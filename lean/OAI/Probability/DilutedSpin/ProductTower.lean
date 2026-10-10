import OAI.Probability.DilutedSpin.QSubtreePotential
import OAI.Probability.DilutedSpin.TopologyDecay

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory Set
open scoped BigOperators
local instance productTowerMeasurableSpace (space : TopCat) :
    MeasurableSpace space := borel space
local instance productTowerBorelSpace (space : TopCat) : BorelSpace space := ⟨rfl⟩
namespace FinitePath
variable {ι : Type} {α : ι → Type}
def proj : (n : ℕ) → FinitePath ((i : ι) → α i) n → (i : ι) → FinitePath (α i) n
  | 0,_,_ => ()
  | n+1,y,i => (y.1 i,proj n y.2 i)
end FinitePath
namespace KernelTower
variable {ι : Type} [Fintype ι] [DecidableEq ι] {α : ι → Type} [∀ i, Fintype (α i)]
noncomputable def pi : (n : ℕ) → ((i : ι) → KernelTower (α i) n) →
    KernelTower ((i : ι) → α i) n
  | 0,_ => ()
  | n+1,T => (FiniteLaw.pi (fun i => (T i).1), fun x => pi n (fun i => (T i).2 (x i)))

 
lemma backwardLog_encode (r : ℕ) (T : (i : ι) → KernelTower (α i) (r+1))
    (V : (i : ι) → FinitePath (α i) (r+1) → Spin) (F : (ι → Spin) → ℝ)
    (m : Fin (r+1) → ℝ) (hm : m (Fin.last r)=1)
    (hV : ∀ i, TerminalInterior r (T i) (fun y => spin (V i y))) :
    backwardLog (r+1) (pi (r+1) T) m
      (fun y => F (fun i => V i (FinitePath.proj (r+1) y i))) =
    DilutedSpinGlass.logMean r (FiniteLaw.spinLog F) (fun i => m i.castSucc)
      (fun i => encode r (T i) (fun y => spin (V i y))) := by
  induction r with
  | zero =>
    change (FiniteLaw.pi (fun i => (T i).1)).logMean (m 0)
      (fun a => F (fun i => V i (a i,()))) =
      FiniteLaw.spinLog F (fun i => Real.artanh ((T i).1.expect (fun a => spin (V i (a,())))))
    rw [show m 0=1 from hm]
    exact FiniteLaw.logMean_pi_spin _ _ F hV
  | succ r ih =>
    change (FiniteLaw.pi (fun i => (T i).1)).logMean (m 0)
      (fun a => backwardLog (r+1) (pi (r+1) (fun i => (T i).2 (a i)))
        (fun j => m j.succ)
        (fun y => F (fun i => V i (a i,FinitePath.proj (r+1) y i)))) = _
    have hc (a : (i : ι) → α i) := ih (fun i => (T i).2 (a i))
      (fun i y => V i (a i,y)) (fun j => m j.succ)
      (by simpa only [Fin.succ_last] using hm) (fun i => hV i (a i))
    simp_rw [hc]
    change Real.log ((FiniteLaw.pi (fun i => (T i).1)).expect
      (fun a => Real.exp (m 0 * DilutedSpinGlass.logMean r (FiniteLaw.spinLog F)
        (fun j => m j.castSucc.succ) (fun i => encode r ((T i).2 (a i))
          (fun y => spin (V i (a i,y))))))) / m 0 =
      Real.log (∫ x, Real.exp (m 0 * DilutedSpinGlass.logMean r (FiniteLaw.spinLog F)
        (fun j => m j.succ.castSucc) x)
        ∂Measure.pi (fun i => ((T i).1.asProbability
          (fun a => encode r ((T i).2 a) (fun y => spin (V i (a,y))))).toMeasure)) / m 0
    rw [FiniteLaw.integral_pi_asProbability]
    rfl

end KernelTower
end DilutedSpinGlass

end

end OAI
