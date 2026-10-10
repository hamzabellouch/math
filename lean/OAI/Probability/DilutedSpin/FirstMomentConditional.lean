import OAI.Probability.DilutedSpin.FirstMomentFresh
import OAI.Probability.DilutedSpin.UpperConditional

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory KernelTower
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {n p N : ℕ} [NeZero N]

lemma datumRoot_conditional_replacement_firstMoment (M : Model p) (hM : Admissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ d,0 ≤ m d)
    (hstrict : ∀ d : Fin n,0 < m d.succ) (hroot : m 0=0) (hend : m (Fin.last n)=1)
    (j : Fin p) (f : FinitePath Ω n → ℝ) (k l : ℕ)
    (z : RootPath (UpperDatum p N R) k) (w : RootPath (UpperDatum p N R) l)
    :
    (∫ a,datumRoot T U V x (fun d => m d.succ) j f (k+1) l (a,z) w ∂upperDatumLaw M Q)+
      ((p-1:ℕ):ℝ)*datumRoot T U V x (fun d => m d.succ) j f k l z w ≤
      (p:ℝ)*(∫ a,datumRoot T U V x (fun d => m d.succ) j f k (l+1) z (a,w) ∂upperDatumLaw M Q)-
      ((p-1:ℕ):ℝ)*(∫ a,edgeRoot Q U x (fun d => m d.succ) a ∂M.disorder.toMeasure) := by
  let F := cavityEnergy V x j l (rootMap (fun a => a.2.2) l w)
        (rootMap (fun a => a.2.1) l w) (rootMap Prod.fst l w)
        (realCountEnergy V k (rootMap (fun a => a.2.1) k z) (rootMap Prod.fst k z) f)
  have h := freshRoot_replacement_firstMoment M hM
    (cavityTower T U l (rootMap (fun a => a.2.2) l w)) Q U
    (fun y => V (pathMap (cavityProject l) n y)) x m hm hpos hstrict hroot hend F j
    (fun y => norm_le_pi_norm F y)
  dsimp only [F] at h
  simp only [datumRoot_fresh_true,datumRoot_fresh_selected] at h
  exact h

end DilutedSpinGlass.PrescribedTree

end

end OAI
