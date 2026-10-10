import OAI.Analysis.LipschitzHilbert.Fourier.PVCommutatorSymbolLinearity
import OAI.Analysis.LipschitzHilbert.Estimates.FiniteSignedFunctions
import OAI.Analysis.LipschitzHilbert.Estimates.SignedPVCommutator

namespace OAI

/-! The signed commutator estimate controls the square sum of individual
actual annular PV commutators without assuming a full PV L2 operator. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation

def annularProfile (N : ℕ) (i : Fin (2*N+1)) : SchwartzMap ℝ ℂ :=
  dilatedSlopeWindow reassemblyDifferenceSchwartz (reassemblyScale N i)
    (reassemblyScale_pos N i).ne'

def annularPVComm (N : ℕ) (u : (ℝ×ℝ) → ℝ) (R : ℝ)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (i : Fin (2*N+1)) : (ℝ×ℝ) → ℂ :=
  principalValueProfileCommutator (annularProfile N i) 1 0 R u f

theorem signedAnnularSymbol_fin (N : ℕ) (s : ℕ → Bool) :
    signedAnnularSymbol N s=∑ i : Fin (2*N+1), if s i then annularProfile N i else -annularProfile N i := by
  symm
  unfold annularProfile
  exact Fin.sum_univ_eq_sum_range (fun n => if s n then
    dilatedSlopeWindow reassemblyDifferenceSchwartz (reassemblyScale N n)
      (reassemblyScale_pos N n).ne' else
    -dilatedSlopeWindow reassemblyDifferenceSchwartz (reassemblyScale N n)
      (reassemblyScale_pos N n).ne') (2*N+1)

theorem annularPVComm_signed (N : ℕ) (s : ℕ → Bool) (u : (ℝ×ℝ) → ℝ)
    (hum : Measurable u) (hub : ∀ z, |u z|≤1) (R : ℝ) (hR : 0<R) (hRs : R≤1/4)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    signedFunction (annularPVComm N u R f) (fun i => s i)=
      principalValueProfileCommutator (signedAnnularSymbol N s) 1 0 R u f := by
  rw [←pvCommutatorSymbolLM_apply 1 (by norm_num) u hum hub R hR hRs f,
    signedAnnularSymbol_fin,map_sum]
  funext z
  simp only [signedFunction,finiteSignedSum,Finset.sum_apply,annularPVComm]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp only [map_neg,Pi.neg_apply,pvCommutatorSymbolLM_apply]

theorem annularPVComm_square (N : ℕ) (field : Plane → ℝ) (hf : LipschitzWith 1 field)
    (hfb : ∀ z, |field z|≤1/4) (R : ℝ) (hR : 0<R) (hRs : R≤1/4)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    ∃ hcomm : ∀ i, MemLp (annularPVComm N (fun z => field (planeCoordinates z)) R f i) 2 planeMeasure,
      (∑ i, ‖(hcomm i).toLp (annularPVComm N (fun z => field (planeCoordinates z)) R f i)‖^2)≤
        (signedPVCommutatorConstant*R)^2*‖f.toLp 2 planeMeasure‖^2 := by
  let u := fun z => field (planeCoordinates z)
  have hum : Measurable u := hf.continuous.measurable.comp planeCoordinates.measurable
  have hub (z) : |u z|≤1 := (hfb _).trans (by norm_num)
  have hh := signedFunction_square_bound planeMeasure (annularPVComm N u R f)
    ((signedPVCommutatorConstant*R)*‖f.toLp 2 planeMeasure‖)
    (mul_nonneg (mul_nonneg signedPVCommutatorConstant_nonneg hR.le) (norm_nonneg _)) (fun s => by
      let ss : ℕ → Bool := fun n => if hn : n<2*N+1 then s ⟨n,hn⟩ else false
      have he : (fun i : Fin (2*N+1) => ss i)=s := by
        funext i
        dsimp only [ss]
        rw [dite_eq_left i.isLt]
      rw [←he,annularPVComm_signed N ss u hum hub R hR hRs f]
      exact signedPVCommutator_bound N ss field hf hfb R hR hRs f)
  obtain ⟨hc,hcBound⟩ := hh
  exact ⟨hc,by simpa only [mul_pow] using hcBound⟩

end LipschitzHilbert.PacketRepresentation

end

end OAI
