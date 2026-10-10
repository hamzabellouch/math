import OAI.Analysis.CircleDomains.Sobolev.ComplexCoareaJacobian
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

namespace OAI

/-! Change of variables from real product parameters to the physical complex
plane, with the actual two-column Jacobian. -/
open Set Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

def planarMapJacobian (A : (ℝ × ℝ) →L[ℝ] ℂ) : ℝ :=
  (A (1,0)).re * (A (0,1)).im - (A (1,0)).im * (A (0,1)).re

lemma planarMapJacobian_det (A : (ℝ × ℝ) →L[ℝ] ℂ) :
    (A.comp (Complex.equivRealProdCLM : ℂ →L[ℝ] (ℝ × ℝ))).det =
      planarMapJacobian A := by
  rw [complex_real_det_columns]
  change (A (1,0)).re * (A (0,1)).im - (A (0,1)).re * (A (1,0)).im = _
  unfold planarMapJacobian
  ring

lemma integral_image_planarMap {S : Set (ℝ × ℝ)} (hS : MeasurableSet S)
    {F : (ℝ × ℝ) → ℂ} {A : (ℝ × ℝ) → ((ℝ × ℝ) →L[ℝ] ℂ)}
    (hF : ∀ p ∈ S, HasFDerivAt F (A p) p) (hi : InjOn F S) (q : ℂ → ℝ) :
    (∫ z in F '' S, q z) =
      ∫ p in S, |planarMapJacobian (A p)| * q (F p) := by
  let e := Complex.equivRealProdCLM
  let T : Set ℂ := e ⁻¹' S
  let G : ℂ → ℂ := F ∘ e
  have hT : MeasurableSet T := hS.preimage e.continuous.measurable
  have hG : ∀ z ∈ T, HasFDerivWithinAt G ((A (e z)).comp (e : ℂ →L[ℝ] (ℝ × ℝ))) T z := by
    intro z hz
    exact ((hF (e z) hz).comp z e.hasFDerivAt).hasFDerivWithinAt
  have hiG : InjOn G T := by
    intro x hx y hy h
    exact e.injective (hi hx hy h)
  have himage : G '' T = F '' S := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨e x,hx,rfl⟩
    · rintro ⟨p,hp,rfl⟩
      exact ⟨e.symm p,by simpa [T] using hp,by simp [G]⟩
  have hc := integral_image_eq_integral_abs_det_fderiv_smul volume hT hG hiG q
  rw [himage] at hc
  dsimp only [e] at hc
  simp only [planarMapJacobian_det,smul_eq_mul] at hc
  have he := Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding
    (fun p => |planarMapJacobian (A p)| * q (F p)) S
  exact hc.trans he

end CircleDomainRigidity

end

end OAI
