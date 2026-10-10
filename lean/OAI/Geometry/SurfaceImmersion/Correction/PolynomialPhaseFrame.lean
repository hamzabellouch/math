import OAI.Geometry.SurfaceImmersion.Geometry.LinearFrameJetBound

namespace OAI

/-! Polynomial reconstruction and free-normal bounds for the selected
linear phase charts. The exponent is fixed before the map and its bounds. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open SmallModes PhaseGeometry WeightedEstimates

def phaseFrameInputBudget (m : ℕ) (B : ℝ) : ℝ :=
  1+B*B^(m+2)+4*B^5+16*B^10

lemma phaseFrameInputBudget_polynomial (m : ℕ) :
    HasPolynomialBound (phaseFrameInputBudget m) := by
  unfold phaseFrameInputBudget
  repeat first
    | exact polynomialBound_id
    | apply HasPolynomialBound.add
    | apply HasPolynomialBound.mul
    | apply HasPolynomialBound.pow
    | (apply polynomialBound_const; positivity)

theorem polynomial_phase_frame_bound (m : ℕ) :
    ∃ d : ℕ, ∃ A : ℝ, 1 ≤ A ∧
    ∀ {F : RField 4} {U : Set Base}, ContDiff ℝ ∞ F → IsOpen U →
    ∀ {ξ : Base} (hξ : ξ ≠ 0) {s B : ℝ}, 0 < s → s ≤ 1 → 1 ≤ B →
      ‖ξ‖ ≤ B → ‖(phaseEquiv ξ hξ).symm.toContinuousLinearMap‖ ≤ B →
      (∀ j ≤ m+2, WeightedBound U 1 j (B/s^(j-2)) F) →
      (∀ x ∈ U, Function.Injective (fderiv ℝ F x)) →
      (∀ x ∈ U, Good (realSecondTensor F x) ξ) →
      (∀ x ∈ U, ‖(NormalFrame.gramDet (coordDeriv dx F x) (coordDeriv dy F x))⁻¹‖ ≤ B) →
      (∀ x ∈ U, ‖secondQuadratic (realSecondTensor F x) (-ξ.2,ξ.1)‖⁻¹ ≤ B) →
      ReconstructionCoefficientBound
        (fun x => complexify ((F ∘ (phaseEquiv ξ hξ).symm) x))
        ((phaseEquiv ξ hξ).symm ⁻¹' U) s m (A*B^d) ∧
      WeightedBound ((phaseEquiv ξ hξ).symm ⁻¹' U) s m (A*B^d)
        (freeNormal (F ∘ (phaseEquiv ξ hξ).symm)) := by
  obtain ⟨q,C,hC,hframe⟩ := polynomial_frame_envelope m
  obtain ⟨d,A,hA,hpoly⟩ := (polynomialBound_const (zero_le_one.trans hC)).mul
    ((phaseFrameInputBudget_polynomial m).pow q)
  refine ⟨d,A,hA,?_⟩
  intro F U hF hU ξ hξ s B hs hs1 hB hξB heB hprefix hImm hgood hG hN
  have hB0 := zero_le_one.trans hB
  let S := phaseFrameInputBudget m B
  have hterms : 1 ≤ S ∧ B*B^(m+2) ≤ S ∧ 4*B^5 ≤ S ∧ 16*B^10 ≤ S := by
    have h1 : 0 ≤ B*B^(m+2) := by positivity
    have h2 : 0 ≤ 4*B^5 := by positivity
    have h3 : 0 ≤ 16*B^10 := by positivity
    dsimp [S,phaseFrameInputBudget]
    constructor
    · linarith
    constructor
    · linarith
    constructor <;> linarith
  have hjet := (realTwoJet_linear_prefix_bound hU hF hs hs1 hB0
    (phaseEquiv ξ hξ).symm hB heB hprefix).mono_const hterms.2.1
  have hset : (phaseEquiv ξ hξ) '' U = (phaseEquiv ξ hξ).symm ⁻¹' U := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      simpa only [mem_preimage,ContinuousLinearEquiv.symm_apply_apply] using hy
    · intro hx
      exact ⟨(phaseEquiv ξ hξ).symm x,hx,(phaseEquiv ξ hξ).apply_symm_apply x⟩
  have hdomain := realModeDomain_phase hF hU hξ hImm hgood
  rw [hset] at hdomain
  obtain ⟨hcoeff,hfree⟩ := hframe (hF.comp (phaseEquiv ξ hξ).symm.contDiff)
    hdomain hs hterms.1 hjet
    (fun x hx => (inverse_gram_phase_bound hF hξ hB0 hB0 hξB x (hG _ hx)).trans
      (by convert hterms.2.2.1 using 1; ring))
    (fun x hx => (inverse_normal_phase_bound hF hξ hB0 hB0 hξB x (hImm _ hx)
      (hgood _ hx).2 (hN _ hx)).trans
      (by convert hterms.2.2.2 using 1; ring))
  have hout : C*S^q ≤ A*B^d := (hpoly B hB).2
  exact ⟨hcoeff.mono_const hout,hfree.mono_const hout⟩

end ClosedSurfaceR4.RealModes

end

end OAI
