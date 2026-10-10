import OAI.Geometry.SurfaceImmersion.Correction.PolynomialUnitPerpBounds

namespace OAI

/-! Apply the rational and square-root estimates to the actual free normal
of an immersed surface, with explicit inverse geometric margins. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates

def freeNormalInputBudget (m : ℕ) (C K : ℝ) : ℝ := 1+C+normalBudget m C K

def freeNormalBudget (m : ℕ) (D C K : ℝ) : ℝ :=
  let A := freeNormalInputBudget m C K
  2^m*((m.factorial : ℝ)*D*(K^2)^(m+1)*(1+dotBudget m (perpBudget m A))^m)*perpBudget m A

lemma normalBudget_nonneg (m : ℕ) {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K) :
    0 ≤ normalBudget m C K := by
  have hh := liftBudget_nonneg m hC hK
  unfold normalBudget
  positivity

/-- The coefficient depends polynomially on the two-jet bound and the
inverse Gram and normal-length bounds. -/
theorem polynomial_freeNormal_bound (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ {U : Set Base} {F : RField 4}, ContDiff ℝ ∞ F →
      RealModeDomain F U → ∀ {s C K : ℝ}, 0 < s → 1 ≤ C → 1 ≤ K →
      WeightedBound U s m C (realTwoJet F) →
      (∀ x ∈ U, ‖(NormalFrame.gramDet (coordDeriv dx F x) (coordDeriv dy F x))⁻¹‖ ≤ K) →
      (∀ x ∈ U, (realSecond F x ⬝ᵥ realSecond F x)⁻¹ ≤ K) →
      WeightedBound U s m (freeNormalBudget m D C K) (freeNormal F) := by
  obtain ⟨D,hD,hunit⟩ := weighted_unitPerp (E := Base) m
  refine ⟨D,hD,?_⟩
  intro U F hF hU s C K hs hC hK hb hG hN
  have hC0 := zero_le_one.trans hC
  have hK0 := zero_le_one.trans hK
  have hj : ContDiffOn ℝ ∞ (realTwoJet F) U := (contDiff_realTwoJet hF).contDiffOn
  have hX : ContDiffOn ℝ ∞ (coordDeriv dx F) U := (contDiff_real_coordDeriv hF dx).contDiffOn
  have hY : ContDiffOn ℝ ∞ (coordDeriv dy F) U := (contDiff_real_coordDeriv hF dy).contDiffOn
  have hW : ContDiffOn ℝ ∞ (coordDeriv dy (coordDeriv dy F)) U :=
    (contDiff_real_coordDeriv (contDiff_real_coordDeriv hF dy) dy).contDiffOn
  have bX : WeightedBound U s m C (coordDeriv dx F) := hb.component hU.isOpen.uniqueDiffOn hs.le hC0 hj 0
  have bY : WeightedBound U s m C (coordDeriv dy F) := hb.component hU.isOpen.uniqueDiffOn hs.le hC0 hj 1
  have bW : WeightedBound U s m C (coordDeriv dy (coordDeriv dy F)) :=
    hb.component hU.isOpen.uniqueDiffOn hs.le hC0 hj 4
  have bN : WeightedBound U s m (normalBudget m C K) (realSecond F) :=
    weighted_realNormalPart hU.isOpen.uniqueDiffOn hs hC hK hX hY hW bX bY bW hU.determinant hG
  have hNs := contDiffOn_realSecond hF hU
  let A := freeNormalInputBudget m C K
  have hnn := normalBudget_nonneg m hC0 hK0
  have hA : 0 ≤ A := by dsimp [A,freeNormalInputBudget]; linarith
  have hCA : C ≤ A := by dsimp [A,freeNormalInputBudget]; linarith
  have hNA : normalBudget m C K ≤ A := by dsimp [A,freeNormalInputBudget]; linarith
  have hK2 : 1 ≤ K^2 := by nlinarith
  apply hunit hU.isOpen.uniqueDiffOn hs hA hK2 hX hY hNs
    (bX.mono_const hCA) (bY.mono_const hCA) (bN.mono_const hNA)
  · intro x hx
    exact NormalFrame.perp_sq_pos (hU.determinant x hx) (hU.good x hx)
      (realNormalPart_perp _ _ _ (hU.determinant x hx)).1
      (realNormalPart_perp _ _ _ (hU.determinant x hx)).2
  · intro x hx
    have hn := realNormalPart_perp (coordDeriv dx F x) (coordDeriv dy F x)
      (coordDeriv dy (coordDeriv dy F) x) (hU.determinant x hx)
    change coordDeriv dx F x ⬝ᵥ realSecond F x = 0 ∧
      coordDeriv dy F x ⬝ᵥ realSecond F x = 0 at hn
    have hgpos := NormalFrame.gramDet_pos (hU.determinant x hx)
    have he : NormalFrame.perpProduct (coordDeriv dx F x) (coordDeriv dy F x) (realSecond F x) ⬝ᵥ
        NormalFrame.perpProduct (coordDeriv dx F x) (coordDeriv dy F x) (realSecond F x) =
        NormalFrame.gramDet (coordDeriv dx F x) (coordDeriv dy F x)*
          (realSecond F x ⬝ᵥ realSecond F x) := by
      rw [NormalFrame.perp_sq,hn.1,hn.2]
      ring
    rw [he,mul_inv_rev]
    have hgb : (NormalFrame.gramDet (coordDeriv dx F x) (coordDeriv dy F x))⁻¹ ≤ K :=
      (le_abs_self _).trans (hG x hx)
    simpa only [pow_two] using mul_le_mul (hN x hx) hgb
      (inv_nonneg.mpr hgpos.le) hK0

end ClosedSurfaceR4.RealModes

end

end OAI
