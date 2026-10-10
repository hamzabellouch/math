import OAI.Geometry.SurfaceImmersion.Atlas.LinearPhaseTwoJetBounds
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialPhaseChartInverse

namespace OAI

/-! Explicit jet transfer through nonlinear phase coordinates. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates PhaseGeometry

theorem realTwoJet_coordinate_prefix_bound
    {T : Base → Base} (hT : ContDiff ℝ ∞ T)
    {U V : Set Base} (hU : IsOpen U) (hV : IsOpen V) (hTU : MapsTo T V U)
    {m : ℕ} {s C D : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 ≤ C) (hD : 1 ≤ D)
    (hTd : ∀ j, 1 ≤ j → j ≤ m+2 → ∀ x ∈ V,
      ‖iteratedFDerivWithin ℝ j T V x‖ ≤ D)
    {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (hb : ∀ j ≤ m+2, WeightedBound U 1 j (C/s^(j-2)) F) :
    WeightedBound V s m (((m+2).factorial : ℝ)*D^(m+2)*C) (realTwoJet (F ∘ T)) := by
  apply realTwoJet_prefix_bound_on hV (hF.comp hT) hs hs1 (by positivity)
  intro j hj
  have hc (k : ℕ) (hk : 1 ≤ k) (hkj : k ≤ j) (x : Base) (hx : x ∈ V) :
      ‖iteratedFDerivWithin ℝ k T V x‖ ≤ D := hTd k hk (hkj.trans hj) x hx
  have hh := (hb j hj).comp_coordinates hV.uniqueDiffOn hU.uniqueDiffOn zero_lt_one le_rfl
    hD (div_nonneg hC (pow_nonneg hs.le _)) hT.contDiffOn hF.contDiffOn hTU hc
  apply hh.mono_const
  calc
    (j.factorial : ℝ)*(C/s^(j-2))*D^j = ((j.factorial : ℝ)*D^j)*C/s^(j-2) := by ring
    _ ≤ (((m+2).factorial : ℝ)*D^(m+2)*C)/s^(j-2) := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg hs.le _)
      apply mul_le_mul_of_nonneg_right _ hC
      gcongr

theorem polynomial_inverse_chart_twoJet_bound (m : ℕ) :
    ∃ d : ℕ, ∃ C : ℝ, 1 ≤ C ∧
    ∀ (F : RField 4) (e : OpenPartialHomeomorph Base Base),
      ContDiff ℝ ∞ F → ContDiff ℝ ∞ e → ContDiff ℝ ∞ e.symm →
    ∀ s B : ℝ, 0 < s → s ≤ 1 → 1 ≤ B →
      (∀ j ≤ m+2, WeightedBound e.source 1 j (B/s^(j-2)) F) →
      (∀ j, 1 ≤ j → j ≤ m+2 → ∀ x ∈ e.source,
        ‖iteratedFDerivWithin ℝ j e e.source x‖ ≤ B) →
      (∀ x ∈ e.source, ‖(coordDet (fderiv ℝ e x))⁻¹‖ ≤ B) →
      WeightedBound e.target s m (C*B^d) (realTwoJet (F ∘ e.symm)) := by
  obtain ⟨d₀,C₀,hC₀,hInv⟩ := polynomial_inverse_chart_bound (m+1)
  have hp := ((polynomialBound_const (Nat.cast_nonneg (m+2).factorial)).mul
    (((polynomialBound_const (zero_le_one.trans hC₀)).mul (polynomialBound_id.pow d₀)).pow
      (m+2))).mul polynomialBound_id
  obtain ⟨d,C,hC,hpoly⟩ := hp
  refine ⟨d,C,hC,?_⟩
  intro F e hF he hi s B hs hs1 hB hFjet hejet hdet
  have hD : 1 ≤ C₀*B^d₀ := one_le_mul_of_one_le_of_one_le hC₀ (one_le_pow₀ hB)
  have hb := realTwoJet_coordinate_prefix_bound hi e.open_source e.open_target
    (fun x hx => e.map_target hx) hs hs1 (zero_le_one.trans hB) hD
    (fun j hj hjm x hx => hInv e he hi B hB hejet hdet j hj (by omega) x hx) hF hFjet
  exact hb.mono_const (hpoly B hB).2

end ClosedSurfaceR4.RealModes

end

end OAI
