import OAI.Analysis.KadisonKastler.VonNeumannSpectralCut
import OAI.Analysis.KadisonKastler.TypeIIIProjectionComparison

namespace OAI

/-! # Making a nonzero type III corner strictly positive

Spectral compression of a nonzero element produces a positive invertible
left-right product. Scaling both factors to norm at most one half makes
this operation available inside a convex unitary-orbit family.
-/

namespace KadisonKastler

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {N : VonNeumannAlgebra H}

local instance typeIIIPositiveCornerLE : LE (Algebra N) :=
  (CStarAlgebra.spectralOrder (Algebra N)).toLE
local instance typeIIIPositiveCornerOrder : PartialOrder (Algebra N) :=
  CStarAlgebra.spectralOrder _
local instance typeIIIPositiveCornerPreorder : Preorder (Algebra N) :=
  (CStarAlgebra.spectralOrder (Algebra N)).toPreorder
local instance typeIIIPositiveCornerStarOrder : StarOrderedRing (Algebra N) :=
  CStarAlgebra.spectralOrderedRing _

theorem TypeIIIFactor.positive_compression_of_projection_countability
    (hN : TypeIIIFactor N) (hFamilies : HasCountableProjectionFamilies N)
    (x : Algebra N) (ε : ℝ) (hε : 0 < ε) (hx : ε ≤ ‖x‖) :
    ∃ v : Algebra N, star v * v = 1 ∧
      algebraMap ℝ (Algebra N) (ε ^ 2 / 2) ≤ star v * (star x * x) * v := by
  have ht : 0 < ε ^ 2 / 2 := by positivity
  have hlt : ε ^ 2 / 2 < ‖star x * x‖ := by
    rw [CStarRing.norm_star_mul_self]
    nlinarith [norm_nonneg x]
  obtain ⟨p, hp, hpne, hpx⟩ := publishedVonNeumannSpectralCut H N x (ε ^ 2 / 2) ht hlt
  obtain ⟨v, hv, hvp⟩ :=
    hN.exists_isometry_onto_projection_of_projection_countability hFamilies p hp hpne
  refine ⟨v, hv, ?_⟩
  have h := star_left_conjugate_le_conjugate hpx v
  have hvpv : star v * p * v = 1 := by
    rw [← hvp]
    calc
      star v * (v * star v) * v = (star v * v) * (star v * v) := by simp only [mul_assoc]
      _ = 1 := by rw [hv, one_mul]
  simpa only [mul_smul_comm, smul_mul_assoc, hvpv, Algebra.algebraMap_eq_smul_one] using h

theorem TypeIIIFactor.exists_small_positive_product_of_projection_countability
    (hN : TypeIIIFactor N) (hFamilies : HasCountableProjectionFamilies N)
    (c : Algebra N) (hc : c ≠ 0) :
    ∃ a b : Algebra N, ‖a‖ ≤ 1 / 2 ∧ ‖b‖ ≤ 1 / 2 ∧
      ∃ δ : ℝ, 0 < δ ∧ δ • (1 : Algebra N) ≤ a * c * b := by
  let : Nontrivial (Algebra N) :=
    ⟨⟨1, 0, fun h => hN.nonzero (congrArg Subtype.val h)⟩⟩
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  obtain ⟨v, hv, hvbound⟩ := hN.positive_compression_of_projection_countability
    hFamilies (star c) ‖c‖ hcpos (by rw [norm_star])
  have hvnorm : ‖v‖ = 1 := by
    have hh := congrArg norm hv
    rw [CStarRing.norm_star_mul_self, norm_one] at hh
    nlinarith [norm_nonneg v]
  let s : ℝ := (2 * (‖c‖ + 1))⁻¹
  have hs : 0 < s := by dsimp [s]; positivity
  let a : Algebra N := (1 / 2 : ℝ) • star v
  let b : Algebra N := s • (star c * v)
  have ha : ‖a‖ ≤ 1 / 2 := by
    change ‖(1 / 2 : ℝ) • star v‖ ≤ 1 / 2
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
      norm_star, hvnorm, mul_one]
  have hb : ‖b‖ ≤ 1 / 2 := by
    change ‖s • (star c * v)‖ ≤ 1 / 2
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs]
    calc
      s * ‖star c * v‖ ≤ s * (‖star c‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left (norm_mul_le _ _) hs.le
      _ = s * ‖c‖ := by rw [norm_star, hvnorm, mul_one]
      _ ≤ 1 / 2 := by
        dsimp [s]
        rw [inv_mul_eq_div, div_le_iff₀ (by positivity)]
        linarith
  let δ : ℝ := ((1 / 2) * s) * (‖c‖ ^ 2 / 2)
  refine ⟨a, b, ha, hb, δ, by dsimp [δ]; positivity, ?_⟩
  have hh := smul_le_smul_of_nonneg_left (α := ℝ) (β := Algebra N) hvbound
    (show 0 ≤ (1 / 2 : ℝ) * s by positivity)
  simpa only [a, b, δ, star_star, Algebra.algebraMap_eq_smul_one,
    smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc,
    mul_comm s (1 / 2 : ℝ)] using hh

theorem TypeIIIFactor.exists_small_positive_product [TopologicalSpace.SeparableSpace H]
    (hN : TypeIIIFactor N) (c : Algebra N) (hc : c ≠ 0) :
    ∃ a b : Algebra N, ‖a‖ ≤ 1 / 2 ∧ ‖b‖ ≤ 1 / 2 ∧
      ∃ δ : ℝ, 0 < δ ∧ δ • (1 : Algebra N) ≤ a * c * b :=
  hN.exists_small_positive_product_of_projection_countability
    (fun _ p hp ho => countable_of_orthogonal_nonzero_projections p hp ho) c hc

end

end KadisonKastler

end OAI
