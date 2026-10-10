import OAI.Analysis.IrrationalRotation.Model.ProductPowers
import OAI.Analysis.IrrationalRotation.Spectral.ProductQuasinilpotent

namespace OAI

noncomputable section
open MeasureTheory Set Function Filter
open scoped ENNReal BigOperators Topology

namespace Invariant233.WeightedShift
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem fieldShift_one_pow (n : ℕ) :
    ((shift 1).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ) ^ n =
      (shift (n : ℤ)).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ := by
  induction n with
  | zero => simpa using (fieldShift_zero (μ := μ)).symm
  | succ n ih =>
    rw [pow_succ, ih, ← fieldShift_add]
    norm_cast

theorem fieldOperator_pow_eq_shift_mul_of_coeff
    (a : X → Weight) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ x, ‖a x‖ ≤ C)
    (hm : ∀ k, AEStronglyMeasurable (fun x => a x k) μ)
    (b : X → Weight) (D : ℝ) (hD : 0 ≤ D)
    (hb : ∀ x, ‖b x‖ ≤ D)
    (hn : ∀ k, AEStronglyMeasurable (fun x => b x k) μ)
    (n : ℕ) (heq : ∀ᵐ x ∂μ, ∀ k : ℤ,
      b x k = ∏ j ∈ Finset.range n, a x (k + j)) :
    fieldOperator a C hC ha hm ^ n =
      ((shift 1).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ) ^ n *
        fieldDiagonal b D hD hb hn := by
  rw [fieldShift_one_pow]
  ext f
  filter_upwards [fieldOperator_pow_ae a C hC ha hm n f,
    fieldShift_ae (n : ℤ) (fieldDiagonal b D hD hb hn f),
    fieldDiagonal_coordinate_ae b D hD hb hn f, heq] with x hx hs hd he
  apply lp.ext
  funext k
  change ((fieldOperator a C hC ha hm ^ n) f) x k =
    ((shift (n : ℤ)).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ
      (fieldDiagonal b D hD hb hn f)) x k
  rw [hx, hs, shift_apply, hd, he]
  exact operator_pow_apply (a x) n (f x) k

end Invariant233.WeightedShift

namespace Invariant233.ProductModel

theorem ae_weight_orbit_product_eq_cocycleVersion
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i)
    (hθ : Summable θ) (n : ℕ) :
    ∀ᵐ x ∂baseMeasure, ∀ k : ℤ,
      (∏ j ∈ Finset.range n, weight θ c (rotationIterate θ (k + j) x)) =
        ProductCocycle.cocycleVersion θ c n (rotationIterate θ k x) := by
  obtain ⟨s, _hsm, hfull, hinv, hs, hlaw⟩ :=
    ProductCocycle.exists_invariant_cocycle_core θ hθ0 hθ
  filter_upwards [hfull] with x hx k
  have hxk : ProductCocycle.rotate θ k x ∈ s := by
    change x ∈ ProductCocycle.rotate θ k ⁻¹' s
    rw [hinv k]
    exact hx
  have hprod := weight_orbit_product_eq_cocycleVersion θ c hθ0 hc s hinv hs
    (fun y hy => hlaw y hy c) (ProductCocycle.rotate θ k x) hxk n
  have hrot (j : ℕ) : rotationIterate θ (k + j) x =
      rotationIterate θ j (ProductCocycle.rotate θ k x) :=
    ProductCocycle.rotate_add θ k j x
  simp_rw [hrot]
  exact hprod

theorem weightedOperator_pow_coordinate_ae
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i)
    (hθ : Summable θ) (n : ℕ) (f : Hilbert) :
    ∀ᵐ x ∂baseMeasure, ∀ k : ℤ,
      (weightedOperator θ c ^ n) f x k =
        (ProductCocycle.cocycleVersion θ c n (rotationIterate θ (k - n) x) : ℂ) *
          f x (k - n) := by
  have hb (x : Base) : ‖(weight θ c x : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (weight_mem_Icc θ c x).1] using (weight_mem_Icc θ c x).2
  have ha (x : Base) : ‖multiplierField θ (fun x => (weight θ c x : ℂ)) 1 hb x‖ ≤ 1 :=
    lp.norm_le_of_forall_le (by norm_num) (fun k => hb _)
  have hm (k : ℤ) : AEStronglyMeasurable
      (fun x => (multiplierField θ (fun x => (weight θ c x : ℂ)) 1 hb x) k)
      baseMeasure := by
    exact ((measurable_weight θ c).complex_ofReal.comp
      (ProductCocycle.measurePreserving_rotate θ k).measurable).aestronglyMeasurable
  have hp := WeightedShift.fieldOperator_pow_ae
    (multiplierField θ (fun x => (weight θ c x : ℂ)) 1 hb) 1
    (by norm_num) ha hm n f
  change (weightedOperator θ c ^ n) f =ᵐ[baseMeasure] _ at hp
  filter_upwards [hp, ae_weight_orbit_product_eq_cocycleVersion θ c hθ0 hc hθ n]
    with x hx he k
  rw [hx, WeightedShift.operator_pow_apply]
  change (∏ j ∈ Finset.range n,
    (weight θ c (rotationIterate θ (k - n + j) x) : ℂ)) * f x (k - n) = _
  rw [← Complex.ofReal_prod, he]

theorem weightedOperator_pow_eq_shift_mul_positiveCocycleMultiplier
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i)
    (hθ : Summable θ) (n : ℕ) :
    weightedOperator θ c ^ n =
      shiftOperator ^ n * positiveCocycleMultiplier θ c hθ0 hc n := by
  unfold weightedOperator positiveCocycleMultiplier multiplier shiftOperator
  apply WeightedShift.fieldOperator_pow_eq_shift_mul_of_coeff
    (multiplierField θ (fun x => (weight θ c x : ℂ)) 1 _) 1 _ _ _
    (multiplierField θ (fun x => (ProductCocycle.cocycleVersion θ c n x : ℂ)) 1 _)
    1 _ _ _ n
  filter_upwards [ae_weight_orbit_product_eq_cocycleVersion θ c hθ0 hc hθ n]
    with x hx k
  change (ProductCocycle.cocycleVersion θ c n (rotationIterate θ k x) : ℂ) =
    ∏ j ∈ Finset.range n, (weight θ c (rotationIterate θ (k + j) x) : ℂ)
  rw [← Complex.ofReal_prod, hx]

theorem positiveCocycleMultiplier_mem_factor
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (n : ℕ) :
    positiveCocycleMultiplier θ c hθ0 hc n ∈ factor θ := by
  apply subset_vonNeumannGenerated _
  apply Set.mem_union_right
  exact ⟨_, _, _, _, _, rfl⟩

end Invariant233.ProductModel

end

end OAI
