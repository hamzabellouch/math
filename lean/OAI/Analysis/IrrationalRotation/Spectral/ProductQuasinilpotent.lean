import OAI.Analysis.IrrationalRotation.Model.Product
import OAI.Analysis.IrrationalRotation.Product.ProductWeightBridge
import OAI.Analysis.IrrationalRotation.Product.ProductLogIntegral
import OAI.Analysis.IrrationalRotation.Rotation.FieldWeightedShiftPowers
import OAI.Analysis.IrrationalRotation.Analysis.GeneratedVonNeumann
import OAI.Analysis.IrrationalRotation.Product.ProductNorm

namespace OAI

noncomputable section
open MeasureTheory Set Function Filter
open scoped ENNReal BigOperators Topology

namespace Invariant233.ProductModel

theorem weight_orbit_product_eq_cocycleVersion
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i)
    (s : Set Base) (hinv : ∀ k : ℤ, ProductCocycle.rotate θ k ⁻¹' s = s)
    (hs : ∀ x ∈ s, ∀ k : ℤ, HasFiniteSupport
      (fun i ↦ ⌊ProductCocycle.representative (x i) + (k : ℝ) * θ i⌋))
    (hlaw : ∀ x ∈ s, ∀ k n : ℤ,
      ProductCocycle.cocycleVersion θ c (k + n) x =
        ProductCocycle.cocycleVersion θ c n (ProductCocycle.rotate θ k x) *
          ProductCocycle.cocycleVersion θ c k x)
    (x : Base) (hx : x ∈ s) (n : ℕ) :
    (∏ j ∈ Finset.range n, weight θ c (rotationIterate θ j x)) =
      ProductCocycle.cocycleVersion θ c n x := by
  have hweight (k : ℤ) : weight θ c (rotationIterate θ k x) =
      ProductCocycle.cocycleVersion θ c 1 (ProductCocycle.rotate θ k x) := by
    apply weight_eq_cocycleVersion_of_finite_support θ c hθ0 hc
    have hxk : ProductCocycle.rotate θ k x ∈ s := by
      change x ∈ ProductCocycle.rotate θ k ⁻¹' s
      rw [hinv k]
      exact hx
    simpa only [ProductCocycle.representative, circleRepresentative,
      Int.cast_one, one_mul, rotationIterate, ProductCocycle.rotate] using hs _ hxk 1
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, hweight]
    simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using (hlaw x hx n 1).symm

theorem ae_weight_orbit_product_le
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i)
    (hθ : Summable θ) (I : Finset ℕ) (n : ℕ) :
    ∀ᵐ x ∂baseMeasure, ∀ k : ℤ,
      (∏ j ∈ Finset.range n, weight θ c (rotationIterate θ (k + j) x)) ≤
        Real.exp ((∑ i ∈ I, c i) - (n : ℝ) * (∑ i ∈ I, c i * θ i)) := by
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
  rw [hprod]
  apply ProductNorm.infinite_weight_upper_bound I c
    (fun i => ProductCocycle.representative (ProductCocycle.rotate θ k x i)) θ n
    hc (fun i => (ProductCocycle.representative_mem_Ico _).1) hθ0
  simpa only [Int.cast_natCast] using
    FiniteSupportCocycle.summable_weighted_int c (hs _ hxk n)

theorem norm_weightedOperator_pow_le
    (θ c : ℕ → ℝ) (n : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hprod : ∀ᵐ x ∂baseMeasure, ∀ k : ℤ,
      (∏ j ∈ Finset.range n, weight θ c (rotationIterate θ (k + j) x)) ≤ B) :
    ‖weightedOperator θ c ^ n‖ ≤ B := by
  unfold weightedOperator multiplier shiftOperator
  apply WeightedShift.norm_fieldOperator_pow_le
    (multiplierField θ (fun x => (weight θ c x : ℂ)) 1 _) 1 _ _ _ n hB
  filter_upwards [hprod] with x hx k
  change ‖∏ j ∈ Finset.range n,
    (weight θ c (rotationIterate θ (k + j) x) : ℂ)‖ ≤ B
  rw [← Complex.ofReal_prod, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.prod_nonneg (fun j _hj => (weight_mem_Icc θ c _).1))]
  exact hx k

theorem norm_weightedOperator_pow_le_finite_cost
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i)
    (hθ : Summable θ) (I : Finset ℕ) (n : ℕ) :
    ‖weightedOperator θ c ^ n‖ ≤
      Real.exp ((∑ i ∈ I, c i) - (n : ℝ) * (∑ i ∈ I, c i * θ i)) :=
  norm_weightedOperator_pow_le θ c n (Real.exp_nonneg _)
    (ae_weight_orbit_product_le θ c hθ0 hc hθ I n)

theorem weightedOperator_normQuasinilpotent
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i)
    (hθ : Summable θ)
    (hdiv : (∑' i, ENNReal.ofReal (c i * θ i)) = ∞) :
    NormQuasinilpotent (weightedOperator θ c) := by
  classical
  have hex : ∀ q : ℕ, ∃ I : Finset ℕ, (q : ℝ) < ∑ i ∈ I, c i * θ i := by
    intro q
    exact ProductNorm.exists_finite_sum_gt_of_tsum_eq_top (fun i => c i * θ i)
      (fun i => mul_nonneg (hc i) (hθ0 i)) hdiv q
  choose I hI using hex
  apply ProductNorm.tendsto_root_zero_of_exponential_bounds
    (fun n => ‖weightedOperator θ c ^ n‖)
    (fun q => ∑ i ∈ I q, c i) (fun q => ∑ i ∈ I q, c i * θ i)
    (fun n => norm_nonneg _)
  · intro q n _hn
    exact norm_weightedOperator_pow_le_finite_cost θ c hθ0 hc hθ (I q) n
  · intro b
    obtain ⟨q, hq⟩ := exists_nat_gt b
    exact ⟨q, hq.trans (hI q)⟩

theorem weightedOperator_normQuasinilpotent_of_logIntegral
    (θ c : ℕ → ℝ) (hθ01 : ∀ i, θ i ∈ Ico (0 : ℝ) 1)
    (hc : ∀ i, 0 ≤ c i) (hθ : Summable θ)
    (hlog : HasNegInfiniteLogIntegral baseMeasure (weight θ c)) :
    NormQuasinilpotent (weightedOperator θ c) :=
  weightedOperator_normQuasinilpotent θ c (fun i => (hθ01 i).1) hc hθ
    ((hasNegInfiniteLogIntegral_iff_tsum θ c hθ01 hc).mp hlog)

theorem weightedOperator_ne_zero
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i)
    (hθ : Summable θ) : weightedOperator θ c ≠ 0 := by
  unfold weightedOperator multiplier shiftOperator
  apply WeightedShift.fieldOperator_ne_zero_of_coordinate
    (multiplierField θ (fun x => (weight θ c x : ℂ)) 1 _) 1 _ _ _ (0 : ℤ)
  filter_upwards [ae_weight_pos θ c hθ0 hc hθ] with x hx
  change (weight θ c (rotationIterate θ 0 x) : ℂ) ≠ 0
  have hrot : rotationIterate θ 0 x = x := ProductCocycle.rotate_zero θ x
  rw [hrot, Complex.ofReal_ne_zero]
  exact ne_of_gt hx

theorem weightedOperator_mem_factor (θ c : ℕ → ℝ) :
    weightedOperator θ c ∈ factor θ := by
  unfold weightedOperator
  apply (factor θ).mul_mem
  · exact subset_vonNeumannGenerated _ (Set.mem_union_left _ (by simp))
  · apply subset_vonNeumannGenerated _
    apply Set.mem_union_right
    exact ⟨_, _, _, _, _, rfl⟩

theorem weightedOperator_spectralRadius_eq_zero
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i)
    (hθ : Summable θ)
    (hdiv : (∑' i, ENNReal.ofReal (c i * θ i)) = ∞) :
    spectralRadius ℂ (weightedOperator θ c) = 0 :=
  spectralRadius_zero_of_norm_root_tendsto_zero _
    (weightedOperator_normQuasinilpotent θ c hθ0 hc hθ hdiv)

theorem weightedOperator_spectrum_eq_singleton_zero
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i)
    (hθ : Summable θ)
    (hdiv : (∑' i, ENNReal.ofReal (c i * θ i)) = ∞) :
    spectrum ℂ (weightedOperator θ c) = {0} := by
  let : Nontrivial (Hilbert →L[ℂ] Hilbert) :=
    ⟨⟨weightedOperator θ c, 0, weightedOperator_ne_zero θ c hθ0 hc hθ⟩⟩
  exact spectrum_eq_zero_of_spectralRadius_zero _
    (weightedOperator_spectralRadius_eq_zero θ c hθ0 hc hθ hdiv)

end Invariant233.ProductModel

end

end OAI
