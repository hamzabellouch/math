import OAI.MeasureTheory.Falconer.Estimates.MixedMaskBounds

namespace OAI

/-! # Global ambient bounds for the actual normalized cap cutoffs

The packing argument works around every ambient point.  The fixed smooth
reciprocal also keeps the sum of all normalized caps between zero and one
off the sphere.  These are the bounds needed by the separated jet operators.
-/

namespace Falconer
open Set
open scoped ContDiff

theorem separated_ambient_overlap {d : ℕ} (S : Finset (Sphere d))
    {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ/2 ≤ dist x y) (w : Space d) :
    ((S.filter (fun c : Sphere d => dist w (c : Space d) ≤ δ)).card : ℝ) ≤ (5 : ℝ)^d := by
  classical
  let T := S.filter (fun c : Sphere d => dist w (c : Space d) ≤ δ)
  have hinj : Function.Injective (fun c : Sphere d => (c : Space d)) := Subtype.val_injective
  have he := separated_ball_card (T.image (fun c : Sphere d => (c : Space d))) w
    (half_pos hδ) hδ.le (by
      intro x hx y hy hxy
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hy
      exact hsep a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1
        (fun hab => hxy (congrArg Subtype.val hab))) (by
      intro x hx
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
      simpa only [dist_comm] using (Finset.mem_filter.mp ha).2)
  rw [Finset.card_image_of_injective T hinj] at he
  have hratio : 2*δ/(δ/2)+1 = (5 : ℝ) := by
    field_simp
    norm_num
  simpa only [hratio] using he


theorem capDenominator_global_derivatives (d k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (δ : ℝ) (hδ : 0 < δ)
      (S : Finset (Sphere d)),
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ/2 ≤ dist x y) →
      ∀ w : Space d,
      ‖iteratedFDeriv ℝ k (capDenominator δ hδ S) w‖ ≤ B*(δ⁻¹)^k := by
  classical
  obtain ⟨C,hC,hCb⟩ := capBump_ambient_derivatives d k
  refine ⟨5^d*C, by positivity, ?_⟩
  intro δ hδ S hsep w
  let T := S.filter (fun c : Sphere d => dist w (c : Space d) ≤ δ)
  let f := fun c : Sphere d => iteratedFDeriv ℝ k (capBump δ hδ c) w
  have hzero (c : Sphere d) (hc : c ∈ S) (hct : c ∉ T) : f c = 0 := by
    have hd : δ < dist w (c : Space d) :=
      lt_of_not_ge (fun h => hct (Finset.mem_filter.mpr ⟨hc,h⟩))
    exact capBump_ambient_derivative_zero hδ c w (by
      simpa only [dist_eq_norm] using hd) k
  have hsum : (∑ c ∈ S, f c) = ∑ c ∈ T, f c := by
    symm
    exact Finset.sum_subset (Finset.filter_subset _ _) hzero
  change ‖iteratedFDeriv ℝ k (fun x => ∑ c ∈ S, capBump δ hδ c x) w‖ ≤ _
  rw [iteratedFDeriv_fun_sum_apply (n := k)
    (fun c _ => ((capBump δ hδ c).contDiff (n := (k : ℕ∞))).contDiffAt)]
  change ‖∑ c ∈ S, f c‖ ≤ _
  rw [hsum]
  calc
    _ ≤ ∑ c ∈ T, ‖f c‖ := norm_sum_le _ _
    _ ≤ ∑ _c ∈ T, C*(δ⁻¹)^k := Finset.sum_le_sum (fun c _ => hCb δ hδ c w)
    _ = (T.card : ℝ)*(C*(δ⁻¹)^k) := by rw [Finset.sum_const,nsmul_eq_mul]
    _ ≤ 5^d*(C*(δ⁻¹)^k) := mul_le_mul_of_nonneg_right
      (separated_ambient_overlap S hδ hsep w) (by positivity)
    _ = _ := by ring


theorem capReciprocal_global_derivatives (d k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (δ : ℝ) (hδ : 0 < δ)
      (S : Finset (Sphere d)),
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ/2 ≤ dist x y) →
      ∀ w : Space d,
      ‖iteratedFDeriv ℝ k (capReciprocal δ hδ S) w‖ ≤ C*(δ⁻¹)^k := by
  choose B hB hBb using fun j => capDenominator_global_derivatives d j
  obtain ⟨C,hC,hCb⟩ := compact_iteratedFDeriv_bound
    (smoothReciprocal_contDiff 1 zero_lt_one)
    (isCompact_closedBall (0 : ℝ) (B 0)) k
  refine ⟨mixedCompositionBudget B k*C,
    mul_nonneg (mixedCompositionBudget_nonneg hB k) hC, ?_⟩
  intro δ hδ S hsep w
  have hmem : capDenominator δ hδ S w ∈ Metric.closedBall (0 : ℝ) (B 0) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    simpa using hBb 0 δ hδ S hsep w
  exact mixed_composition_derivative_bound
    (capDenominator_contDiff hδ S).contDiffAt
    (smoothReciprocal_contDiff 1 zero_lt_one).contDiffAt hC k
    (fun j hj => hCb j hj _ hmem)
    (fun j _ _ => hBb j δ hδ S hsep w)

theorem normalizedCap_global_derivatives (d k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (δ : ℝ) (hδ : 0 < δ)
      (S : Finset (Sphere d)),
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ/2 ≤ dist x y) →
      ∀ (c : Sphere d) (w : Space d),
      ‖iteratedFDeriv ℝ k (normalizedCap δ hδ S c) w‖ ≤ C*(δ⁻¹)^k := by
  choose B hB hBb using fun j => capBump_ambient_derivatives d j
  choose Q hQ hQb using fun j => capReciprocal_global_derivatives d j
  let A := ∑ j ∈ Finset.range (k+1), (k.choose j : ℝ)*B j*Q (k-j)
  have hA : 0 ≤ A := Finset.sum_nonneg (fun j _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB j)) (hQ _))
  refine ⟨A,hA,?_⟩
  intro δ hδ S hsep c w
  apply (norm_iteratedFDeriv_mul_le (capBump δ hδ c).contDiff
    (capReciprocal_contDiff hδ S) w (by simp : (k : ℕ∞ω) ≤ ∞)).trans
  change _ ≤ (∑ j ∈ Finset.range (k+1), (k.choose j : ℝ)*B j*Q (k-j))*(δ⁻¹)^k
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  calc
    _ ≤ (k.choose j : ℝ)*(B j*(δ⁻¹)^j)*(Q (k-j)*(δ⁻¹)^(k-j)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hBb j δ hδ c w) (Nat.cast_nonneg _))
        (hQb (k-j) δ hδ S hsep w) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hB j) (by positivity)))
    _ = _ := by
      have hp : (δ⁻¹)^j*(δ⁻¹)^(k-j) = (δ⁻¹)^k := by
        rw [← pow_add,Nat.add_sub_of_le hjk]
      calc
        _ = ((k.choose j : ℝ)*B j*Q (k-j))*((δ⁻¹)^j*(δ⁻¹)^(k-j)) := by ring
        _ = _ := by rw [hp]


theorem capCutoffAmbient_global_derivatives (d k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (δ : ℝ) (hδ : 0 < δ)
      (S : Finset (Sphere d)),
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ/2 ≤ dist x y) →
      ∀ (U : Set (Sphere d)) (w : Space d),
      ‖iteratedFDeriv ℝ k (capCutoffAmbient δ hδ S U) w‖ ≤ B*(δ⁻¹)^k := by
  classical
  obtain ⟨C,hC,hCb⟩ := normalizedCap_global_derivatives d k
  refine ⟨5^d*C, by positivity, ?_⟩
  intro δ hδ S hsep U w
  let S₀ := cutoffCapCenters δ S U
  let T := S₀.filter (fun c : Sphere d => dist w (c : Space d) ≤ δ)
  let f := fun c : Sphere d =>
    iteratedFDeriv ℝ k (normalizedCap δ hδ S c) w
  have hsub : S₀ ⊆ S := Finset.filter_subset _ _
  have hzero (c : Sphere d) (hc : c ∈ S₀) (hct : c ∉ T) : f c = 0 := by
    have hd : δ < dist w (c : Space d) :=
      lt_of_not_ge (fun h => hct (Finset.mem_filter.mpr ⟨hc,h⟩))
    exact normalizedCap_ambient_derivative_zero hδ S c w (by
      simpa only [dist_eq_norm] using hd) k
  have hsum : (∑ c ∈ S₀, f c) = ∑ c ∈ T, f c := by
    symm
    exact Finset.sum_subset (Finset.filter_subset _ _) hzero
  change ‖iteratedFDeriv ℝ k (fun x => ∑ c ∈ S₀, normalizedCap δ hδ S c x) w‖ ≤ _
  rw [iteratedFDeriv_fun_sum_apply
    (fun c _ => ((normalizedCap_contDiff hδ S c).of_le (by simp)).contDiffAt)]
  change ‖∑ c ∈ S₀, f c‖ ≤ _
  rw [hsum]
  calc
    _ ≤ ∑ c ∈ T, ‖f c‖ := norm_sum_le _ _
    _ ≤ ∑ _c ∈ T, C*(δ⁻¹)^k := Finset.sum_le_sum (fun c _ => hCb δ hδ S hsep c w)
    _ = (T.card : ℝ)*(C*(δ⁻¹)^k) := by rw [Finset.sum_const,nsmul_eq_mul]
    _ ≤ 5^d*(C*(δ⁻¹)^k) := mul_le_mul_of_nonneg_right
      (separated_ambient_overlap S₀ hδ
        (fun x hx y hy hxy => hsep x (hsub hx) y (hsub hy) hxy) w) (by positivity)
    _ = _ := by ring



theorem smoothReciprocal_nonneg {τ u : ℝ} (hτ : 0 < τ) (hu : 0 ≤ u) :
    0 ≤ smoothReciprocal τ hτ u :=
  mul_nonneg (sub_nonneg.mpr (PlanarFalconer.sineZeroCutoff τ hτ).le_one)
    (inv_nonneg.mpr hu)

theorem mul_smoothReciprocal_le_one {τ u : ℝ} (hτ : 0 < τ) :
    u*smoothReciprocal τ hτ u ≤ 1 := by
  by_cases hu : u = 0
  · simp [hu]
  · calc
      u*smoothReciprocal τ hτ u = 1-PlanarFalconer.sineZeroCutoff τ hτ u := by
        unfold smoothReciprocal
        rw [mul_comm (1-_),← mul_assoc,mul_inv_cancel₀ hu,one_mul]
      _ ≤ 1 := sub_le_self _ (PlanarFalconer.sineZeroCutoff τ hτ).nonneg

theorem normalizedCap_global_nonneg {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Sphere d)) (c : Sphere d) (x : Space d) :
    0 ≤ normalizedCap δ hδ S c x := by
  have hden : 0 ≤ capDenominator δ hδ S x :=
    Finset.sum_nonneg (fun c _ => (capBump δ hδ c).nonneg)
  exact mul_nonneg (capBump δ hδ c).nonneg (smoothReciprocal_nonneg zero_lt_one hden)

theorem normalizedCap_global_sum_le_one {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Sphere d)) (x : Space d) :
    ∑ c ∈ S, normalizedCap δ hδ S c x ≤ 1 := by
  simp only [normalizedCap,← Finset.sum_mul]
  exact mul_smoothReciprocal_le_one zero_lt_one

theorem capCutoffAmbient_global_bounds {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Sphere d)) (U : Set (Sphere d)) (x : Space d) :
    0 ≤ capCutoffAmbient δ hδ S U x ∧ capCutoffAmbient δ hδ S U x ≤ 1 := by
  classical
  constructor
  · exact Finset.sum_nonneg (fun c _ => normalizedCap_global_nonneg hδ S c x)
  · apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun c _ _ => normalizedCap_global_nonneg hδ S c x))
    exact normalizedCap_global_sum_le_one hδ S x

end Falconer

end OAI
