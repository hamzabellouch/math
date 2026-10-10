import OAI.Probability.GaussianPropeller.Dual

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal

open scoped RealInnerProductSpace

namespace GaussianPropeller.Reduction

variable {d k : ℕ} [NeZero k]

theorem optimal_width_le {A : Fin k → Set (Space d)} (hA : Optimal A)
    (v : Tuple d k) : width v ≤ Real.sqrt (value A) * ‖v‖ := by
  have hn : ‖moments (scoreCell v.ofLp)‖ ≤ Real.sqrt (value A) := by
    apply (Real.le_sqrt (norm_nonneg _) (value_nonneg A)).mpr
    rw [norm_moments_sq]
    exact hA.2 _ (scoreCell_partition _)
  rw [← pairing_scoreCell]
  calc
    ⟪v, moments (scoreCell v.ofLp)⟫ ≤ ‖v‖ * ‖moments (scoreCell v.ofLp)‖ := real_inner_le_norm _ _
    _ ≤ ‖v‖ * Real.sqrt (value A) := mul_le_mul_of_nonneg_left hn (norm_nonneg _)
    _ = _ := mul_comm _ _

omit [NeZero k] in
lemma erase_univ_nonempty (hk : 2 ≤ k) (i : Fin k) :
    (Finset.univ.erase i).Nonempty := by
  classical
  apply Finset.card_pos.mp
  simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  omega

noncomputable def omittedMax (hk : 2 ≤ k) (z : Fin k → Space d)
    (i : Fin k) (x : Space d) : ℝ :=
  (Finset.univ.erase i).sup' (erase_univ_nonempty hk i) (fun j => ⟪z j,x⟫)

noncomputable def recentered (z : Fin k → Space d) (i : Fin k) : Tuple d k :=
  WithLp.toLp 2 (fun j => if j = i then 0 else z j + ((k:ℝ)-1)⁻¹ • z i)

omit [NeZero k] in
lemma sum_erase_zero (z : Fin k → Space d) (hz : ∑ j, z j = 0) (i : Fin k) :
    ∑ j ∈ Finset.univ.erase i, z j = -z i := by
  classical
  have hh := Finset.sum_erase_add Finset.univ z (Finset.mem_univ i)
  rw [hz] at hh
  exact eq_neg_of_add_eq_zero_left hh

omit [NeZero k] in
lemma sum_erased_centered (hk : 2 ≤ k) (z : Fin k → Space d)
    (hz : ∑ j, z j = 0) (i : Fin k) :
    ∑ j ∈ Finset.univ.erase i, (z j + ((k:ℝ)-1)⁻¹ • z i) = 0 := by
  classical
  have hk' : (k:ℝ)-1 ≠ 0 := by exact_mod_cast (show (k:ℤ)-1 ≠ 0 by omega)
  rw [Finset.sum_add_distrib, sum_erase_zero z hz i,
    Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
    Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  simp only [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one,
    mul_inv_cancel₀ hk', one_smul, neg_add_cancel]

omit [NeZero k] in
lemma recentered_norm_sq (hk : 2 ≤ k) (z : Fin k → Space d)
    (hz : ∑ j, z j = 0) (i : Fin k) :
    ‖recentered z i‖^2 = (∑ j, ‖z j‖^2) -
      ((k:ℝ)/((k:ℝ)-1)) * ‖z i‖^2 := by
  classical
  let b : ℝ := ((k:ℝ)-1)⁻¹
  have hk' : (k:ℝ)-1 ≠ 0 := by exact_mod_cast (show (k:ℤ)-1 ≠ 0 by omega)
  have he : ‖recentered z i‖^2 =
      ∑ j ∈ Finset.univ.erase i, ‖z j + b • z i‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    change (∑ j, ‖if j = i then 0 else z j + b • z i‖^2) = _
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    simp only [ite_true, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    rw [ite_eq_right (Finset.ne_of_mem_erase hj)]
  rw [he]
  simp_rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hn := Finset.sum_erase_add Finset.univ (fun j => ‖z j‖^2) (Finset.mem_univ i)
  have hi : ∑ j ∈ Finset.univ.erase i, 2 * (b * ⟪z j,z i⟫) = -2*b*‖z i‖^2 := by
    simp_rw [← mul_assoc]
    rw [← Finset.mul_sum, ← sum_inner, sum_erase_zero z hz i, inner_neg_left,
      real_inner_self_eq_norm_sq]
    ring
  rw [hi, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  dsimp [b]
  rw [← hn]
  field_simp
  ring

lemma scoreMax_recentered (hk : 2 ≤ k) (z : Fin k → Space d)
    (hz : ∑ j, z j = 0) (i : Fin k) (x : Space d) :
    scoreMax (recentered z i).ofLp x = omittedMax hk z i x + ⟪((k:ℝ)-1)⁻¹ • z i,x⟫ := by
  classical
  let f : Fin k → ℝ := fun j => ⟪z j + ((k:ℝ)-1)⁻¹ • z i,x⟫
  have hsum : ∑ j ∈ Finset.univ.erase i, f j = 0 := by
    rw [← sum_inner, sum_erased_centered hk z hz i, inner_zero_left]
  have hnon : 0 ≤ (Finset.univ.erase i).sup' (erase_univ_nonempty hk i) f := by
    by_contra! hn
    have hh : ∑ j ∈ Finset.univ.erase i, f j < 0 := Finset.sum_neg
      (fun j hj => (Finset.le_sup' f hj).trans_lt hn) (erase_univ_nonempty hk i)
    linarith
  have hex : (Finset.univ.erase i).sup' (erase_univ_nonempty hk i) f =
      omittedMax hk z i x + ⟪((k:ℝ)-1)⁻¹ • z i,x⟫ := by
    dsimp only [omittedMax, f]
    simp_rw [inner_add_left]
    exact (Finset.sup'_add _ _ _ _).symm
  rw [← hex]
  apply le_antisymm
  · apply (scoreMax_le_iff _ _ _).mpr
    intro j
    change ⟪if j = i then 0 else z j + ((k:ℝ)-1)⁻¹ • z i,x⟫ ≤ _
    by_cases hji : j = i
    · simpa only [ite_eq_left hji, inner_zero_left] using hnon
    · rw [ite_eq_right hji]
      exact Finset.le_sup' f (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩)
  · apply (Finset.sup'_le_iff _ _).mpr
    intro j hj
    have hh := le_scoreMax (recentered z i).ofLp j x
    change ⟪if j = i then 0 else z j + ((k:ℝ)-1)⁻¹ • z i,x⟫ ≤ _ at hh
    simpa only [ite_eq_right (Finset.ne_of_mem_erase hj)] using hh

lemma omittedMax_integrable (hk : 2 ≤ k) (z : Fin k → Space d)
    (hz : ∑ j, z j = 0) (i : Fin k) :
    Integrable (omittedMax hk z i) (gaussian d) := by
  have heq : omittedMax hk z i = fun x => scoreMax (recentered z i).ofLp x -
      ⟪((k:ℝ)-1)⁻¹ • z i,x⟫ := by
    funext x
    rw [scoreMax_recentered hk z hz i x]
    ring
  rw [heq]
  exact (integrable_scoreMax _).sub
    (Integrable.const_inner _ (integrable_id_gaussian d))

lemma integral_omittedMax (hk : 2 ≤ k) (z : Fin k → Space d)
    (hz : ∑ j, z j = 0) (i : Fin k) :
    ∫ x, omittedMax hk z i x ∂gaussian d = width (recentered z i) := by
  have heq : scoreMax (recentered z i).ofLp = fun x => omittedMax hk z i x +
      ⟪((k:ℝ)-1)⁻¹ • z i,x⟫ := funext (scoreMax_recentered hk z hz i)
  rw [width, heq]
  change _ = ∫ x, omittedMax hk z i x + ⟪((k:ℝ)-1)⁻¹ • z i,x⟫ ∂gaussian d
  have hi : Integrable (fun x : Space d => ⟪((k:ℝ)-1)⁻¹ • z i,x⟫) (gaussian d) :=
    Integrable.const_inner _ (integrable_id_gaussian d)
  rw [integral_add (omittedMax_integrable hk z hz i) hi]
  have hz0 : (∫ x : Space d, ⟪((k:ℝ)-1)⁻¹ • z i,x⟫ ∂gaussian d) = 0 := by
    rw [integral_inner (integrable_id_gaussian d)]
    simp only [gaussian, integral_id_stdGaussian, inner_zero_right]
  rw [hz0, add_zero]

lemma scoreMax_eq_max_omitted (hk : 2 ≤ k) (z : Fin k → Space d)
    (i : Fin k) (x : Space d) : scoreMax z x = max ⟪z i,x⟫ (omittedMax hk z i x) := by
  classical
  apply le_antisymm
  · apply (scoreMax_le_iff _ _ _).mpr
    intro j
    by_cases hji : j = i
    · subst j
      exact le_max_left _ _
    · exact (Finset.le_sup' (fun j => ⟪z j,x⟫)
        (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩)).trans (le_max_right _ _)
  · apply max_le
    · exact le_scoreMax z i x
    · exact Finset.sup'_le _ _ (fun j _ => le_scoreMax z j x)

lemma positive_gap_eq (hk : 2 ≤ k) (z : Fin k → Space d)
    (i : Fin k) (x : Space d) :
    max (⟪z i,x⟫ - omittedMax hk z i x) 0 = scoreMax z x - omittedMax hk z i x := by
  rw [scoreMax_eq_max_omitted hk z i x]
  simpa only [sub_self] using max_sub_sub_right ⟪z i,x⟫ (omittedMax hk z i x) (omittedMax hk z i x)

theorem optimal_loss_lower (hk : 2 ≤ k) {A : Fin k → Set (Space d)}
    (hA : Optimal A) (i : Fin k) :
    value A - Real.sqrt (value A) *
      Real.sqrt (value A - ((k:ℝ)/((k:ℝ)-1)) * ‖centroid (A i)‖^2) ≤
    ∫ x, max (⟪centroid (A i),x⟫ -
      omittedMax hk (fun j => centroid (A j)) i x) 0 ∂gaussian d := by
  let z : Fin k → Space d := fun j => centroid (A j)
  have hz : ∑ j, z j = 0 := sum_centroid_eq_zero hA.1
  have hn : ‖recentered z i‖ =
      Real.sqrt (value A - ((k:ℝ)/((k:ℝ)-1)) * ‖centroid (A i)‖^2) := by
    rw [← show ‖recentered z i‖^2 = value A - ((k:ℝ)/((k:ℝ)-1)) *
      ‖centroid (A i)‖^2 from recentered_norm_sq hk z hz i, Real.sqrt_sq (norm_nonneg _)]
  have heq : (fun x => max (⟪centroid (A i),x⟫ - omittedMax hk z i x) 0) =
      fun x => scoreMax z x - omittedMax hk z i x := funext (positive_gap_eq hk z i)
  change _ ≤ ∫ x, max (⟪centroid (A i),x⟫ - omittedMax hk z i x) 0 ∂gaussian d
  rw [heq]
  have hiz : Integrable (scoreMax z) (gaussian d) := integrable_scoreMax (WithLp.toLp 2 z)
  rw [integral_sub hiz (omittedMax_integrable hk z hz i), integral_omittedMax hk z hz i]
  change _ ≤ width (moments A) - width (recentered z i)
  rw [width_moments_of_optimal hA]
  have hb := optimal_width_le hA (recentered z i)
  rw [hn] at hb
  linarith

end GaussianPropeller.Reduction

end OAI
