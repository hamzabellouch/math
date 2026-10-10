import Mathlib

namespace OAI

noncomputable section
open scoped InnerProductSpace Topology
open Filter

namespace ProjectionConcavity

lemma abs_add_abs_sub_of_abs_le {a b : ℝ} (h : |b| ≤ |a|) :
    |a + b| + |a - b| = 2 * |a| := by
  by_cases ha : 0 ≤ a
  · rw [abs_of_nonneg ha] at h ⊢
    have hb := abs_le.mp h
    rw [abs_of_nonneg (by linarith : 0 ≤ a + b),
      abs_of_nonneg (by linarith : 0 ≤ a - b)]
    ring
  · have ha' : a ≤ 0 := le_of_not_ge ha
    rw [abs_of_nonpos ha'] at h ⊢
    have hb := abs_le.mp h
    rw [abs_of_nonpos (by linarith : a + b ≤ 0),
      abs_of_nonpos (by linarith : a - b ≤ 0)]
    ring

lemma exists_pos_mul_abs_le {ι : Type*} [Fintype ι] (a b : ι → ℝ)
    (hzero : ∀ i, a i = 0 → b i = 0) :
    ∃ t : ℝ, 0 < t ∧ ∀ i, |t * b i| ≤ |a i| := by
  have hi (i : ι) : ∀ᶠ t : ℝ in 𝓝 0, |t * b i| ≤ |a i| := by
    by_cases ha : a i = 0
    · simp [ha, hzero i ha]
    · have ha' : 0 < |a i| := abs_pos.mpr ha
      have hb' : 0 < |b i| + 1 := by positivity
      apply Metric.eventually_nhds_iff.mpr
      refine ⟨|a i| / (|b i| + 1), div_pos ha' hb', ?_⟩
      intro t ht
      rw [Real.dist_eq, sub_zero] at ht
      rw [abs_mul]
      calc
        |t| * |b i| ≤ |t| * (|b i| + 1) := by
          nlinarith only [abs_nonneg t]
        _ ≤ |a i| := ((lt_div_iff₀ hb').mp ht).le
  have hall : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, |t * b i| ≤ |a i| :=
    eventually_all.mpr hi
  obtain ⟨r, hr, h⟩ := Metric.eventually_nhds_iff.mp hall
  refine ⟨r / 2, half_pos hr, h ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hr)]
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι]

lemma normalize_decreases (n : ι → E) {x u : E}
    (hx : 1 < ‖x‖) (hu : 0 < ∑ i, |inner ℝ (n i) u|)
    (hcost : (∑ i, |inner ℝ (n i) x|) ≤ ∑ i, |inner ℝ (n i) u|) :
    ∃ w : E, ‖w‖ = 1 ∧
      (∑ i, |inner ℝ (n i) w|) < ∑ i, |inner ℝ (n i) u| := by
  have hx0 : 0 < ‖x‖ := lt_trans zero_lt_one hx
  refine ⟨‖x‖⁻¹ • x, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx0)]
    exact inv_mul_cancel₀ (ne_of_gt hx0)
  · simp_rw [inner_smul_right, abs_mul, abs_of_pos (inv_pos.mpr hx0)]
    rw [← Finset.mul_sum]
    have hstrict : (∑ i, |inner ℝ (n i) x|) <
        (∑ i, |inner ℝ (n i) u|) * ‖x‖ := by
      exact hcost.trans_lt (by nlinarith only [mul_lt_mul_of_pos_left hx hu])
    have hdiv := (div_lt_iff₀ hx0).mpr hstrict
    simpa only [div_eq_mul_inv, mul_comm] using hdiv

theorem exists_unit_lower_abs_inner_sum (n : ι → E) {u v : E}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0)
    (hpos : 0 < ∑ i, |inner ℝ (n i) u|)
    (hzero : ∀ i, inner ℝ (n i) u = 0 → inner ℝ (n i) v = 0) :
    ∃ w : E, ‖w‖ = 1 ∧
      (∑ i, |inner ℝ (n i) w|) < ∑ i, |inner ℝ (n i) u| := by
  obtain ⟨t, ht, hsmall⟩ := exists_pos_mul_abs_le
    (fun i => inner ℝ (n i) u) (fun i => inner ℝ (n i) v) hzero
  have hplus : 1 < ‖u + t • v‖ := by
    have h := norm_add_sq_real u (t • v)
    rw [hu, norm_smul, hv, Real.norm_eq_abs, abs_of_pos ht,
      inner_smul_right, huv] at h
    nlinarith only [h, sq_pos_of_pos ht, norm_nonneg (u + t • v)]
  have hminus : 1 < ‖u - t • v‖ := by
    have h := norm_sub_sq_real u (t • v)
    rw [hu, norm_smul, hv, Real.norm_eq_abs, abs_of_pos ht,
      inner_smul_right, huv] at h
    nlinarith only [h, sq_pos_of_pos ht, norm_nonneg (u - t • v)]
  have hsum : (∑ i, |inner ℝ (n i) (u + t • v)|) +
      (∑ i, |inner ℝ (n i) (u - t • v)|) = 2 * ∑ i, |inner ℝ (n i) u| := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [inner_add_right, inner_sub_right, inner_smul_right]
    exact abs_add_abs_sub_of_abs_le (hsmall i)
  by_cases h : (∑ i, |inner ℝ (n i) (u + t • v)|) ≤ ∑ i, |inner ℝ (n i) u|
  · exact normalize_decreases n hplus hpos h
  · apply normalize_decreases n hminus hpos
    linarith only [hsum, lt_of_not_ge h]

end ProjectionConcavity

namespace ProjectionConcavity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

lemma exists_unit_orthogonal_of_finrank_lt (K : Submodule ℝ E)
    (hK : Module.finrank ℝ K < Module.finrank ℝ E) :
    ∃ v : E, ‖v‖ = 1 ∧ ∀ x ∈ K, inner ℝ x v = 0 := by
  have hdim := K.finrank_add_finrank_orthogonal
  have hpos : 0 < Module.finrank ℝ Kᗮ := by omega
  have : Nontrivial Kᗮ := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨w, hw⟩ : ∃ w : Kᗮ, w ≠ 0 := exists_ne 0
  have hw' : (w : E) ≠ 0 := fun h => hw (Subtype.ext h)
  have hn : 0 < ‖(w : E)‖ := norm_pos_iff.mpr hw'
  refine ⟨‖(w : E)‖⁻¹ • (w : E), ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
    exact inv_mul_cancel₀ (ne_of_gt hn)
  · intro x hx
    rw [inner_smul_right, (K.mem_orthogonal (w : E)).mp w.property x hx, mul_zero]

variable {ι : Type*} [Fintype ι]

theorem minimizing_unit_annihilates_two (n : ι → E) {u : E}
    (hdim : 3 ≤ Module.finrank ℝ E) (hu : ‖u‖ = 1)
    (hpos : 0 < ∑ i, |inner ℝ (n i) u|)
    (hmin : ∀ w : E, ‖w‖ = 1 →
      (∑ i, |inner ℝ (n i) u|) ≤ ∑ i, |inner ℝ (n i) w|) :
    ∃ i j : ι, i ≠ j ∧ inner ℝ (n i) u = 0 ∧ inner ℝ (n j) u = 0 := by
  classical
  by_contra hnone
  have hunique : ∀ i j : ι, inner ℝ (n i) u = 0 → inner ℝ (n j) u = 0 → i = j := by
    intro i j hi hj
    by_contra hij
    exact hnone ⟨i, j, hij, hi, hj⟩
  have obtain_v : ∃ v : E, ‖v‖ = 1 ∧ inner ℝ u v = 0 ∧
      ∀ i, inner ℝ (n i) u = 0 → inner ℝ (n i) v = 0 := by
    by_cases hex : ∃ i, inner ℝ (n i) u = 0
    · obtain ⟨i, hi⟩ := hex
      let K := Submodule.span ℝ (↑({u, n i} : Finset E) : Set E)
      have hK : Module.finrank ℝ K ≤ 2 := by
        have h := finrank_span_finset_le_card (R := ℝ) ({u, n i} : Finset E)
        have hc : ({u, n i} : Finset E).card ≤ 2 := by simpa using (Finset.card_insert_le u ({n i} : Finset E))
        exact h.trans hc
      obtain ⟨v, hv, horth⟩ := exists_unit_orthogonal_of_finrank_lt K (by omega)
      refine ⟨v, hv, horth u (Submodule.subset_span (by simp)), ?_⟩
      intro j hj
      have hji : j = i := hunique j i hj hi
      subst j
      exact horth (n i) (Submodule.subset_span (by simp))
    · let K := Submodule.span ℝ (↑({u} : Finset E) : Set E)
      have hK : Module.finrank ℝ K ≤ 1 := by
        have h := finrank_span_finset_le_card (R := ℝ) ({u} : Finset E)
        change Module.finrank ℝ K ≤ ({u} : Finset E).card at h
        simpa only [Finset.card_singleton] using h
      obtain ⟨v, hv, horth⟩ := exists_unit_orthogonal_of_finrank_lt K (by omega)
      refine ⟨v, hv, horth u (Submodule.subset_span (by simp)), ?_⟩
      intro i hi
      exact False.elim (hex ⟨i, hi⟩)
  obtain ⟨v, hv, huv, hz⟩ := obtain_v
  obtain ⟨w, hw, hless⟩ := exists_unit_lower_abs_inner_sum n hu hv huv hpos hz
  exact (not_lt_of_ge (hmin w hw)) hless

end ProjectionConcavity

namespace ProjectionConcavity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]

theorem exists_minimizing_unit_annihilates_two (n : ι → E)
    (hdim : 3 ≤ Module.finrank ℝ E)
    (hpos : ∀ u : E, ‖u‖ = 1 → 0 < ∑ i, |inner ℝ (n i) u|) :
    ∃ u : E, ‖u‖ = 1 ∧
      (∀ w : E, ‖w‖ = 1 →
        (∑ i, |inner ℝ (n i) u|) ≤ ∑ i, |inner ℝ (n i) w|) ∧
      ∃ i j : ι, i ≠ j ∧ inner ℝ (n i) u = 0 ∧ inner ℝ (n j) u = 0 := by
  have hdim0 : 0 < Module.finrank ℝ E := by omega
  have : Nontrivial E := Module.nontrivial_of_finrank_pos hdim0
  have hc : Continuous (fun u : E => ∑ i, |inner ℝ (n i) u|) := by fun_prop
  obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr (by norm_num : (0 : ℝ) ≤ 1)) hc.continuousOn
  have hu' : ‖u‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hu
  have hm : ∀ w : E, ‖w‖ = 1 →
      (∑ i, |inner ℝ (n i) u|) ≤ ∑ i, |inner ℝ (n i) w| := by
    intro w hw
    exact hmin (by simpa only [Metric.mem_sphere, dist_zero_right] using hw)
  exact ⟨u, hu', hm, minimizing_unit_annihilates_two n hdim hu' (hpos u hu') hm⟩

end ProjectionConcavity

end

end OAI
