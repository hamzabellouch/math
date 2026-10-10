import OAI.Analysis.Mahler.HannerBodies
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Strict.Extreme

namespace OAI

noncomputable section

namespace SymmetricMahler

section
open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def IsMetricMedian (x : Fin 3 → E) (m : E) : Prop :=
  ∀ i j, i ≠ j → dist (x i) (x j) = dist (x i) m + dist m (x j)

def HasMetricMedians (E : Type*) [PseudoMetricSpace E] : Prop :=
  ∀ x : Fin 3 → E, ∃ m, ∀ i j, i ≠ j →
    dist (x i) (x j) = dist (x i) m + dist m (x j)

def ThreeBallIntersection (E : Type*) [PseudoMetricSpace E] : Prop :=
  ∀ (x : Fin 3 → E) (r : Fin 3 → ℝ), (∀ i, 0 ≤ r i) →
    (∀ i j, i ≠ j → (closedBall (x i) (r i) ∩ closedBall (x j) (r j)).Nonempty) →
    (⋂ i, closedBall (x i) (r i)).Nonempty

lemma segment_point_distances (m x : E) {r : ℝ}
    (hr : 0 ≤ r) (hrd : r ≤ dist m x) (hd : 0 < dist m x) :
    ∃ z : E, dist z x = r ∧ dist z m = dist m x - r := by
  let d := dist m x
  let z := x + (r / d) • (m - x)
  have hd0 : d ≠ 0 := ne_of_gt hd
  have ha : 0 ≤ r / d := div_nonneg hr hd.le
  have ha1 : r / d ≤ 1 := (div_le_one hd).mpr hrd
  have hz : z - m = (1 - r / d) • (x - m) := by
    dsimp [z]
    module
  refine ⟨z, ?_, ?_⟩
  · rw [dist_eq_norm]
    change ‖x + (r / d) • (m - x) - x‖ = r
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
    rw [← dist_eq_norm]
    change r / d * d = r
    exact div_mul_cancel₀ _ hd0
  · rw [dist_eq_norm, hz, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr ha1), ← dist_eq_norm, dist_comm x m]
    change (1 - r / d) * d = d - r
    field_simp

theorem threeBallIntersection_of_metricMedians (hmedian : HasMetricMedians E) :
    ThreeBallIntersection E := by
  intro x r hr hinter
  obtain ⟨m, hm⟩ := hmedian x
  have hpair : ∀ i j, i ≠ j → dist m (x i) + dist m (x j) ≤ r i + r j := by
    intro i j hij
    obtain ⟨w, hwi, hwj⟩ := hinter i j hij
    have ht := dist_triangle (x i) w (x j)
    have hi : dist (x i) w ≤ r i := by simpa [dist_comm] using hwi
    have hj : dist w (x j) ≤ r j := hwj
    rw [hm i j hij, dist_comm (x i) m] at ht
    linarith
  by_cases hall : ∀ i, dist m (x i) ≤ r i
  · exact ⟨m, mem_iInter.mpr hall⟩
  · push Not at hall
    obtain ⟨i, hi⟩ := hall
    have hd : 0 < dist m (x i) := lt_of_le_of_lt (hr i) hi
    obtain ⟨z, hzi, hzm⟩ := segment_point_distances m (x i) (hr i) hi.le hd
    refine ⟨z, mem_iInter.mpr fun j => ?_⟩
    change dist z (x j) ≤ r j
    by_cases hji : j = i
    · simp [hji, hzi]
    · have hp := hpair i j (Ne.symm hji)
      have ht := dist_triangle z m (x j)
      rw [hzm] at ht
      linarith

theorem metricMedians_of_threeBallIntersection (hballs : ThreeBallIntersection E) :
    HasMetricMedians E := by
  intro x
  let a := dist (x 0) (x 1)
  let b := dist (x 0) (x 2)
  let c := dist (x 1) (x 2)
  let r : Fin 3 → ℝ := ![(a + b - c) / 2, (a + c - b) / 2, (b + c - a) / 2]
  have habc : c ≤ a + b := by
    simpa [a, b, c, dist_comm] using dist_triangle (x 1) (x 0) (x 2)
  have hacb : b ≤ a + c := dist_triangle (x 0) (x 1) (x 2)
  have hbca : a ≤ b + c := by
    simpa [a, b, c, dist_comm] using dist_triangle (x 0) (x 2) (x 1)
  have hr : ∀ i, 0 ≤ r i := by
    intro i
    fin_cases i <;> dsimp [r] <;> linarith
  have hsum : ∀ i j, i ≠ j → r i + r j = dist (x i) (x j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [r, a, b, c]
    all_goals
      try rw [dist_comm (x 1) (x 0)]
      try rw [dist_comm (x 2) (x 0)]
      try rw [dist_comm (x 2) (x 1)]
      ring
  have hinter : ∀ i j, i ≠ j →
      (closedBall (x i) (r i) ∩ closedBall (x j) (r j)).Nonempty := by
    intro i j hij
    have hs := hsum i j hij
    by_cases hd : dist (x i) (x j) = 0
    · have hx : x i = x j := dist_eq_zero.mp hd
      refine ⟨x i, ?_, ?_⟩ <;> simpa [hx] using (hr _)
    · have hdpos : 0 < dist (x i) (x j) := lt_of_le_of_ne (dist_nonneg) (Ne.symm hd)
      obtain ⟨z, hzj, hzi⟩ := segment_point_distances (x i) (x j) (hr j)
        (by linarith [hr i]) hdpos
      exact ⟨z, by change dist z (x i) ≤ r i; linarith,
        by change dist z (x j) ≤ r j; exact hzj.le⟩
  obtain ⟨m, hm⟩ := hballs x r hr hinter
  have hm' : ∀ i, dist m (x i) ≤ r i := mem_iInter.mp hm
  refine ⟨m, fun i j hij => ?_⟩
  apply le_antisymm (dist_triangle _ _ _)
  have hi := hm' i
  have hj := hm' j
  rw [dist_comm (x i) m]
  linarith [hsum i j hij]

 theorem metricMedians_iff_threeBallIntersection :
    HasMetricMedians E ↔ ThreeBallIntersection E :=
  ⟨threeBallIntersection_of_metricMedians, metricMedians_of_threeBallIntersection⟩

theorem median_of_aggregate_decomposition (x y rp rm : E)
    (hadd : rp + rm = x - y)
    (hp : ‖rp‖ ≤ (‖x-y‖ + ‖x‖ - ‖y‖)/2)
    (hm : ‖rm‖ ≤ (‖x-y‖ - ‖x‖ + ‖y‖)/2)
    (hrem : ‖x+y-(rp-rm)‖ ≤ ‖x‖ + ‖y‖ - ‖x-y‖) :
    ∃ m : E, ‖x‖ = ‖m‖ + ‖x-m‖ ∧ ‖y‖ = ‖m‖ + ‖y-m‖ ∧
      ‖x-y‖ = ‖x-m‖ + ‖m-y‖ := by
  let m := x-rp
  have hx : x-m = rp := by dsimp [m]; abel
  have hy : m-y = rm := by
    calc
      _ = (x-y)-rp := by dsimp [m]; abel
      _ = (rp+rm)-rp := by rw [hadd]
      _ = rm := by abel
  have htwo : x+y-(rp-rm) = (2 : ℝ) • m := by
    have hy' : y = x-(rp+rm) := by rw [hadd]; abel
    rw [hy']
    dsimp [m]
    module
  have hmn : ‖m‖ ≤ (‖x‖ + ‖y‖ - ‖x-y‖)/2 := by
    rw [htwo, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at hrem
    linarith
  have hxt : ‖x‖ ≤ ‖m‖ + ‖rp‖ := by
    have := norm_add_le m rp
    have he : m+rp = x := by dsimp [m]; abel
    simpa [he] using this
  have hyt : ‖y‖ ≤ ‖m‖ + ‖rm‖ := by
    have := norm_sub_le m rm
    have he : m-rm = y := by rw [← hy]; abel
    simpa [he] using this
  have hpt : ‖x-y‖ ≤ ‖rp‖ + ‖rm‖ := by
    rw [← hadd]
    exact norm_add_le _ _
  refine ⟨m, ?_, ?_, ?_⟩
  · rw [hx]; linarith
  · rw [← norm_neg (y-m), neg_sub, hy]; linarith
  · rw [hx, hy]; linarith

lemma extreme_unit_norm_add {x u : E}
    (hx : x ∈ (closedBall (0 : E) 1).extremePoints ℝ) (hnx : ‖x‖ = 1)
    (hadd : ‖u‖ + ‖x - u‖ = 1) : u = ‖u‖ • x := by
  by_cases hu : ‖u‖ = 0
  · have hu0 : u = 0 := norm_eq_zero.mp hu
    simp [hu0]
  by_cases hv : ‖x - u‖ = 0
  · have hv0 : x = u := sub_eq_zero.mp (norm_eq_zero.mp hv)
    simp [← hv0, hnx]
  have hup : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hu)
  have hvp : 0 < ‖x-u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
  have hnu : ‖u‖⁻¹ • u ∈ closedBall (0 : E) 1 := by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hup), inv_mul_cancel₀ hu]
  have hnv : ‖x-u‖⁻¹ • (x-u) ∈ closedBall (0 : E) 1 := by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hvp), inv_mul_cancel₀ hv]
  have hseg : x ∈ openSegment ℝ (‖u‖⁻¹ • u) (‖x-u‖⁻¹ • (x-u)) := by
    refine ⟨‖u‖, ‖x-u‖, hup, hvp, hadd, ?_⟩
    simp only [smul_smul, mul_inv_cancel₀ hu, mul_inv_cancel₀ hv, one_smul]
    abel
  have heq : ‖u‖⁻¹ • u = x := hx.2 hnu hnv hseg
  calc
    u = ‖u‖ • (‖u‖⁻¹ • u) := by rw [smul_smul, mul_inv_cancel₀ hu, one_smul]
    _ = ‖u‖ • x := by rw [heq]

theorem dist_extreme_unit_eq_two [Nontrivial E] (hmed : HasMetricMedians E)
    {x y : E} (hx : x ∈ (closedBall (0 : E) 1).extremePoints ℝ)
    (hy : y ∈ (closedBall (0 : E) 1).extremePoints ℝ) (hxy : x ≠ y) :
    dist x y = 2 := by
  have hnx : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp
    (extremePoints_closedBall_subset_sphere hx)
  have hny : ‖y‖ = 1 := mem_sphere_zero_iff_norm.mp
    (extremePoints_closedBall_subset_sphere hy)
  obtain ⟨m, hm⟩ := hmed ![0, x, y]
  have hmx : ‖m‖ + ‖x-m‖ = 1 := by
    have h := hm 0 1 (by decide)
    simpa [dist_eq_norm, norm_sub_rev, hnx] using h.symm
  have hmy : ‖m‖ + ‖y-m‖ = 1 := by
    have h := hm 0 2 (by decide)
    simpa [dist_eq_norm, norm_sub_rev, hny] using h.symm
  have hm0 : m = 0 := by
    by_contra hm0
    have h1 := extreme_unit_norm_add hx hnx hmx
    have h2 := extreme_unit_norm_add hy hny hmy
    have hn : ‖m‖ ≠ 0 := norm_ne_zero_iff.mpr hm0
    apply hxy
    have hh := congrArg (fun z : E => ‖m‖⁻¹ • z) (h1.symm.trans h2)
    simpa only [smul_smul, inv_mul_cancel₀ hn, one_smul] using hh
  have h := hm 1 2 (by decide)
  change dist x y = dist x m + dist m y at h
  norm_num [hm0, hnx, hny, dist_zero_left, dist_zero_right] at h ⊢
  exact h

theorem finite_extreme_unit_of_medians [FiniteDimensional ℝ E] [Nontrivial E]
    (hmed : HasMetricMedians E) :
    ((closedBall (0 : E) 1).extremePoints ℝ).Finite := by
  have htb : TotallyBounded ((closedBall (0 : E) 1).extremePoints ℝ) :=
    (isCompact_closedBall (0 : E) 1).totallyBounded.subset extremePoints_subset
  obtain ⟨t, ht, htfin, hcover⟩ := Metric.finite_approx_of_totallyBounded htb 1 zero_lt_one
  apply htfin.subset
  intro x hx
  obtain ⟨y, hyt, hxyball⟩ := mem_iUnion₂.mp (hcover hx)
  have heq : x = y := by
    by_contra hne
    have hd := dist_extreme_unit_eq_two hmed hx (ht hyt) hne
    have hb : dist x y < 1 := hxyball
    linarith
  exact heq ▸ hyt

theorem unitBall_eq_finite_convexHull_of_medians [FiniteDimensional ℝ E] [Nontrivial E]
    (hmed : HasMetricMedians E) :
    ∃ V : Set E, V.Finite ∧ closedBall (0 : E) 1 = convexHull ℝ V := by
  let V := (closedBall (0 : E) 1).extremePoints ℝ
  have hV : V.Finite := finite_extreme_unit_of_medians hmed
  refine ⟨V, hV, ?_⟩
  have h := closure_convexHull_extremePoints (isCompact_closedBall (0 : E) 1)
    (convex_closedBall (0 : E) 1)
  change closure (convexHull ℝ V) = closedBall (0 : E) 1 at h
  rw [(hV.isClosed_convexHull ℝ).closure_eq] at h
  exact h.symm

end

section
open Set Metric
open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [inst449 : NormedSpace ℝ E]

def aggregateSet (w : E) (A B : ℝ) : Set E :=
  {z | ∃ rp rm : E, rp + rm = w ∧ ‖rp‖ ≤ A ∧ ‖rm‖ ≤ B ∧ z = rp - rm}

omit inst449 in
lemma aggregateSet_eq_image [NormedSpace ℝ E] (w : E) (A B : ℝ) :
    aggregateSet w A B = (fun r : E × E => r.1 - r.2) ''
      ((closedBall (0 : E) A ×ˢ closedBall (0 : E) B) ∩
        {r : E × E | r.1 + r.2 = w}) := by
  ext z
  simp only [aggregateSet, Set.mem_ofPred_eq, mem_image, mem_inter_iff, mem_prod,
    mem_closedBall, dist_zero_right]
  constructor
  · rintro ⟨rp, rm, hadd, hp, hm, rfl⟩
    exact ⟨(rp, rm), ⟨⟨hp, hm⟩, hadd⟩, rfl⟩
  · rintro ⟨⟨rp, rm⟩, ⟨⟨hp, hm⟩, hadd⟩, rfl⟩
    exact ⟨rp, rm, hadd, hp, hm, rfl⟩

lemma isCompact_aggregateSet [FiniteDimensional ℝ E] (w : E) (A B : ℝ) :
    IsCompact (aggregateSet w A B) := by
  rw [aggregateSet_eq_image]
  exact (((isCompact_closedBall (0 : E) A).prod (isCompact_closedBall (0 : E) B)).inter_right
    (isClosed_eq (continuous_fst.add continuous_snd) continuous_const)).image
      (continuous_fst.sub continuous_snd)

lemma convex_aggregateSet (w : E) (A B : ℝ) : Convex ℝ (aggregateSet w A B) := by
  intro z hz v hv a b ha hb hab
  rcases hz with ⟨zp, zm, hzadd, hzp, hzm, rfl⟩
  rcases hv with ⟨vp, vm, hvadd, hvp, hvm, rfl⟩
  refine ⟨a • zp + b • vp, a • zm + b • vm, ?_, ?_, ?_, ?_⟩
  · calc
      _ = a • (zp + zm) + b • (vp + vm) := by module
      _ = w := by rw [hzadd, hvadd, ← add_smul, hab, one_smul]
  · calc
      _ ≤ ‖a • zp‖ + ‖b • vp‖ := norm_add_le _ _
      _ = a * ‖zp‖ + b * ‖vp‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * A + b * A := add_le_add (mul_le_mul_of_nonneg_left hzp ha)
        (mul_le_mul_of_nonneg_left hvp hb)
      _ = A := by rw [← add_mul, hab, one_mul]
  · calc
      _ ≤ ‖a • zm‖ + ‖b • vm‖ := norm_add_le _ _
      _ = a * ‖zm‖ + b * ‖vm‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * B + b * B := add_le_add (mul_le_mul_of_nonneg_left hzm ha)
        (mul_le_mul_of_nonneg_left hvm hb)
      _ = B := by rw [← add_mul, hab, one_mul]
  · module

lemma exists_unitBall_dual_maximizer [FiniteDimensional ℝ E] (f : E →L[ℝ] ℝ) :
    ∃ v : E, ‖v‖ ≤ 1 ∧ f v = ‖f‖ := by
  obtain ⟨v, hv, hmax⟩ := (isCompact_closedBall (0 : E) 1).exists_isMaxOn
    (nonempty_closedBall.mpr (by norm_num)) f.continuous.continuousOn
  have hvnorm : ‖v‖ ≤ 1 := by simpa using hv
  have hfv : 0 ≤ f v := by
    have := hmax (by simp : (0 : E) ∈ closedBall 0 1)
    simpa using this
  have hupper (x : E) : f x ≤ f v * ‖x‖ := by
    by_cases hx : x = 0
    · simp [hx]
    have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hunit : ‖(‖x‖⁻¹ : ℝ) • x‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hnx.le),
        inv_mul_cancel₀ hnx.ne']
    have hh := hmax (by simpa using hunit)
    have hh' : ‖x‖⁻¹ * f x ≤ f v := by simpa using hh
    have := mul_le_mul_of_nonneg_left hh' hnx.le
    simpa [← mul_assoc, hnx.ne', mul_comm] using this
  have hop : ‖f‖ ≤ f v := by
    apply f.opNorm_le_bound hfv
    intro x
    rw [Real.norm_eq_abs, abs_le]
    have hneg := hupper (-x)
    simp only [map_neg, norm_neg] at hneg
    exact ⟨by linarith, hupper x⟩
  refine ⟨v, hvnorm, le_antisymm ?_ hop⟩
  calc
    f v ≤ ‖f v‖ := le_abs_self _
    _ ≤ ‖f‖ * ‖v‖ := f.le_opNorm v
    _ ≤ ‖f‖ := by simpa using mul_le_mul_of_nonneg_left hvnorm (norm_nonneg f)

lemma aggregate_decomposition_of_support [FiniteDimensional ℝ E]
    (w t : E) (A B R : ℝ) (hR : 0 ≤ R)
    (hsupport : ∀ (f : E →L[ℝ] ℝ) (ε : ℝ), 0 < ε →
      ∃ z ∈ aggregateSet w A B, f t ≤ f z + R * ‖f‖ + ε) :
    ∃ rp rm : E, rp + rm = w ∧ ‖rp‖ ≤ A ∧ ‖rm‖ ≤ B ∧
      ‖t - (rp-rm)‖ ≤ R := by
  let S := aggregateSet w A B + closedBall (0 : E) R
  have hc : IsCompact S := (isCompact_aggregateSet w A B).add (isCompact_closedBall 0 R)
  have hv : Convex ℝ S := (convex_aggregateSet w A B).add (convex_closedBall 0 R)
  have ht : t ∈ S := by
    by_contra hnot
    obtain ⟨f, u, hsep, hut⟩ := geometric_hahn_banach_closed_point hv hc.isClosed hnot
    obtain ⟨z, hz, hfz⟩ := hsupport f ((f t - u) / 2) (by linarith)
    obtain ⟨v, hv, hfv⟩ := exists_unitBall_dual_maximizer f
    have hRv : R • v ∈ closedBall (0 : E) R := by
      simp only [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hR]
      simpa using mul_le_mul_of_nonneg_left hv hR
    have hmem : z + R • v ∈ S := Set.add_mem_add hz hRv
    have hh := hsep (z + R • v) hmem
    simp only [map_add, map_smul, smul_eq_mul, hfv] at hh
    linarith
  obtain ⟨z, ⟨rp, rm, hadd, hp, hm, rfl⟩, v, hv, he⟩ := Set.mem_add.mp ht
  refine ⟨rp, rm, hadd, hp, hm, ?_⟩
  have htv : t - (rp-rm) = v := by rw [← he]; abel
  simpa [htv] using hv

lemma median_of_aggregate_support [FiniteDimensional ℝ E] (x y : E)
    (hsupport : ∀ (f : E →L[ℝ] ℝ) (ε : ℝ), 0 < ε →
      ∃ z ∈ aggregateSet (x-y) ((‖x-y‖ + ‖x‖ - ‖y‖)/2)
        ((‖x-y‖ - ‖x‖ + ‖y‖)/2),
        f (x+y) ≤ f z + (‖x‖ + ‖y‖ - ‖x-y‖) * ‖f‖ + ε) :
    ∃ m : E, ‖x‖ = ‖m‖ + ‖x-m‖ ∧ ‖y‖ = ‖m‖ + ‖y-m‖ ∧
      ‖x-y‖ = ‖x-m‖ + ‖m-y‖ := by
  obtain ⟨rp, rm, hadd, hp, hm, hrem⟩ := aggregate_decomposition_of_support (x-y) (x+y)
    ((‖x-y‖ + ‖x‖ - ‖y‖)/2) ((‖x-y‖ - ‖x‖ + ‖y‖)/2)
    (‖x‖ + ‖y‖ - ‖x-y‖) (by linarith [norm_sub_le x y]) hsupport
  exact median_of_aggregate_decomposition x y rp rm hadd hp hm hrem

end

section
open Set Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma extreme_unit_scaled_norm_add {e u : E} {R : ℝ}
    (he : e ∈ (closedBall (0 : E) 1).extremePoints ℝ) (hne : ‖e‖ = 1)
    (hR : 0 < R) (hadd : ‖u‖ + ‖R • e - u‖ = R) : u = ‖u‖ • e := by
  have hden : ‖R⁻¹ • u‖ + ‖e - R⁻¹ • u‖ = 1 := by
    have hi : e - R⁻¹ • u = R⁻¹ • (R • e - u) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hR.ne', one_smul]
    rw [hi, norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR),
      ← mul_add, hadd, inv_mul_cancel₀ hR.ne']
  have h := extreme_unit_norm_add he hne hden
  have hh := congrArg (fun z : E => R • z) h
  simpa only [smul_smul, mul_inv_cancel₀ hR.ne', one_smul, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR), ← mul_assoc, one_mul] using hh

theorem extreme_unit_spear [Nontrivial E] (hmed : HasMetricMedians E)
    {e : E} (he : e ∈ (closedBall (0 : E) 1).extremePoints ℝ) (x : E) :
    max ‖x + e‖ ‖x - e‖ = ‖x‖ + 1 := by
  have hne : ‖e‖ = 1 := mem_sphere_zero_iff_norm.mp
    (extremePoints_closedBall_subset_sphere he)
  obtain ⟨m,hm⟩ := hmed ![0, (2:ℝ) • e, x+e]
  have h2 : ‖m‖ + ‖(2:ℝ) • e-m‖ = 2 := by
    have hh := hm 0 1 (by decide)
    simpa [dist_eq_norm, norm_sub_rev, norm_smul, hne] using hh.symm
  have hmx := extreme_unit_scaled_norm_add he hne (by norm_num : (0:ℝ)<2) h2
  have hxm : ‖x+e‖ = ‖m‖ + ‖x+e-m‖ := by
    have hh := hm 0 2 (by decide)
    change dist 0 (x+e) = dist 0 m + dist m (x+e) at hh
    simpa only [dist_eq_norm, zero_sub, norm_neg, norm_sub_rev m (x+e)] using hh
  have hym : ‖x-e‖ = 2 - ‖m‖ + ‖x+e-m‖ := by
    have hh := hm 1 2 (by decide)
    change dist ((2:ℝ) • e) (x+e) = dist ((2:ℝ) • e) m + dist m (x+e) at hh
    have heq : (2:ℝ) • e - (x+e) = -(x-e) := by module
    simp only [dist_eq_norm, heq, norm_neg, norm_sub_rev m (x+e)] at hh
    linarith
  have hbound : ‖x‖ ≤ |‖m‖-1| + ‖x+e-m‖ := by
    have heq : (‖m‖-1) • e = m-e := by rw [sub_smul, one_smul, ← hmx]
    calc
      ‖x‖ = ‖(‖m‖-1) • e + (x+e-m)‖ := by rw [heq]; congr 1; abel
      _ ≤ ‖(‖m‖-1) • e‖ + ‖x+e-m‖ := norm_add_le _ _
      _ = _ := by rw [norm_smul, Real.norm_eq_abs, hne, mul_one]
  apply le_antisymm
  · exact max_le (by simpa [hne] using norm_add_le x e)
      (by simpa [hne] using norm_sub_le x e)
  · rcases le_total 1 ‖m‖ with ht | ht
    · rw [abs_of_nonneg (by linarith)] at hbound
      exact (by linarith : ‖x‖+1 ≤ ‖x+e‖).trans (le_max_left _ _)
    · rw [abs_of_nonpos (by linarith)] at hbound
      exact (by linarith : ‖x‖+1 ≤ ‖x-e‖).trans (le_max_right _ _)

lemma dual_eval_le_unit_norm (f : E →L[ℝ] ℝ) (hf : ‖f‖ ≤ 1) (x : E) : f x ≤ ‖x‖ := by
  calc
    f x ≤ |f x| := le_abs_self _
    _ ≤ ‖f‖ * ‖x‖ := f.le_opNorm x
    _ ≤ ‖x‖ := by simpa using mul_le_mul_of_nonneg_right hf (norm_nonneg x)

theorem extreme_unit_dual_face_norming [Nontrivial E] (hmed : HasMetricMedians E)
    {e : E} (he : e ∈ (closedBall (0 : E) 1).extremePoints ℝ) (x : E) :
    ∃ f : E →L[ℝ] ℝ, ‖f‖ ≤ 1 ∧ f x = ‖x‖ ∧ (f e = 1 ∨ f e = -1) := by
  have hne : ‖e‖ = 1 := mem_sphere_zero_iff_norm.mp
    (extremePoints_closedBall_subset_sphere he)
  have hs := extreme_unit_spear hmed he x
  rcases le_total ‖x-e‖ ‖x+e‖ with hle | hle
  · rw [max_eq_left hle] at hs
    obtain ⟨f,hfn,hf⟩ := exists_dual_vector'' ℝ (x+e)
    have hx := dual_eval_le_unit_norm f hfn x
    have he' := dual_eval_le_unit_norm f hfn e
    rw [map_add, hs] at hf
    change f x + f e = ‖x‖ + 1 at hf
    rw [hne] at he'
    exact ⟨f,hfn,by linarith,Or.inl (by linarith)⟩
  · rw [max_eq_right hle] at hs
    obtain ⟨f,hfn,hf⟩ := exists_dual_vector'' ℝ (x-e)
    have hx := dual_eval_le_unit_norm f hfn x
    have he' := dual_eval_le_unit_norm f hfn (-e)
    rw [map_sub, hs] at hf
    change f x - f e = ‖x‖ + 1 at hf
    rw [map_neg, norm_neg, hne] at he'
    exact ⟨f,hfn,by linarith,Or.inr (by linarith)⟩

end

section
open Set Metric Finset
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure SignedUnitRepresentation (q : E) (a T : ℝ) where
  size : ℕ
  point : Fin size → E
  sign : Fin size → ℝ
  weight : Fin size → ℝ
  point_norm : ∀ i, ‖point i‖ ≤ 1
  sign_eq : ∀ i, sign i = 1 ∨ sign i = -1
  weight_nonneg : ∀ i, 0 ≤ weight i
  sum_point : ∑ i, weight i • point i = q
  sum_sign : ∑ i, weight i * sign i = a
  sum_weight : ∑ i, weight i = T

namespace SignedUnitRepresentation
variable {q : E} {a T : ℝ} (R : SignedUnitRepresentation q a T)

def plus : E := ∑ i, ((1 + R.sign i) / 2 * R.weight i) • R.point i

def minus : E := ∑ i, ((1 - R.sign i) / 2 * R.weight i) • R.point i

lemma plus_add_minus : R.plus + R.minus = q := by
  calc
    R.plus + R.minus = ∑ i, R.weight i • R.point i := by
      rw [plus, minus, ← sum_add_distrib]
      apply sum_congr rfl
      intro i hi
      rw [← add_smul]
      congr 1
      ring
    _ = q := R.sum_point

lemma plus_norm : ‖R.plus‖ ≤ (T+a)/2 := by
  calc
    _ ≤ ∑ i, ‖((1+R.sign i)/2*R.weight i) • R.point i‖ := norm_sum_le _ _
    _ ≤ ∑ i, (1+R.sign i)/2 * R.weight i := by
      apply sum_le_sum
      intro i hi
      have hc : 0 ≤ (1+R.sign i)/2 * R.weight i := by
        rcases R.sign_eq i with h | h <;> rw [h] <;> nlinarith [R.weight_nonneg i]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
      exact (mul_le_mul_of_nonneg_left (R.point_norm i) hc).trans_eq (mul_one _)
    _ = _ := by
      simp_rw [show ∀ i, (1+R.sign i)/2 * R.weight i =
        (R.weight i + R.weight i*R.sign i)/2 by intro i; ring]
      rw [← sum_div, sum_add_distrib, R.sum_weight, R.sum_sign]

lemma minus_norm : ‖R.minus‖ ≤ (T-a)/2 := by
  calc
    _ ≤ ∑ i, ‖((1-R.sign i)/2*R.weight i) • R.point i‖ := norm_sum_le _ _
    _ ≤ ∑ i, (1-R.sign i)/2 * R.weight i := by
      apply sum_le_sum
      intro i hi
      have hc : 0 ≤ (1-R.sign i)/2 * R.weight i := by
        rcases R.sign_eq i with h | h <;> rw [h] <;> nlinarith [R.weight_nonneg i]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
      exact (mul_le_mul_of_nonneg_left (R.point_norm i) hc).trans_eq (mul_one _)
    _ = _ := by
      simp_rw [show ∀ i, (1-R.sign i)/2 * R.weight i =
        (R.weight i - R.weight i*R.sign i)/2 by intro i; ring]
      rw [← sum_div, sum_sub_distrib, R.sum_weight, R.sum_sign]

lemma eval_difference (u : E →L[ℝ] ℝ) :
    u (R.plus - R.minus) = ∑ i, R.weight i * R.sign i * u (R.point i) := by
  simp only [plus, minus, map_sub, map_sum, map_smul, smul_eq_mul, ← sum_sub_distrib]
  apply sum_congr rfl
  intro i hi
  ring

lemma difference_mem : R.plus - R.minus ∈ aggregateSet q ((T+a)/2) ((T-a)/2) :=
  ⟨R.plus, R.minus, R.plus_add_minus, R.plus_norm, R.minus_norm, rfl⟩

end SignedUnitRepresentation

def HasEndpointScaling (ell : ℝ → ℝ) : Prop :=
  ∀ a b : ℝ, 0 < a → a ≤ b → ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < ell (1-δ) ∧
      ∀ c ∈ Icc a b, |ell (1-δ*c) / ell (1-δ) - c| ≤ ε

def liftedLensCost (ell : ℝ → ℝ) (u : E →L[ℝ] ℝ) (δ : ℝ) (b : E) (σ : ℝ) : ℝ :=
  ell (1-δ*(1-σ*u b))

def HasOptimalLiftRepresentations (ell : ℝ → ℝ) (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  ∀ u : E →L[ℝ] ℝ, ‖u‖ < 1 → ∀ δ : ℝ, 0 < δ → δ < 1 →
  ∀ q : E, ∀ a : ℝ, q ≠ 0 →
    ∃ R : SignedUnitRepresentation q a (max ‖q‖ |a|),
      ∀ T : ℝ, ∀ S : SignedUnitRepresentation q a T,
        (∑ i, R.weight i * liftedLensCost ell u δ (R.point i) (R.sign i)) ≤
          ∑ i, S.weight i * liftedLensCost ell u δ (S.point i) (S.sign i)

lemma endpoint_factor_mem {u : E →L[ℝ] ℝ} {b : E} {σ : ℝ}
    (hb : ‖b‖ ≤ 1) (hσ : σ = 1 ∨ σ = -1) :
    1-σ*u b ∈ Icc (1-‖u‖) (1+‖u‖) := by
  have hu : |u b| ≤ ‖u‖ := by
    exact (u.le_opNorm b).trans ((mul_le_mul_of_nonneg_left hb (norm_nonneg u)).trans_eq
      (mul_one _))
  rcases abs_le.mp hu with ⟨hl,hr⟩
  rcases hσ with rfl | rfl <;> constructor <;> linarith

namespace SignedUnitRepresentation
variable {q : E} {a T : ℝ} (R : SignedUnitRepresentation q a T)

def cost (ell : ℝ → ℝ) (u : E →L[ℝ] ℝ) (δ : ℝ) : ℝ :=
  ∑ i, R.weight i * liftedLensCost ell u δ (R.point i) (R.sign i)

lemma cost_error {ell : ℝ → ℝ} {u : E →L[ℝ] ℝ} {δ ε : ℝ}
    (herr : ∀ c ∈ Icc (1-‖u‖) (1+‖u‖),
        |ell (1-δ*c) / ell (1-δ) - c| ≤ ε) :
    |R.cost ell u δ / ell (1-δ) - (T-u (R.plus-R.minus))| ≤ T * ε := by
  have he : R.cost ell u δ / ell (1-δ) - (T-u (R.plus-R.minus)) =
      ∑ i, R.weight i * (liftedLensCost ell u δ (R.point i) (R.sign i) / ell (1-δ) -
        (1-R.sign i*u (R.point i))) := by
    have hc : T-u (R.plus-R.minus) = ∑ i, R.weight i *
        (1-R.sign i*u (R.point i)) := by
      rw [R.eval_difference]
      simp only [mul_sub, mul_one, ← mul_assoc, sum_sub_distrib, R.sum_weight]
    rw [hc, cost, sum_div, ← sum_sub_distrib]
    apply sum_congr rfl
    intro i hi
    ring
  rw [he]
  calc
    _ ≤ ∑ i, |R.weight i * (liftedLensCost ell u δ (R.point i) (R.sign i) / ell (1-δ) -
        (1-R.sign i*u (R.point i)))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, R.weight i * ε := by
      apply sum_le_sum
      intro i hi
      rw [abs_mul, abs_of_nonneg (R.weight_nonneg i)]
      exact mul_le_mul_of_nonneg_left
        (herr _ (endpoint_factor_mem (R.point_norm i) (R.sign_eq i))) (R.weight_nonneg i)
    _ = T*ε := by rw [← sum_mul, R.sum_weight]

end SignedUnitRepresentation

def medianCompetitor {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) :
    SignedUnitRepresentation (x-y) (‖x‖-‖y‖) (‖x‖+‖y‖) where
  size := 2
  point := ![‖x‖⁻¹ • x, -(‖y‖⁻¹ • y)]
  sign := ![1,-1]
  weight := ![‖x‖,‖y‖]
  point_norm := by
    intro i
    fin_cases i <;> simp [norm_smul, hx, hy]
  sign_eq := by intro i; fin_cases i <;> simp
  weight_nonneg := by intro i; fin_cases i <;> simp
  sum_point := by
    simp [Fin.sum_univ_two, smul_smul, hx, hy, sub_eq_add_neg]
  sum_sign := by simp [Fin.sum_univ_two, sub_eq_add_neg]
  sum_weight := by simp [Fin.sum_univ_two]

lemma medianCompetitor_difference {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) :
    (medianCompetitor hx hy).plus - (medianCompetitor hx hy).minus = x+y := by
  dsimp [SignedUnitRepresentation.plus, SignedUnitRepresentation.minus, medianCompetitor]
  simp [Fin.sum_univ_two, smul_smul, hx, hy]

lemma aggregate_support_interior_of_optimal
    {ell : ℝ → ℝ} (hell : HasEndpointScaling ell) (hopt : HasOptimalLiftRepresentations ell E)
    {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y)
    (u : E →L[ℝ] ℝ) (hu : ‖u‖ < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ z ∈ aggregateSet (x-y) ((‖x-y‖+‖x‖-‖y‖)/2) ((‖x-y‖-‖x‖+‖y‖)/2),
      u (x+y) ≤ u z + (‖x‖+‖y‖-‖x-y‖) + ε := by
  have hp : 0 < ‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hs : 0 < ‖x‖+‖y‖+‖x-y‖ := by positivity
  let η := ε / (‖x‖+‖y‖+‖x-y‖)
  obtain ⟨δ,hδ,hδ1,hellδ,herr⟩ := hell (1-‖u‖) (1+‖u‖)
    (by linarith) (by linarith [norm_nonneg u]) η (div_pos hε hs)
  have hmax : max ‖x-y‖ |‖x‖-‖y‖| = ‖x-y‖ :=
    max_eq_left (abs_norm_sub_norm_le x y)
  obtain ⟨R,hR⟩ := hopt u hu δ hδ hδ1 (x-y) (‖x‖-‖y‖) (sub_ne_zero.mpr hxy)
  have hcost := div_le_div_of_nonneg_right (hR _ (medianCompetitor hx hy)) hellδ.le
  have hrerr := (abs_le.mp (R.cost_error herr)).1
  have hserr := (abs_le.mp ((medianCompetitor hx hy).cost_error herr)).2
  rw [medianCompetitor_difference] at hserr
  change R.cost ell u δ / ell (1-δ) ≤ (medianCompetitor hx hy).cost ell u δ / ell (1-δ) at hcost
  have hz := R.difference_mem
  simp only [hmax] at hz hrerr
  refine ⟨R.plus-R.minus, ?_, ?_⟩
  · convert hz using 1 ; congr 2 <;> ring
  · have he : (‖x‖+‖y‖+‖x-y‖)*η = ε := mul_div_cancel₀ _ hs.ne'
    nlinarith

end

open Set Metric
variable {E : Type*} [NormedAddCommGroup E] [inst459 : NormedSpace ℝ E]

lemma aggregate_support_of_optimal
    {ell : ℝ → ℝ} (hell : HasEndpointScaling ell) (hopt : HasOptimalLiftRepresentations ell E)
    {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y)
    (f : E →L[ℝ] ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ z ∈ aggregateSet (x-y) ((‖x-y‖+‖x‖-‖y‖)/2) ((‖x-y‖-‖x‖+‖y‖)/2),
      f (x+y) ≤ f z + (‖x‖+‖y‖-‖x-y‖)*‖f‖ + ε := by
  let R := ‖x‖+‖y‖-‖x-y‖
  have hR : 0 ≤ R := sub_nonneg.mpr (norm_sub_le x y)
  let d := ε / (2*(R+1))
  have hd : 0 < d := div_pos hε (by positivity)
  have hd' : d*(R+1) = ε/2 := by dsimp [d]; field_simp
  let L := ‖f‖+d
  have hL : 0 < L := add_pos_of_nonneg_of_pos (norm_nonneg f) hd
  let u : E →L[ℝ] ℝ := L⁻¹ • f
  have hu : ‖u‖ < 1 := by
    rw [show ‖u‖ = L⁻¹ * ‖f‖ by simp [u, norm_smul, abs_of_pos hL]]
    rw [← div_eq_inv_mul]
    exact (div_lt_one hL).mpr (by dsimp [L]; linarith)
  let η := ε/(2*L)
  have hη : 0 < η := div_pos hε (by positivity)
  have hη' : L*η = ε/2 := by dsimp [η]; field_simp
  obtain ⟨z,hz,hbound⟩ := aggregate_support_interior_of_optimal hell hopt hx hy hxy u hu η hη
  have hev (v : E) : L*u v = f v := by simp [u, hL.ne']
  have hh : f (x+y) ≤ f z + L*R + ε/2 := by
    calc
      _ = L*u (x+y) := (hev _).symm
      _ ≤ L*(u z+R+η) := mul_le_mul_of_nonneg_left hbound hL.le
      _ = _ := by rw [mul_add, mul_add, hev, hη']
  refine ⟨z,hz,?_⟩
  dsimp only [L] at hh
  change f (x+y) ≤ f z + R*‖f‖ + ε
  nlinarith

theorem zero_median_of_optimal [FiniteDimensional ℝ E]
    {ell : ℝ → ℝ} (hell : HasEndpointScaling ell) (hopt : HasOptimalLiftRepresentations ell E)
    (x y : E) :
    ∃ m : E, ‖x‖ = ‖m‖+‖x-m‖ ∧ ‖y‖ = ‖m‖+‖y-m‖ ∧
      ‖x-y‖ = ‖x-m‖+‖m-y‖ := by
  by_cases hx : x = 0
  · subst x
    exact ⟨0, by simp⟩
  by_cases hy : y = 0
  · subst y
    exact ⟨0, by simp⟩
  by_cases hxy : x = y
  · subst y
    exact ⟨x, by simp⟩
  exact median_of_aggregate_support x y (aggregate_support_of_optimal hell hopt hx hy hxy)

omit inst459 in
lemma metricMedians_of_zero_medians [NormedSpace ℝ E]
    (h : ∀ x y : E, ∃ m : E, ‖x‖ = ‖m‖+‖x-m‖ ∧ ‖y‖ = ‖m‖+‖y-m‖ ∧
      ‖x-y‖ = ‖x-m‖+‖m-y‖) : HasMetricMedians E := by
  intro v
  obtain ⟨m,h1,h2,h12⟩ := h (v 1-v 0) (v 2-v 0)
  let M := m + v 0
  have h0 : ‖v 0-M‖ = ‖m‖ := by simp [M, show v 0-(m+v 0) = -m by abel]
  have hi (i : Fin 3) : v i-M = (v i-v 0)-m := by dsimp [M]; abel
  have he : (v 1-v 0)-(v 2-v 0) = v 1-v 2 := by abel
  have h01 : dist (v 0) (v 1) = dist (v 0) M + dist M (v 1) := by
    simpa only [dist_eq_norm, norm_sub_rev (v 0) (v 1), h0, norm_sub_rev M (v 1), hi, sub_self, zero_sub, norm_neg] using h1
  have h02 : dist (v 0) (v 2) = dist (v 0) M + dist M (v 2) := by
    simpa only [dist_eq_norm, norm_sub_rev (v 0) (v 2), h0, norm_sub_rev M (v 2), hi, sub_self, zero_sub, norm_neg] using h2
  have h1' : ‖m-(v 2-v 0)‖ = ‖M-v 2‖ := by congr 1; dsimp [M]; abel
  have h12' : dist (v 1) (v 2) = dist (v 1) M + dist M (v 2) := by
    simpa only [dist_eq_norm, hi, he, h1'] using h12
  have rev (a b : E) (h : dist a b = dist a M + dist M b) :
      dist b a = dist b M + dist M a := by
    calc
      dist b a = dist a b := dist_comm _ _
      _ = dist a M + dist M b := h
      _ = dist b M + dist M a := by rw [dist_comm a M, dist_comm M b, add_comm]
  refine ⟨M,?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals first
    | exact False.elim (hij rfl)
    | exact h01
    | exact h02
    | exact h12'
    | exact rev _ _ h01
    | exact rev _ _ h02
    | exact rev _ _ h12'

theorem metricMedians_of_optimal_lift [FiniteDimensional ℝ E]
    {ell : ℝ → ℝ} (hell : HasEndpointScaling ell) (hopt : HasOptimalLiftRepresentations ell E) :
    HasMetricMedians E := metricMedians_of_zero_medians (zero_median_of_optimal hell hopt)

end SymmetricMahler
end

end OAI
