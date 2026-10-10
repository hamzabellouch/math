import Mathlib
import OAI.Probability.LatticeSurface.Dynamics.ShiftData

namespace OAI

open Set MeasureTheory intervalIntegral

namespace FeasibleShift

variable {V : Type*} [Fintype V] [DecidableEq V]

@[simp] theorem mem_component (G : SimpleGraph V) (x y : V) :
    y ∈ component G x ↔ G.Reachable x y := by simp [component]

@[simp] theorem self_mem_component (G : SimpleGraph V) (x : V) :
    x ∈ component G x := by simp

theorem component_nonempty (G : SimpleGraph V) (x : V) :
    (component G x).Nonempty := ⟨x, self_mem_component G x⟩

theorem component_eq_of_reachable {G : SimpleGraph V} {x y : V}
    (hxy : G.Reachable x y) : component G x = component G y := by
  ext z
  simp only [mem_component]
  exact ⟨fun h => hxy.symm.trans h, fun h => hxy.trans h⟩

theorem component_mono {G H : SimpleGraph V} (hGH : G ≤ H) (x : V) :
    component G x ⊆ component H x := by
  intro y hy
  rw [mem_component] at hy ⊢
  exact hy.mono hGH

omit [Fintype V] [DecidableEq V] in
theorem contactGraph_le (G : SimpleGraph V) (h : V → ℝ) (s : ℝ) :
    contactGraph G h s ≤ G := fun _ _ hh => hh.1

omit [Fintype V] [DecidableEq V] in
theorem contactGraph_mono (G : SimpleGraph V) (h : V → ℝ) {s t : ℝ}
    (hst : s ≤ t) : contactGraph G h s ≤ contactGraph G h t :=
  fun _ _ hh => ⟨hh.1, hh.2.trans hst⟩

omit [Fintype V] [DecidableEq V] in
theorem walk_oscillation (G : SimpleGraph V) (f : V → ℝ) (L : ℝ)
    (hf : ∀ x y, G.Adj x y → |f x - f y| ≤ L)
    {x y : V} (p : G.Walk x y) : |f x - f y| ≤ L * p.length := by
  induction p with
  | nil => simp
  | @cons x y z hxy p ih =>
    calc
      |f x - f z| ≤ |f x - f y| + |f y - f z| := abs_sub_le _ _ _
      _ ≤ L + L * p.length := add_le_add (hf _ _ hxy) ih
      _ = L * (SimpleGraph.Walk.cons hxy p).length := by
        simp [SimpleGraph.Walk.length_cons]; ring

theorem walk_support_subset_component {G : SimpleGraph V} {x y : V}
    (p : G.Walk x y) : ∀ z ∈ p.support, z ∈ component G x := by
  induction p with
  | nil => simp
  | @cons x y z hxy p ih =>
    intro w hw
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact self_mem_component G _
    · exact (mem_component G x w).2 (hxy.reachable.trans ((mem_component G y w).1 (ih w hw)))

theorem component_oscillation (G : SimpleGraph V) (f : V → ℝ) (L : ℝ)
    (hL : 0 ≤ L) (hf : ∀ x y, G.Adj x y → |f x - f y| ≤ L)
    {x y : V} (hy : y ∈ component G x) :
    |f x - f y| ≤ L * (component G x).card := by
  classical
  have hxy := (mem_component G x y).1 hy
  apply hxy.elim_path
  intro p
  have hcard : p.val.length + 1 ≤ (component G x).card := by
    rw [← p.val.length_support, ← List.toFinset_card_of_nodup p.property.support_nodup]
    exact Finset.card_le_card (by
      intro z hz
      exact walk_support_subset_component p.val z (List.mem_toFinset.1 hz))
  exact (walk_oscillation G f L hf p.val).trans
    (mul_le_mul_of_nonneg_left (by exact_mod_cast (Nat.le_of_succ_le hcard)) hL)

theorem prescription_ground (G : SimpleGraph V) (ground : Finset V)
    (f : V → ℝ) {x : V} (hx : x ∈ ground) : prescription G ground f x = 0 := by
  classical
  have hn : ¬ Disjoint (component G x) ground := by
    intro hd
    exact Finset.disjoint_left.1 hd (self_mem_component G x) hx
  simp [prescription, hn]

theorem prescription_eq_of_reachable {G : SimpleGraph V} (ground : Finset V)
    (f : V → ℝ) {x y : V} (hxy : G.Reachable x y) :
    prescription G ground f x = prescription G ground f y := by
  simp only [prescription, component_eq_of_reachable hxy]

theorem prescription_bound (G : SimpleGraph V) (ground : Finset V)
    (f : V → ℝ) (M : ℝ) (hM : 0 ≤ M) (hf : ∀ x, |f x| ≤ M) (x : V) :
    |prescription G ground f x| ≤ M := by
  classical
  unfold prescription
  split_ifs with hd
  · have hc : (0 : ℝ) < (component G x).card := by
      exact_mod_cast (component_nonempty G x).card_pos
    rw [abs_div, abs_of_pos hc, div_le_iff₀ hc]
    calc
      |∑ y ∈ component G x, f y| ≤ ∑ y ∈ component G x, |f y| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ y ∈ component G x, M := Finset.sum_le_sum fun _ _ => hf _
      _ = M * (component G x).card := by simp; ring
  · simpa using hM

theorem prescription_approximation (G : SimpleGraph V) (ground : Finset V)
    (f : V → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hfground : ∀ x ∈ ground, f x = 0)
    (hf : ∀ x y, G.Adj x y → |f x - f y| ≤ L) (x : V) :
    |prescription G ground f x - f x| ≤ L * (component G x).card := by
  classical
  unfold prescription
  split_ifs with hd
  · have hc : (0 : ℝ) < (component G x).card := by
      exact_mod_cast (component_nonempty G x).card_pos
    rw [div_sub' hc.ne', abs_div, abs_of_pos hc, div_le_iff₀ hc]
    have heq : (∑ y ∈ component G x, f y) - (component G x).card * f x =
        ∑ y ∈ component G x, (f y - f x) := by simp [Finset.sum_sub_distrib]
    rw [heq]
    calc
      |∑ y ∈ component G x, (f y - f x)| ≤ ∑ y ∈ component G x, |f y - f x| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ y ∈ component G x, L * (component G x).card :=
        Finset.sum_le_sum fun y hy => by
          rw [abs_sub_comm]
          exact component_oscillation G f L hL hf hy
      _ = L * (component G x).card * (component G x).card := by simp; ring
  · have hex : ∃ y ∈ component G x, y ∈ ground := by
      simpa [Finset.disjoint_left] using hd
    obtain ⟨y, hy, hyg⟩ := hex
    simpa [hfground y hyg, abs_sub_comm] using component_oscillation G f L hL hf hy

omit [DecidableEq V] in
theorem measurableSet_contactGraph_fiber (G H : SimpleGraph V) (h : V → ℝ) :
    MeasurableSet {s : ℝ | contactGraph G h s = H} := by
  classical
  have heq : {s : ℝ | contactGraph G h s = H} =
      {s : ℝ | ∀ x y, (G.Adj x y ∧ 1 - |h x - h y| ≤ s) ↔ H.Adj x y} := by
    ext s
    exact ⟨fun hh x y => by rw [← hh]; rfl,
      fun hh => SimpleGraph.ext (by funext x y; exact propext (hh x y))⟩
  rw [heq]
  simp_rw [ofPred_forall]
  apply MeasurableSet.iInter
  intro x
  apply MeasurableSet.iInter
  intro y
  by_cases hg : G.Adj x y <;> by_cases hh : H.Adj x y <;> simp only [hg, hh,
    true_and, false_and, iff_true, iff_false, not_le]
  · exact measurableSet_Ici
  · exact measurableSet_Iio
  · exact MeasurableSet.empty
  · exact MeasurableSet.univ

theorem measurable_prescription (G : SimpleGraph V) (ground : Finset V)
    (f h : V → ℝ) (x : V) :
    Measurable (fun s : ℝ => prescription (contactGraph G h s) ground f x) := by
  classical
  have heq : (fun s : ℝ => prescription (contactGraph G h s) ground f x) =
      fun s => ∑ H : SimpleGraph V, if contactGraph G h s = H then
        prescription H ground f x else 0 := by
    funext s
    simp
  rw [heq]
  apply Finset.measurable_sum
  intro H _
  exact Measurable.ite (measurableSet_contactGraph_fiber G H h) measurable_const measurable_const

theorem intervalIntegrable_prescription (G : SimpleGraph V) (ground : Finset V)
    (f h : V → ℝ) (s₀ s₁ : ℝ) (x : V) :
    IntervalIntegrable (fun s : ℝ => prescription (contactGraph G h s) ground f x)
      volume s₀ s₁ := by
  have hm := (measurable_prescription G ground f h x).aestronglyMeasurable (μ := volume)
  have hbound : ∀ s : ℝ, |prescription (contactGraph G h s) ground f x| ≤ ∑ y, |f y| :=
    fun s => prescription_bound (contactGraph G h s) ground f (∑ y : V, |f y|)
      (Finset.sum_nonneg fun y _ => abs_nonneg (f y)) (fun y =>
      Finset.single_le_sum (fun z _ => abs_nonneg (f z)) (Finset.mem_univ y)) x
  rw [intervalIntegrable_iff]
  exact Measure.integrableOn_of_bounded (by simp [Real.volume_uIoc]) hm
    (Filter.Eventually.of_forall fun s => by simpa [Real.norm_eq_abs] using hbound s)

theorem averagedShift_sub (G : SimpleGraph V) (ground : Finset V)
    (f h : V → ℝ) {s₀ s₁ : ℝ} (hs : s₀ < s₁) (x : V) :
    averagedShift G ground f h s₀ s₁ x - f x =
      (s₁ - s₀)⁻¹ * ∫ s in s₀..s₁, (prescription (contactGraph G h s) ground f x - f x) := by
  rw [intervalIntegral.integral_sub (intervalIntegrable_prescription G ground f h s₀ s₁ x)
    intervalIntegrable_const, intervalIntegral.integral_const]
  unfold averagedShift
  simp only [smul_eq_mul]
  field_simp [ne_of_gt (sub_pos.mpr hs)]

theorem averagedShift_approximation (G : SimpleGraph V) (ground : Finset V)
    (f h : V → ℝ) (s₀ s₁ s₂ L : ℝ) (hs : s₀ < s₁) (hss : s₁ ≤ s₂)
    (hL : 0 ≤ L) (hfground : ∀ x ∈ ground, f x = 0)
    (hfl : ∀ x y, G.Adj x y → |f x - f y| ≤ L) (x : V) :
    |averagedShift G ground f h s₀ s₁ x - f x| ≤
      L * (component (contactGraph G h s₂) x).card := by
  have hd : 0 < s₁ - s₀ := sub_pos.mpr hs
  rw [averagedShift_sub G ground f h hs x, abs_mul, abs_of_pos (inv_pos.mpr hd)]
  have hb : |∫ s in s₀..s₁, (prescription (contactGraph G h s) ground f x - f x)| ≤
      (L * (component (contactGraph G h s₂) x).card) * (s₁ - s₀) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := s₀) (b := s₁)
      (C := L * (component (contactGraph G h s₂) x).card)
      (f := fun s => prescription (contactGraph G h s) ground f x - f x) (fun s hsm => by
        rw [Real.norm_eq_abs]
        have hle : s ≤ s₂ := ((uIoc_of_le hs.le ▸ hsm).2).trans hss
        exact (prescription_approximation (contactGraph G h s) ground f L hL hfground
          (fun y z hyz => hfl y z hyz.1) x).trans
          (mul_le_mul_of_nonneg_left (by exact_mod_cast (Finset.card_le_card
            (component_mono (contactGraph_mono G h hle) x))) hL))
    simpa only [Real.norm_eq_abs, abs_of_pos hd] using h
  calc
    _ ≤ (s₁ - s₀)⁻¹ * ((L * (component (contactGraph G h s₂) x).card) * (s₁ - s₀)) :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hd.le)
    _ = _ := by field_simp [hd.ne']

theorem averagedShift_bound (G : SimpleGraph V) (ground : Finset V) (f h : V → ℝ)
    (s₀ s₁ M : ℝ) (hs : s₀ < s₁) (hM : 0 ≤ M) (hfb : ∀ x, |f x| ≤ M) (x : V) :
    |averagedShift G ground f h s₀ s₁ x| ≤ M := by
  have hd : 0 < s₁ - s₀ := sub_pos.mpr hs
  unfold averagedShift
  rw [abs_mul, abs_of_pos (inv_pos.mpr hd)]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := s₀) (b := s₁)
    (f := fun s => prescription (contactGraph G h s) ground f x)
    (fun s _ => by simpa only [Real.norm_eq_abs] using
      prescription_bound (contactGraph G h s) ground f M hM hfb x)
  rw [Real.norm_eq_abs, abs_of_pos hd] at hb
  calc
    _ ≤ (s₁ - s₀)⁻¹ * (M * (s₁ - s₀)) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hd.le)
    _ = M := by field_simp [hd.ne']

theorem averagedShift_ground (G : SimpleGraph V) (ground : Finset V) (f h : V → ℝ)
    (s₀ s₁ : ℝ) {x : V} (hx : x ∈ ground) : averagedShift G ground f h s₀ s₁ x = 0 := by
  simp [averagedShift, prescription_ground _ _ _ hx]

theorem averagedShift_tangent (G : SimpleGraph V) (ground : Finset V) (f h : V → ℝ)
    {s₀ s₁ : ℝ} (hs : s₀ ≤ s₁) {x y : V} (hxy : G.Adj x y)
    (hst : 1 - |h x - h y| ≤ s₀) :
    averagedShift G ground f h s₀ s₁ x = averagedShift G ground f h s₀ s₁ y := by
  unfold averagedShift
  congr 1
  apply intervalIntegral.integral_congr
  intro s hsm
  have hle : s₀ ≤ s := (uIcc_of_le hs ▸ hsm).1
  exact prescription_eq_of_reachable ground f
    (SimpleGraph.Adj.reachable (G := contactGraph G h s) ⟨hxy, hst.trans hle⟩)

theorem averaged_shift_approximation
    (G : SimpleGraph V) (ground : Finset V) (f h : V → ℝ)
    (s₀ s₁ s₂ L M : ℝ) (hs : s₀ < s₁) (hss : s₁ < s₂)
    (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hfground : ∀ x ∈ ground, f x = 0)
    (hfl : ∀ x y, G.Adj x y → |f x - f y| ≤ L)
    (hfb : ∀ x, |f x| ≤ M) :
    (∀ x, |averagedShift G ground f h s₀ s₁ x - f x| ≤
      L * (component (contactGraph G h s₂) x).card) ∧
    (∀ x, |averagedShift G ground f h s₀ s₁ x| ≤ M) ∧
    (∀ x ∈ ground, averagedShift G ground f h s₀ s₁ x = 0) ∧
    (∀ x y, G.Adj x y → 1 - |h x - h y| ≤ s₀ →
      averagedShift G ground f h s₀ s₁ x = averagedShift G ground f h s₀ s₁ y) := by
  exact ⟨averagedShift_approximation G ground f h s₀ s₁ s₂ L hs hss.le hL hfground hfl,
    averagedShift_bound G ground f h s₀ s₁ M hs hM hfb,
    fun _ hx => averagedShift_ground G ground f h s₀ s₁ hx,
    fun _ _ hxy hst => averagedShift_tangent G ground f h hs.le hxy hst⟩

noncomputable def betweenIndicator (a b : ℝ) (s : ℝ) : ℝ :=
  (uIcc a b).indicator (fun _ => 1) s

theorem betweenIndicator_nonneg (a b s : ℝ) : 0 ≤ betweenIndicator a b s := by
  classical
  by_cases hs : s ∈ uIcc a b <;> simp [betweenIndicator, hs]

theorem integrable_betweenIndicator (a b : ℝ) : Integrable (betweenIndicator a b) := by
  apply (integrableOn_const (s := uIcc a b) (C := (1 : ℝ)) (by simp)).integrable_indicator
    measurableSet_uIcc

theorem integral_betweenIndicator_le (a b s₀ s₁ : ℝ) (hs : s₀ ≤ s₁) :
    (∫ s in s₀..s₁, betweenIndicator a b s) ≤ |b - a| := by
  rw [intervalIntegral.integral_of_le hs]
  calc
    _ ≤ ∫ s, betweenIndicator a b s := setIntegral_le_integral
      (integrable_betweenIndicator a b) (Filter.Eventually.of_forall (betweenIndicator_nonneg a b))
    _ = |b - a| := by
      unfold betweenIndicator
      rw [MeasureTheory.integral_indicator_const (1 : ℝ) measurableSet_uIcc]
      simp

theorem integral_edge_change_bound {ι : Type*} (S : Finset ι) (a b : ι → ℝ)
    (F : ℝ → ℝ) (B s₀ s₁ : ℝ) (hB : 0 ≤ B) (hs : s₀ ≤ s₁)
    (hbound : ∀ s ∈ Icc s₀ s₁, |F s| ≤ B)
    (hzero : ∀ s ∈ Icc s₀ s₁, (∀ i ∈ S, s ∉ uIcc (a i) (b i)) → F s = 0) :
    |∫ s in s₀..s₁, F s| ≤ B * ∑ i ∈ S, |b i - a i| := by
  classical
  have hi (i : ι) : IntervalIntegrable (betweenIndicator (a i) (b i)) volume s₀ s₁ :=
    (integrable_betweenIndicator _ _).intervalIntegrable
  have hdom (s : ℝ) (hsm : s ∈ Icc s₀ s₁) :
      |F s| ≤ B * ∑ i ∈ S, betweenIndicator (a i) (b i) s := by
    by_cases hz : ∀ i ∈ S, s ∉ uIcc (a i) (b i)
    · rw [hzero s hsm hz, abs_zero]
      exact mul_nonneg hB (Finset.sum_nonneg fun i _ => betweenIndicator_nonneg _ _ s)
    · push Not at hz
      obtain ⟨i, hiS, him⟩ := hz
      have hone : (1 : ℝ) ≤ ∑ i ∈ S, betweenIndicator (a i) (b i) s := by
        calc
          _ = betweenIndicator (a i) (b i) s := by simp [betweenIndicator, him]
          _ ≤ _ := Finset.single_le_sum (fun j _ => betweenIndicator_nonneg _ _ s) hiS
      exact (hbound s hsm).trans (by nlinarith)
  have hint : IntervalIntegrable (fun s => B * ∑ i ∈ S, betweenIndicator (a i) (b i) s)
      volume s₀ s₁ := by
    simpa only [Finset.sum_apply] using (IntervalIntegrable.sum S (fun i _ => hi i)).const_mul B
  have hn := intervalIntegral.norm_integral_le_of_norm_le (f := F) hs
    (Filter.Eventually.of_forall fun s hsm => by
      simpa only [Real.norm_eq_abs] using hdom s (Ioc_subset_Icc_self hsm)) hint
  rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum (fun i _ => hi i)] at hn
  exact hn.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ =>
    integral_betweenIndicator_le _ _ _ _ hs) hB)

theorem le_iff_of_not_mem_uIcc {a b s : ℝ} (hs : s ∉ uIcc a b) : a ≤ s ↔ b ≤ s := by
  constructor
  · intro ha
    by_contra hb
    exact hs (mem_uIcc_of_le ha (le_of_not_ge hb))
  · intro hb
    by_contra ha
    exact hs (mem_uIcc_of_ge hb (le_of_not_ge ha))

noncomputable def edgeThreshold (h : V → ℝ) (e : V × V) : ℝ :=
  1 - |h e.1 - h e.2|

omit [DecidableEq V] in
theorem edgeThreshold_difference (h k : V → ℝ) (e : V × V) :
    |edgeThreshold k e - edgeThreshold h e| ≤ 2 * ‖h - k‖ := by
  have hx : |h e.1 - k e.1| ≤ ‖h - k‖ := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using norm_le_pi_norm (h - k) e.1
  have hy : |h e.2 - k e.2| ≤ ‖h - k‖ := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using norm_le_pi_norm (h - k) e.2
  calc
    _ = |(|h e.1 - h e.2|) - (|k e.1 - k e.2|)| := by unfold edgeThreshold; congr 1; ring
    _ ≤ |(h e.1 - h e.2) - (k e.1 - k e.2)| := abs_abs_sub_abs_le _ _
    _ = |(h e.1 - k e.1) - (h e.2 - k e.2)| := by congr 1; ring
    _ ≤ |h e.1 - k e.1| + |h e.2 - k e.2| := abs_sub _ _
    _ ≤ 2 * ‖h - k‖ := by linarith

theorem averagedShift_difference (G : SimpleGraph V) (ground : Finset V)
    (f h k : V → ℝ) (s₀ s₁ : ℝ) (x : V) :
    averagedShift G ground f h s₀ s₁ x - averagedShift G ground f k s₀ s₁ x =
      (s₁ - s₀)⁻¹ * ∫ s in s₀..s₁,
        (prescription (contactGraph G h s) ground f x - prescription (contactGraph G k s) ground f x) := by
  rw [intervalIntegral.integral_sub (intervalIntegrable_prescription G ground f h s₀ s₁ x)
    (intervalIntegrable_prescription G ground f k s₀ s₁ x)]
  unfold averagedShift
  ring

theorem averagedShift_global_difference (G : SimpleGraph V) (ground : Finset V)
    (f h k : V → ℝ) (s₀ s₁ M : ℝ) (hs : s₀ < s₁) (hM : 0 ≤ M)
    (hfb : ∀ x, |f x| ≤ M) (x : V) :
    |averagedShift G ground f h s₀ s₁ x - averagedShift G ground f k s₀ s₁ x| ≤
      ((s₁ - s₀)⁻¹ * (4 * M * Fintype.card (V × V))) * ‖h - k‖ := by
  classical
  have hd : 0 < s₁ - s₀ := sub_pos.mpr hs
  rw [averagedShift_difference G ground f h k s₀ s₁ x, abs_mul, abs_of_pos (inv_pos.mpr hd)]
  have hb := integral_edge_change_bound (Finset.univ : Finset (V × V))
    (edgeThreshold h) (edgeThreshold k)
    (fun s => prescription (contactGraph G h s) ground f x -
      prescription (contactGraph G k s) ground f x) (2 * M) s₀ s₁ (by positivity) hs.le
    (fun s _ => (abs_sub _ _).trans (by
      have h1 := prescription_bound (contactGraph G h s) ground f M hM hfb x
      have h2 := prescription_bound (contactGraph G k s) ground f M hM hfb x
      linarith))
    (fun s _ hstatus => by
      have heq : contactGraph G h s = contactGraph G k s := by
        ext y z
        exact and_congr_right (fun _ => le_iff_of_not_mem_uIcc (hstatus (y, z) (Finset.mem_univ _)))
      rw [heq, sub_self])
  have hsum : (∑ e : V × V, |edgeThreshold k e - edgeThreshold h e|) ≤
      Fintype.card (V × V) * (2 * ‖h - k‖) := by
    calc
      _ ≤ ∑ e : V × V, 2 * ‖h - k‖ := Finset.sum_le_sum fun e _ => edgeThreshold_difference h k e
      _ = _ := by simp
  calc
    _ ≤ (s₁ - s₀)⁻¹ * (2 * M * ∑ e : V × V, |edgeThreshold k e - edgeThreshold h e|) :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hd.le)
    _ ≤ (s₁ - s₀)⁻¹ * (2 * M * (Fintype.card (V × V) * (2 * ‖h - k‖))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum (by positivity)) (by positivity)
    _ = _ := by ring

theorem averagedShift_lipschitz (G : SimpleGraph V) (ground : Finset V)
    (f : V → ℝ) (s₀ s₁ M : ℝ) (hs : s₀ < s₁) (hM : 0 ≤ M)
    (hfb : ∀ x, |f x| ≤ M) :
    LipschitzWith ⟨(s₁ - s₀)⁻¹ * (4 * M * Fintype.card (V × V)), by positivity⟩
      (fun h : V → ℝ => averagedShift G ground f h s₀ s₁) := by
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro h k
  change ‖averagedShift G ground f h s₀ s₁ - averagedShift G ground f k s₀ s₁‖ ≤
    ((s₁ - s₀)⁻¹ * (4 * M * Fintype.card (V × V))) * ‖h - k‖
  have hd : 0 < s₁ - s₀ := sub_pos.mpr hs
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro x
  simpa only [Real.norm_eq_abs, Pi.sub_apply] using
    averagedShift_global_difference G ground f h k s₀ s₁ M hs hM hfb x

theorem reachable_of_agree_on_component {H K J : SimpleGraph V} (hHJ : H ≤ J)
    (x : V) (hag : ∀ y ∈ component J x, ∀ z ∈ component J x, H.Adj y z → K.Adj y z)
    {y z : V} (hy : y ∈ component J x) (hyz : H.Reachable y z) : K.Reachable y z := by
  obtain ⟨p⟩ := hyz
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons y w z hyw p ih =>
    have hw : w ∈ component J x := (mem_component J x w).2
      (((mem_component J x y).1 hy).trans (hHJ hyw).reachable)
    exact (hag y hy w hw hyw).reachable.trans (ih hw)

theorem component_eq_of_agree {H K J : SimpleGraph V} (hHJ : H ≤ J) (hKJ : K ≤ J)
    (x : V) (hag : ∀ y ∈ component J x, ∀ z ∈ component J x, H.Adj y z ↔ K.Adj y z) :
    component H x = component K x := by
  ext y
  simp only [mem_component]
  exact ⟨reachable_of_agree_on_component hHJ x (fun y hy z hz => (hag y hy z hz).mp)
      (self_mem_component J x),
    reachable_of_agree_on_component hKJ x (fun y hy z hz => (hag y hy z hz).mpr)
      (self_mem_component J x)⟩

noncomputable def componentEdges (G J : SimpleGraph V) (x : V) : Finset (V × V) := by
  classical
  exact ((component J x).product (component J x)).filter (fun e => G.Adj e.1 e.2)

@[simp] theorem mem_componentEdges (G J : SimpleGraph V) (x : V) (e : V × V) :
    e ∈ componentEdges G J x ↔ e.1 ∈ component J x ∧ e.2 ∈ component J x ∧ G.Adj e.1 e.2 := by
  classical
  simp [componentEdges, and_assoc]

theorem averagedShift_component_difference (G J : SimpleGraph V) (ground : Finset V)
    (f h k : V → ℝ) (s₀ s₁ L : ℝ) (hs : s₀ < s₁) (hL : 0 ≤ L)
    (hfground : ∀ x ∈ ground, f x = 0)
    (hfl : ∀ x y, G.Adj x y → |f x - f y| ≤ L)
    (hhJ : contactGraph G h s₁ ≤ J) (hkJ : contactGraph G k s₁ ≤ J) (x : V) :
    |averagedShift G ground f h s₀ s₁ x - averagedShift G ground f k s₀ s₁ x| ≤
      (s₁ - s₀)⁻¹ * (2 * L * (component J x).card *
        ∑ e ∈ componentEdges G J x, |edgeThreshold k e - edgeThreshold h e|) := by
  classical
  have hd : 0 < s₁ - s₀ := sub_pos.mpr hs
  rw [averagedShift_difference G ground f h k s₀ s₁ x, abs_mul, abs_of_pos (inv_pos.mpr hd)]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hd.le)
  apply integral_edge_change_bound _ _ _ _ _ _ _ (by positivity) hs.le
  · intro s hsm
    have ha (q : V → ℝ) (hq : contactGraph G q s₁ ≤ J) :
        |prescription (contactGraph G q s) ground f x - f x| ≤ L * (component J x).card := by
      exact (prescription_approximation (contactGraph G q s) ground f L hL hfground
        (fun y z hyz => hfl y z hyz.1) x).trans (mul_le_mul_of_nonneg_left
        (by exact_mod_cast (Finset.card_le_card (component_mono
          ((contactGraph_mono G q hsm.2).trans hq) x))) hL)
    calc
      _ ≤ |prescription (contactGraph G h s) ground f x - f x| +
          |f x - prescription (contactGraph G k s) ground f x| := abs_sub_le _ _ _
      _ = |prescription (contactGraph G h s) ground f x - f x| +
          |prescription (contactGraph G k s) ground f x - f x| := by rw [abs_sub_comm (f x)]
      _ ≤ 2 * L * (component J x).card := by linarith [ha h hhJ, ha k hkJ]
  · intro s hsm hstatus
    have heq : component (contactGraph G h s) x = component (contactGraph G k s) x := by
      apply component_eq_of_agree ((contactGraph_mono G h hsm.2).trans hhJ)
        ((contactGraph_mono G k hsm.2).trans hkJ) x
      intro y hy z hz
      by_cases hg : G.Adj y z
      · exact and_congr_right (fun _ => le_iff_of_not_mem_uIcc
          (hstatus (y, z) (by simp [hy, hz, hg])))
      · simp [contactGraph, hg]
    simp only [prescription, heq, sub_self]

omit [DecidableEq V] in
@[simp] theorem mem_neighbors (G : SimpleGraph V) (x y : V) : y ∈ neighbors G x ↔ G.Adj x y := by
  classical
  simp [neighbors]

theorem componentEdges_card_le (G J : SimpleGraph V) (D : ℕ)
    (hD : ∀ x, (neighbors G x).card ≤ D) (x : V) :
    (componentEdges G J x).card ≤ (component J x).card * D := by
  classical
  calc
    _ ≤ ((component J x).biUnion fun y => (neighbors G y).image (fun z => (y, z))).card := by
      apply Finset.card_le_card
      intro e he
      obtain ⟨hy, hz, he⟩ := (mem_componentEdges G J x e).1 he
      exact Finset.mem_biUnion.2 ⟨e.1, hy, Finset.mem_image.2 ⟨e.2, by simpa, rfl⟩⟩
    _ ≤ _ := Finset.card_biUnion_le_card_mul _ _ _ (fun y _ =>
      (Finset.card_image_le).trans (hD y))

theorem averagedShift_component_lipschitz_bound (G J : SimpleGraph V)
    (ground : Finset V) (f h k : V → ℝ) (s₀ s₁ L : ℝ) (D : ℕ)
    (hs : s₀ < s₁) (hL : 0 ≤ L)
    (hfground : ∀ x ∈ ground, f x = 0)
    (hfl : ∀ x y, G.Adj x y → |f x - f y| ≤ L)
    (hD : ∀ x, (neighbors G x).card ≤ D)
    (hhJ : contactGraph G h s₁ ≤ J) (hkJ : contactGraph G k s₁ ≤ J) (x : V) :
    |averagedShift G ground f h s₀ s₁ x - averagedShift G ground f k s₀ s₁ x| ≤
      ((s₁ - s₀)⁻¹ * (4 * D * L) * (component J x).card ^ 2) * ‖h - k‖ := by
  classical
  have hd : 0 < s₁ - s₀ := sub_pos.mpr hs
  have hsum : (∑ e ∈ componentEdges G J x, |edgeThreshold k e - edgeThreshold h e|) ≤
      ((component J x).card * D : ℝ) * (2 * ‖h - k‖) := by
    calc
      _ ≤ ∑ e ∈ componentEdges G J x, 2 * ‖h - k‖ :=
        Finset.sum_le_sum fun e _ => edgeThreshold_difference h k e
      _ = ((componentEdges G J x).card : ℝ) * (2 * ‖h - k‖) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast componentEdges_card_le G J D hD x)
        (by positivity)
  calc
    _ ≤ (s₁ - s₀)⁻¹ * (2 * L * (component J x).card *
        ∑ e ∈ componentEdges G J x, |edgeThreshold k e - edgeThreshold h e|) :=
      averagedShift_component_difference G J ground f h k s₀ s₁ L hs hL hfground hfl hhJ hkJ x
    _ ≤ (s₁ - s₀)⁻¹ * (2 * L * (component J x).card *
        (((component J x).card * D : ℝ) * (2 * ‖h - k‖))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum (by positivity)) (by positivity)
    _ = _ := by ring

omit [DecidableEq V] in
theorem contactGraph_le_of_distance (G : SimpleGraph V) (h k : V → ℝ) {s t : ℝ}
    (hst : s + 2 * ‖h - k‖ ≤ t) : contactGraph G k s ≤ contactGraph G h t := by
  intro x y hxy
  refine ⟨hxy.1, ?_⟩
  have hd := (abs_le.mp (edgeThreshold_difference h k (x, y))).1
  dsimp [edgeThreshold] at hd
  linarith [hxy.2]

theorem averagedShift_feasible (G : SimpleGraph V) (ground : Finset V)
    (f h : V → ℝ) (s₀ s₁ s₂ L B : ℝ) (hs : s₀ < s₁) (hss : s₁ ≤ s₂)
    (hL : 0 ≤ L) (hfground : ∀ x ∈ ground, f x = 0)
    (hfl : ∀ x y, G.Adj x y → |f x - f y| ≤ L)
    (hgood : ∀ x, ((component (contactGraph G h s₂) x).card : ℝ) ≤ B)
    (hsmall : L * (2 * B + 1) ≤ s₀)
    (hfeasible : ∀ x y, G.Adj x y → |h x - h y| ≤ 1) :
    ∀ x y, G.Adj x y →
      |(h x + averagedShift G ground f h s₀ s₁ x) -
        (h y + averagedShift G ground f h s₀ s₁ y)| ≤ 1 := by
  intro x y hxy
  by_cases ht : 1 - |h x - h y| ≤ s₀
  · rw [averagedShift_tangent G ground f h hs.le hxy ht, add_sub_add_right_eq_sub]
    exact hfeasible x y hxy
  · have he (z : V) : |averagedShift G ground f h s₀ s₁ z - f z| ≤ L * B :=
      (averagedShift_approximation G ground f h s₀ s₁ s₂ L hs hss hL hfground hfl z).trans
        (mul_le_mul_of_nonneg_left (hgood z) hL)
    have hu : |averagedShift G ground f h s₀ s₁ x - averagedShift G ground f h s₀ s₁ y| ≤
        L * (2 * B + 1) := by
      calc
        _ ≤ |averagedShift G ground f h s₀ s₁ x - f x| + |f x - f y| +
            |f y - averagedShift G ground f h s₀ s₁ y| := by
              linarith [abs_sub_le (averagedShift G ground f h s₀ s₁ x) (f x)
                (averagedShift G ground f h s₀ s₁ y),
                abs_sub_le (f x) (f y) (averagedShift G ground f h s₀ s₁ y)]
        _ ≤ _ := by rw [abs_sub_comm (f y)]; linarith [he x, he y, hfl x y hxy]
    calc
      _ = |(h x - h y) + (averagedShift G ground f h s₀ s₁ x -
          averagedShift G ground f h s₀ s₁ y)| := by congr 1; ring
      _ ≤ |h x - h y| + |averagedShift G ground f h s₀ s₁ x -
          averagedShift G ground f h s₀ s₁ y| := abs_add_le _ _
      _ ≤ 1 := by linarith

theorem averagedShift_injective_good (G : SimpleGraph V) (ground : Finset V)
    (f : V → ℝ) (s₀ s₁ s₂ L B : ℝ) (D : ℕ) (hs : s₀ < s₁) (hss : s₁ ≤ s₂)
    (hL : 0 ≤ L) (hB : 0 ≤ B) (hfground : ∀ x ∈ ground, f x = 0)
    (hfl : ∀ x y, G.Adj x y → |f x - f y| ≤ L)
    (hD : ∀ x, (neighbors G x).card ≤ D)
    (hbuffer : s₁ + 4 * L * B ≤ s₂)
    (hsmall : (s₁ - s₀)⁻¹ * (4 * D * L) * B ^ 2 < 1) :
    Set.InjOn (fun h : V → ℝ => h + averagedShift G ground f h s₀ s₁)
      {h | ∀ x, ((component (contactGraph G h s₂) x).card : ℝ) ≤ B} := by
  intro h hh k hk hcollision
  have hd : 0 < s₁ - s₀ := sub_pos.mpr hs
  have he (q : V → ℝ) (hq : ∀ x, ((component (contactGraph G q s₂) x).card : ℝ) ≤ B) (x : V) :
      |averagedShift G ground f q s₀ s₁ x - f x| ≤ L * B :=
    (averagedShift_approximation G ground f q s₀ s₁ s₂ L hs hss hL hfground hfl x).trans
      (mul_le_mul_of_nonneg_left (hq x) hL)
  have hnorm : ‖h - k‖ ≤ 2 * L * B := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro x
    have hc := congrFun hcollision x
    change h x + averagedShift G ground f h s₀ s₁ x = k x + averagedShift G ground f k s₀ s₁ x at hc
    have hx : |h x - k x| = |averagedShift G ground f k s₀ s₁ x -
        averagedShift G ground f h s₀ s₁ x| := by congr 1; linarith
    simp only [Pi.sub_apply, Real.norm_eq_abs]
    rw [hx]
    calc
      _ ≤ |averagedShift G ground f k s₀ s₁ x - f x| +
          |f x - averagedShift G ground f h s₀ s₁ x| := abs_sub_le _ _ _
      _ ≤ _ := by rw [abs_sub_comm (f x)]; linarith [he h hh x, he k hk x]
  have hkJ : contactGraph G k s₁ ≤ contactGraph G h s₂ :=
    contactGraph_le_of_distance G h k (by linarith)
  have hu : ‖averagedShift G ground f h s₀ s₁ - averagedShift G ground f k s₀ s₁‖ ≤
      ((s₁ - s₀)⁻¹ * (4 * D * L) * B ^ 2) * ‖h - k‖ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro x
    simp only [Pi.sub_apply, Real.norm_eq_abs]
    apply (averagedShift_component_lipschitz_bound G (contactGraph G h s₂) ground f h k
      s₀ s₁ L D hs hL hfground hfl hD (contactGraph_mono G h hss) hkJ x).trans
    gcongr
    exact hh x
  have hn : ‖h - k‖ = ‖averagedShift G ground f h s₀ s₁ - averagedShift G ground f k s₀ s₁‖ := by
    have heq : h - k = -(averagedShift G ground f h s₀ s₁ - averagedShift G ground f k s₀ s₁) := by
      ext x
      have hc := congrFun hcollision x
      simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply] at hc ⊢
      linarith
    rw [heq, norm_neg]
  have hz : ‖h - k‖ = 0 := by rw [← hn] at hu; nlinarith [norm_nonneg (h - k)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

noncomputable def incidentEdges (G : SimpleGraph V) (j : V) : Finset (V × V) :=
  (neighbors G j).image (fun y => (j, y)) ∪ (neighbors G j).image (fun y => (y, j))

@[simp] theorem mem_incidentEdges (G : SimpleGraph V) (j : V) (e : V × V) :
    e ∈ incidentEdges G j ↔ G.Adj e.1 e.2 ∧ (e.1 = j ∨ e.2 = j) := by
  classical
  rcases e with ⟨x, y⟩
  simp only [incidentEdges, Finset.mem_union, Finset.mem_image, mem_neighbors, Prod.mk.injEq]
  constructor
  · rintro (⟨z, hz, rfl, rfl⟩ | ⟨z, hz, rfl, rfl⟩)
    · exact ⟨hz, Or.inl rfl⟩
    · exact ⟨hz.symm, Or.inr rfl⟩
  · rintro ⟨hxy, rfl | rfl⟩
    · exact Or.inl ⟨y, hxy, rfl, rfl⟩
    · exact Or.inr ⟨x, hxy.symm, rfl, rfl⟩

theorem incidentEdges_card_le (G : SimpleGraph V) (D : ℕ)
    (hD : ∀ j, (neighbors G j).card ≤ D) (j : V) : (incidentEdges G j).card ≤ 2 * D := by
  unfold incidentEdges
  calc
    _ ≤ ((neighbors G j).image (fun y => (j, y))).card +
        ((neighbors G j).image (fun y => (y, j))).card := Finset.card_union_le _ _
    _ ≤ D + D := Nat.add_le_add (Finset.card_image_le.trans (hD j))
      (Finset.card_image_le.trans (hD j))
    _ = _ := by omega

omit [Fintype V] [DecidableEq V] in
theorem edgeThreshold_same_off_coordinate (h k : V → ℝ) (j : V)
    (heq : ∀ x, x ≠ j → h x = k x) (e : V × V)
    (he : e.1 ≠ j ∧ e.2 ≠ j) : edgeThreshold k e = edgeThreshold h e := by
  simp [edgeThreshold, heq e.1 he.1, heq e.2 he.2]

omit [Fintype V] in
theorem edgeThreshold_coordinate_bound (h k : V → ℝ) (j : V)
    (heq : ∀ x, x ≠ j → h x = k x) (e : V × V) (hne : e.1 ≠ e.2) :
    |edgeThreshold k e - edgeThreshold h e| ≤ |k j - h j| := by
  have ha (a b : ℝ) : |(1 - |a|) - (1 - |b|)| ≤ |a - b| := by
    calc
      _ = abs (|a| - |b|) := by rw [show (1 - |a|) - (1 - |b|) = -(|a| - |b|) by ring, abs_neg]
      _ ≤ _ := abs_abs_sub_abs_le_abs_sub _ _
  apply (ha _ _).trans
  by_cases h₁ : e.1 = j
  · have h₂ : e.2 ≠ j := by intro he; exact hne (h₁.trans he.symm)
    simp [h₁, ← heq e.2 h₂, sub_sub_sub_cancel_right]
  · by_cases h₂ : e.2 = j
    · simp only [← heq e.1 h₁, h₂]
      rw [show (h e.1 - k j) - (h e.1 - h j) = -(k j - h j) by ring, abs_neg]
    · simp [← heq e.1 h₁, ← heq e.2 h₂]

theorem component_threshold_sum_coordinate (G J : SimpleGraph V) (D : ℕ)
    (hD : ∀ j, (neighbors G j).card ≤ D) (h k : V → ℝ) (j : V)
    (heq : ∀ x, x ≠ j → h x = k x) (x : V) :
    ∑ e ∈ componentEdges G J x, |edgeThreshold k e - edgeThreshold h e| ≤
      (2 * D : ℝ) * |k j - h j| := by
  classical
  let S := (componentEdges G J x).filter (fun e => e.1 = j ∨ e.2 = j)
  have hs : S ⊆ incidentEdges G j := by
    intro e he
    obtain ⟨he, hj⟩ := Finset.mem_filter.mp he
    exact (mem_incidentEdges G j e).2 ⟨((mem_componentEdges G J x e).1 he).2.2, hj⟩
  have hsum : ∑ e ∈ componentEdges G J x, |edgeThreshold k e - edgeThreshold h e| =
      ∑ e ∈ S, |edgeThreshold k e - edgeThreshold h e| := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro e he hen
    have hn : e.1 ≠ j ∧ e.2 ≠ j := by
      simpa only [S, Finset.mem_filter, he, true_and, not_or] using hen
    rw [edgeThreshold_same_off_coordinate h k j heq e hn, sub_self, abs_zero]
  rw [hsum]
  calc
    _ ≤ ∑ e ∈ S, |k j - h j| := Finset.sum_le_sum fun e he =>
      edgeThreshold_coordinate_bound h k j heq e
        (((mem_componentEdges G J x e).1 (Finset.mem_filter.mp he).1).2.2.ne)
    _ = (S.card : ℝ) * |k j - h j| := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast (Finset.card_le_card hs).trans (incidentEdges_card_le G D hD j)) (abs_nonneg _)

theorem averagedShift_coordinate_bound (G J : SimpleGraph V) (ground : Finset V)
    (f h k : V → ℝ) (s₀ s₁ L : ℝ) (D : ℕ) (hs : s₀ < s₁) (hL : 0 ≤ L)
    (hfground : ∀ x ∈ ground, f x = 0)
    (hfl : ∀ x y, G.Adj x y → |f x - f y| ≤ L)
    (hD : ∀ x, (neighbors G x).card ≤ D)
    (hhJ : contactGraph G h s₁ ≤ J) (hkJ : contactGraph G k s₁ ≤ J)
    (j : V) (heq : ∀ x, x ≠ j → h x = k x) (x : V) :
    |averagedShift G ground f h s₀ s₁ x - averagedShift G ground f k s₀ s₁ x| ≤
      ((s₁ - s₀)⁻¹ * (4 * D * L) * (component J x).card) * |k j - h j| := by
  have hd : 0 < s₁ - s₀ := sub_pos.mpr hs
  calc
    _ ≤ (s₁ - s₀)⁻¹ * (2 * L * (component J x).card *
        ∑ e ∈ componentEdges G J x, |edgeThreshold k e - edgeThreshold h e|) :=
      averagedShift_component_difference G J ground f h k s₀ s₁ L hs hL hfground hfl hhJ hkJ x
    _ ≤ (s₁ - s₀)⁻¹ * (2 * L * (component J x).card * ((2 * D : ℝ) * |k j - h j|)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (component_threshold_sum_coordinate G J D hD h k j heq x) (by positivity)) (by positivity)
    _ = _ := by ring

theorem averagedShift_coordinate_zero (G J : SimpleGraph V) (ground : Finset V)
    (f h k : V → ℝ) (s₀ s₁ L : ℝ) (hs : s₀ < s₁) (hL : 0 ≤ L)
    (hfground : ∀ x ∈ ground, f x = 0)
    (hfl : ∀ x y, G.Adj x y → |f x - f y| ≤ L)
    (hhJ : contactGraph G h s₁ ≤ J) (hkJ : contactGraph G k s₁ ≤ J)
    (j : V) (heq : ∀ x, x ≠ j → h x = k x) (x : V) (hj : j ∉ component J x) :
    averagedShift G ground f h s₀ s₁ x = averagedShift G ground f k s₀ s₁ x := by
  have hh := averagedShift_component_difference G J ground f h k s₀ s₁ L hs hL hfground hfl hhJ hkJ x
  have hz : ∑ e ∈ componentEdges G J x, |edgeThreshold k e - edgeThreshold h e| = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    obtain ⟨h₁, h₂, _⟩ := (mem_componentEdges G J x e).1 he
    rw [edgeThreshold_same_off_coordinate h k j heq e
      ⟨fun he => hj (he ▸ h₁), fun he => hj (he ▸ h₂)⟩, sub_self, abs_zero]
  rw [hz, mul_zero, mul_zero] at hh
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hh (abs_nonneg _)))

theorem hasDerivAt_coordinate (u : (V → ℝ) → V → ℝ) (h : V → ℝ)
    (A : (V → ℝ) →L[ℝ] (V → ℝ)) (hu : HasFDerivAt u A h) (x j : V) :
    HasDerivAt (fun t : ℝ => u (h + t • Pi.single j 1) x) (A (Pi.single j 1) x) 0 := by
  have hh : HasDerivAt (fun t : ℝ => h + t • Pi.single j (1 : ℝ)) (Pi.single j 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single j (1 : ℝ))).const_add h
  have huc : HasFDerivAt u A (h + (0 : ℝ) • Pi.single j 1) := by simpa using hu
  have hc := huc.comp_hasDerivAt (0 : ℝ) hh
  have hx := (ContinuousLinearMap.proj x : (V → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hc
  simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using hx

theorem coordinate_small_contact (G : SimpleGraph V) (h : V → ℝ) (j : V)
    {s₁ s₂ t : ℝ} (ht : |t| < (s₂ - s₁) / 2) :
    contactGraph G (h + t • Pi.single j 1) s₁ ≤ contactGraph G h s₂ := by
  apply contactGraph_le_of_distance
  have hn : ‖h - (h + t • Pi.single j (1 : ℝ))‖ = |t| := by
    rw [sub_add_cancel_left, norm_neg, norm_smul, Pi.norm_single]
    simp
  rw [hn]
  linarith

theorem averagedShift_derivative_entry (G : SimpleGraph V) (ground : Finset V)
    (f h : V → ℝ) (s₀ s₁ s₂ L : ℝ) (D : ℕ) (hs : s₀ < s₁) (hss : s₁ < s₂)
    (hL : 0 ≤ L) (hfground : ∀ x ∈ ground, f x = 0)
    (hfl : ∀ x y, G.Adj x y → |f x - f y| ≤ L)
    (hD : ∀ x, (neighbors G x).card ≤ D)
    (A : (V → ℝ) →L[ℝ] (V → ℝ))
    (hu : HasFDerivAt (fun h => averagedShift G ground f h s₀ s₁) A h) (x j : V) :
    |A (Pi.single j 1) x| ≤ (s₁ - s₀)⁻¹ * (4 * D * L) *
      (component (contactGraph G h s₂) x).card := by
  have hd : 0 < s₁ - s₀ := sub_pos.mpr hs
  rw [← Real.norm_eq_abs]
  apply (hasDerivAt_coordinate _ h A hu x j).le_of_lip' (by positivity)
  apply Metric.eventually_nhds_iff.mpr
  refine ⟨(s₂ - s₁) / 2, by linarith, ?_⟩
  intro t ht
  have ht' : |t| < (s₂ - s₁) / 2 := by simpa [Real.dist_eq] using ht
  have hbound := averagedShift_coordinate_bound G (contactGraph G h s₂) ground f h
    (h + t • Pi.single j 1) s₀ s₁ L D hs hL hfground hfl hD
    (contactGraph_mono G h hss.le) (coordinate_small_contact G h j ht') j
    (by intro y hy; simp [Pi.single_eq_of_ne hy]) x
  simpa only [zero_smul, add_zero, Real.norm_eq_abs, sub_zero, Pi.add_apply,
    Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, add_sub_cancel_left,
    abs_sub_comm] using hbound

theorem averagedShift_derivative_entry_zero (G : SimpleGraph V) (ground : Finset V)
    (f h : V → ℝ) (s₀ s₁ s₂ L : ℝ) (hs : s₀ < s₁) (hss : s₁ < s₂)
    (hL : 0 ≤ L) (hfground : ∀ x ∈ ground, f x = 0)
    (hfl : ∀ x y, G.Adj x y → |f x - f y| ≤ L)
    (A : (V → ℝ) →L[ℝ] (V → ℝ))
    (hu : HasFDerivAt (fun h => averagedShift G ground f h s₀ s₁) A h)
    (x j : V) (hj : j ∉ component (contactGraph G h s₂) x) : A (Pi.single j 1) x = 0 := by
  have hn : ‖A (Pi.single j 1) x‖ ≤ 0 := by
    apply (hasDerivAt_coordinate _ h A hu x j).le_of_lip' le_rfl
    apply Metric.eventually_nhds_iff.mpr
    refine ⟨(s₂ - s₁) / 2, by linarith, ?_⟩
    intro t ht
    have ht' : |t| < (s₂ - s₁) / 2 := by simpa [Real.dist_eq] using ht
    have he := averagedShift_coordinate_zero G (contactGraph G h s₂) ground f h
      (h + t • Pi.single j 1) s₀ s₁ L hs hL hfground hfl
      (contactGraph_mono G h hss.le) (coordinate_small_contact G h j ht') j
      (by intro y hy; simp [Pi.single_eq_of_ne hy]) x hj
    simp only [zero_smul, add_zero, he, sub_self, norm_zero, zero_mul, le_refl]
  exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))

noncomputable def derivativeMatrix (A : (V → ℝ) →L[ℝ] (V → ℝ)) : Matrix V V ℝ :=
  fun x j => A (Pi.single j 1) x

theorem averagedShift_derivative_HS (G : SimpleGraph V) (ground : Finset V)
    (f h : V → ℝ) (s₀ s₁ s₂ L : ℝ) (D : ℕ) (hs : s₀ < s₁) (hss : s₁ < s₂)
    (hL : 0 ≤ L) (hfground : ∀ x ∈ ground, f x = 0)
    (hfl : ∀ x y, G.Adj x y → |f x - f y| ≤ L)
    (hD : ∀ x, (neighbors G x).card ≤ D)
    (A : (V → ℝ) →L[ℝ] (V → ℝ))
    (hu : HasFDerivAt (fun h => averagedShift G ground f h s₀ s₁) A h) :
    ∑ x, ∑ j, (derivativeMatrix A x j)^2 ≤
      ((s₁ - s₀)⁻¹ * (4 * D * L)) ^ 2 *
        ∑ x, ((component (contactGraph G h s₂) x).card : ℝ) ^ 3 := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  have hd : 0 < s₁ - s₀ := sub_pos.mpr hs
  have hsum : ∑ j, (derivativeMatrix A x j)^2 =
      ∑ j ∈ component (contactGraph G h s₂) x, (derivativeMatrix A x j)^2 := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    rw [derivativeMatrix, averagedShift_derivative_entry_zero G ground f h s₀ s₁ s₂ L
      hs hss hL hfground hfl A hu x j hj, zero_pow (by decide : 2 ≠ 0)]
  rw [hsum]
  calc
    _ ≤ ∑ j ∈ component (contactGraph G h s₂) x,
        (((s₁ - s₀)⁻¹ * (4 * D * L)) * (component (contactGraph G h s₂) x).card)^2 := by
      apply Finset.sum_le_sum
      intro j _
      rw [← sq_abs (derivativeMatrix A x j)]
      exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).2
        (averagedShift_derivative_entry G ground f h s₀ s₁ s₂ L D hs hss hL hfground hfl hD A hu x j)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

theorem identity_add_bijective {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (u : E → E) (K : NNReal) (hu : LipschitzWith K u) (t : ℝ)
    (ht : |t| * K < 1) : Function.Bijective (fun h : E => h + t • u h) := by
  have hl : ∀ y : E, LipschitzWith ⟨|t| * K, mul_nonneg (abs_nonneg _) K.coe_nonneg⟩
      (fun x => y - t • u x) := by
    intro y
    apply lipschitzWith_iff_norm_sub_le.mpr
    intro x z
    change ‖(y - t • u x) - (y - t • u z)‖ ≤ (|t| * K) * ‖x - z‖
    rw [sub_sub_sub_cancel_left, ← smul_sub, norm_smul, Real.norm_eq_abs]
    calc
      _ ≤ |t| * ((K : ℝ) * ‖z - x‖) := mul_le_mul_of_nonneg_left
        (lipschitzWith_iff_norm_sub_le.mp hu z x) (abs_nonneg _)
      _ = _ := by rw [norm_sub_rev]; ring
  constructor
  · intro x z hxz
    change x + t • u x = z + t • u z at hxz
    have he : x - z = -(t • (u x - u z)) := by
      calc
        x - z = (x + t • u x) - (z + t • u z) - t • (u x - u z) := by
          rw [smul_sub]; abel
        _ = _ := by rw [hxz, sub_self, zero_sub]
    have hn : ‖x - z‖ ≤ (|t| * K) * ‖x - z‖ := by
      calc
        _ = |t| * ‖u x - u z‖ := by rw [he, norm_neg, norm_smul, Real.norm_eq_abs]
        _ ≤ |t| * ((K : ℝ) * ‖x - z‖) := mul_le_mul_of_nonneg_left
          (lipschitzWith_iff_norm_sub_le.mp hu x z) (abs_nonneg _)
        _ = _ := by ring
    have hz : ‖x - z‖ = 0 := by nlinarith [norm_nonneg (x - z)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  · intro y
    have hc : ContractingWith ⟨|t| * K, mul_nonneg (abs_nonneg _) K.coe_nonneg⟩
        (fun x : E => y - t • u x) := ⟨ht, hl y⟩
    let x := ContractingWith.fixedPoint _ hc
    have hx : y - t • u x = x := hc.fixedPoint_isFixedPt
    exact ⟨x, eq_sub_iff_add_eq.mp hx.symm⟩

theorem averagedShift_small_preserves_edge_iff (G : SimpleGraph V) (ground : Finset V)
    (f h : V → ℝ) (s₀ s₁ M t : ℝ) (hs : s₀ < s₁) (hs₀ : 0 ≤ s₀)
    (hM : 0 ≤ M) (hfb : ∀ x, |f x| ≤ M) (ht : |t| * (2 * M) ≤ s₀)
    (x y : V) (hxy : G.Adj x y) :
    |(h x + t * averagedShift G ground f h s₀ s₁ x) -
      (h y + t * averagedShift G ground f h s₀ s₁ y)| ≤ 1 ↔ |h x - h y| ≤ 1 := by
  by_cases hc : 1 - |h x - h y| ≤ s₀
  · rw [averagedShift_tangent G ground f h hs.le hxy hc]
    simp
  · have hfeas : |h x - h y| ≤ 1 := by linarith
    have hu : |averagedShift G ground f h s₀ s₁ x - averagedShift G ground f h s₀ s₁ y| ≤ 2 * M := by
      calc
        _ ≤ |averagedShift G ground f h s₀ s₁ x| + |averagedShift G ground f h s₀ s₁ y| := abs_sub _ _
        _ ≤ _ := by linarith [averagedShift_bound G ground f h s₀ s₁ M hs hM hfb x,
          averagedShift_bound G ground f h s₀ s₁ M hs hM hfb y]
    have himage : |(h x + t * averagedShift G ground f h s₀ s₁ x) -
        (h y + t * averagedShift G ground f h s₀ s₁ y)| ≤ 1 := by
      calc
        _ = |(h x - h y) + t * (averagedShift G ground f h s₀ s₁ x -
            averagedShift G ground f h s₀ s₁ y)| := by congr 1; ring
        _ ≤ |h x - h y| + |t| * |averagedShift G ground f h s₀ s₁ x -
            averagedShift G ground f h s₀ s₁ y| := by
            rw [← abs_mul]
            exact abs_add_le _ _
        _ ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_left hu (abs_nonneg t)]
    exact iff_of_true himage hfeas

omit [DecidableEq V] in
theorem abs_trace_square_le_HS (A : Matrix V V ℝ) :
    |(A * A).trace| ≤ ∑ x, ∑ j, (A x j)^2 := by
  classical
  calc
    _ = |∑ x, ∑ j, A x j * A j x| := by simp [Matrix.trace, Matrix.mul_apply]
    _ ≤ ∑ x, ∑ j, |A x j * A j x| := (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun x _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ x, ∑ j, ((A x j)^2 + (A j x)^2) / 2 := by
      apply Finset.sum_le_sum; intro x _
      apply Finset.sum_le_sum; intro j _
      rw [abs_mul]
      nlinarith [sq_nonneg (|A x j| - |A j x|), sq_abs (A x j), sq_abs (A j x)]
    _ = _ := by
      simp only [← Finset.sum_div, Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun x j => (A j x)^2)]
      ring

omit [Fintype V] in
@[simp] theorem extendHeight_pin (pins : Finset V) (β : V → ℝ)
    (h : FreeSites pins → ℝ) (x : V) (hx : x ∈ pins) : extendHeight pins β h x = β x := by
  simp [extendHeight, hx]

omit [Fintype V] in
@[simp] theorem extendHeight_free (pins : Finset V) (β : V → ℝ)
    (h : FreeSites pins → ℝ) (x : FreeSites pins) : extendHeight pins β h x = h x := by
  simp [extendHeight, x.property]

theorem extendHeight_lipschitz (pins : Finset V) (β : V → ℝ) :
    LipschitzWith 1 (extendHeight pins β) := by
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro h k
  simp only [NNReal.coe_one, one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro x
  simp only [Pi.sub_apply]
  by_cases hx : x ∈ pins
  · simp [extendHeight, hx]
  · simpa only [extendHeight, dite_eq_right hx, Pi.sub_apply] using norm_le_pi_norm (h - k) ⟨x, hx⟩

theorem freeShift_lipschitz (G : SimpleGraph V) (ground pins : Finset V)
    (β f : V → ℝ) (s₀ s₁ M : ℝ) (hs : s₀ < s₁) (hM : 0 ≤ M)
    (hfb : ∀ x, |f x| ≤ M) :
    LipschitzWith ⟨(s₁ - s₀)⁻¹ * (4 * M * Fintype.card (V × V)), by positivity⟩
      (freeShift G ground pins β f s₀ s₁) := by
  have hh := (averagedShift_lipschitz G ground f s₀ s₁ M hs hM hfb).comp
    (extendHeight_lipschitz pins β)
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro h k
  change ‖freeShift G ground pins β f s₀ s₁ h - freeShift G ground pins β f s₀ s₁ k‖ ≤
    ((s₁ - s₀)⁻¹ * (4 * M * Fintype.card (V × V))) * ‖h - k‖
  have hd : 0 < s₁ - s₀ := sub_pos.mpr hs
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro x
  change ‖(averagedShift G ground f (extendHeight pins β h) s₀ s₁ -
    averagedShift G ground f (extendHeight pins β k) s₀ s₁) (x : V)‖ ≤ _
  apply (norm_le_pi_norm _ (x : V)).trans
  have hh' := lipschitzWith_iff_norm_sub_le.mp hh h k
  change ‖averagedShift G ground f (extendHeight pins β h) s₀ s₁ -
    averagedShift G ground f (extendHeight pins β k) s₀ s₁‖ ≤
    (((s₁ - s₀)⁻¹ * (4 * M * Fintype.card (V × V))) * 1) * ‖h - k‖ at hh'
  simpa only [mul_one] using hh'

theorem extendHeight_shift (G : SimpleGraph V) (ground pins : Finset V)
    (hp : pins ⊆ ground) (β f : V → ℝ) (s₀ s₁ t : ℝ) (h : FreeSites pins → ℝ) :
    extendHeight pins β (h + t • freeShift G ground pins β f s₀ s₁ h) =
      extendHeight pins β h + t • averagedShift G ground f (extendHeight pins β h) s₀ s₁ := by
  ext x
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hx : x ∈ pins
  · simp [extendHeight_pin pins β _ x hx,
      averagedShift_ground G ground f (extendHeight pins β h) s₀ s₁ (hp hx)]
  · simp [extendHeight, hx, freeShift]

theorem freeShift_small_polytope_preimage (G₀ G : SimpleGraph V) (ground pins walls : Finset V)
    (hp : pins ⊆ ground) (hw : walls ⊆ ground)
    (hG : ∀ x y, G₀.Adj x y → G.Adj x y ∨ (x ∈ ground ∧ y ∈ ground))
    (β f : V → ℝ) (I : V → Set ℝ) (s₀ s₁ M t : ℝ) (hs : s₀ < s₁) (hs₀ : 0 ≤ s₀)
    (hM : 0 ≤ M) (hfb : ∀ x, |f x| ≤ M) (ht : |t| * (2 * M) ≤ s₀) :
    (fun h => h + t • freeShift G ground pins β f s₀ s₁ h) ⁻¹'
      heightPolytope G₀ pins walls β I = heightPolytope G₀ pins walls β I := by
  ext h
  simp only [Set.mem_preimage, heightPolytope, Set.mem_ofPred_eq,
    extendHeight_shift G ground pins hp β f s₀ s₁ t h, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hedge (x y : V) (hxy : G₀.Adj x y) :
      |extendHeight pins β h x + t * averagedShift G ground f (extendHeight pins β h) s₀ s₁ x -
        (extendHeight pins β h y + t * averagedShift G ground f (extendHeight pins β h) s₀ s₁ y)| ≤ 1 ↔
      |extendHeight pins β h x - extendHeight pins β h y| ≤ 1 := by
    rcases hG x y hxy with hxy | ⟨hx, hy⟩
    · exact averagedShift_small_preserves_edge_iff G ground f (extendHeight pins β h)
        s₀ s₁ M t hs hs₀ hM hfb ht x y hxy
    · simp [averagedShift_ground G ground f (extendHeight pins β h) s₀ s₁ hx,
        averagedShift_ground G ground f (extendHeight pins β h) s₀ s₁ hy]
  have hwall (x : V) (hx : x ∈ walls) :
      extendHeight pins β h x + t * averagedShift G ground f (extendHeight pins β h) s₀ s₁ x =
        extendHeight pins β h x := by
    rw [averagedShift_ground G ground f (extendHeight pins β h) s₀ s₁ (hw hx), mul_zero, add_zero]
  constructor
  · rintro ⟨he, hi⟩
    exact ⟨fun x y hxy => (hedge x y hxy).mp (he x y hxy),
      fun x hx => by simpa only [hwall x hx] using hi x hx⟩
  · rintro ⟨he, hi⟩
    exact ⟨fun x y hxy => (hedge x y hxy).mpr (he x y hxy),
      fun x hx => by simpa only [hwall x hx] using hi x hx⟩

theorem freeShift_small_polytope_onto (G₀ G : SimpleGraph V) (ground pins walls : Finset V)
    (hp : pins ⊆ ground) (hw : walls ⊆ ground)
    (hG : ∀ x y, G₀.Adj x y → G.Adj x y ∨ (x ∈ ground ∧ y ∈ ground))
    (β f : V → ℝ) (I : V → Set ℝ) (s₀ s₁ M t : ℝ) (hs : s₀ < s₁) (hs₀ : 0 ≤ s₀)
    (hM : 0 ≤ M) (hfb : ∀ x, |f x| ≤ M) (ht : |t| * (2 * M) ≤ s₀)
    (htlip : |t| * ((s₁ - s₀)⁻¹ * (4 * M * Fintype.card (V × V))) < 1) :
    (fun h => h + t • freeShift G ground pins β f s₀ s₁ h) ''
      heightPolytope G₀ pins walls β I = heightPolytope G₀ pins walls β I := by
  have hb := identity_add_bijective _ _ (freeShift_lipschitz G ground pins β f s₀ s₁ M hs hM hfb) t htlip
  have hpree := freeShift_small_polytope_preimage G₀ G ground pins walls hp hw hG β f I
    s₀ s₁ M t hs hs₀ hM hfb ht
  rw [← hpree, Set.image_preimage_eq _ hb.surjective]
  exact hpree.symm

omit [Fintype V] in
theorem extendHeight_coordinate (pins : Finset V) (β : V → ℝ) (h : FreeSites pins → ℝ)
    (j : FreeSites pins) (t : ℝ) :
    extendHeight pins β (h + t • Pi.single j 1) = extendHeight pins β h + t • Pi.single (j : V) 1 := by
  ext x
  by_cases hx : x ∈ pins
  · have hxj : x ≠ (j : V) := by intro he; exact j.property (he ▸ hx)
    simp [extendHeight, hx, Pi.single_eq_of_ne hxj]
  · by_cases hxj : x = (j : V)
    · subst x
      simp [extendHeight, j.property]
    · have hn : (⟨x, hx⟩ : FreeSites pins) ≠ j := by intro he; exact hxj (congrArg Subtype.val he)
      simp [extendHeight, hx, Pi.single_eq_of_ne hxj, Pi.single_eq_of_ne hn]

theorem freeShift_derivative_entry (G : SimpleGraph V) (ground pins : Finset V)
    (β f : V → ℝ) (h : FreeSites pins → ℝ)
    (s₀ s₁ s₂ L : ℝ) (D : ℕ) (hs : s₀ < s₁) (hss : s₁ < s₂)
    (hL : 0 ≤ L) (hfground : ∀ x ∈ ground, f x = 0)
    (hfl : ∀ x y, G.Adj x y → |f x - f y| ≤ L)
    (hD : ∀ x, (neighbors G x).card ≤ D)
    (A : (FreeSites pins → ℝ) →L[ℝ] (FreeSites pins → ℝ))
    (hu : HasFDerivAt (freeShift G ground pins β f s₀ s₁) A h) (x j : FreeSites pins) :
    |A (Pi.single j 1) x| ≤ (s₁ - s₀)⁻¹ * (4 * D * L) *
      (component (contactGraph G (extendHeight pins β h) s₂) x).card := by
  have hd : 0 < s₁ - s₀ := sub_pos.mpr hs
  rw [← Real.norm_eq_abs]
  apply (hasDerivAt_coordinate _ h A hu x j).le_of_lip' (by positivity)
  apply Metric.eventually_nhds_iff.mpr
  refine ⟨(s₂ - s₁) / 2, by linarith, ?_⟩
  intro t ht
  have ht' : |t| < (s₂ - s₁) / 2 := by simpa [Real.dist_eq] using ht
  have hbound := averagedShift_coordinate_bound G (contactGraph G (extendHeight pins β h) s₂)
    ground f (extendHeight pins β h) (extendHeight pins β h + t • Pi.single (j : V) 1)
    s₀ s₁ L D hs hL hfground hfl hD (contactGraph_mono G _ hss.le)
    (coordinate_small_contact G _ j ht') j (by intro y hy; simp [Pi.single_eq_of_ne hy]) x
  simp only [freeShift, extendHeight_coordinate]
  simpa only [zero_smul, add_zero, Real.norm_eq_abs, sub_zero, Pi.add_apply,
    Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, add_sub_cancel_left,
    abs_sub_comm] using hbound

theorem freeShift_derivative_entry_zero (G : SimpleGraph V) (ground pins : Finset V)
    (β f : V → ℝ) (h : FreeSites pins → ℝ)
    (s₀ s₁ s₂ L : ℝ) (hs : s₀ < s₁) (hss : s₁ < s₂)
    (hL : 0 ≤ L) (hfground : ∀ x ∈ ground, f x = 0)
    (hfl : ∀ x y, G.Adj x y → |f x - f y| ≤ L)
    (A : (FreeSites pins → ℝ) →L[ℝ] (FreeSites pins → ℝ))
    (hu : HasFDerivAt (freeShift G ground pins β f s₀ s₁) A h)
    (x j : FreeSites pins) (hj : (j : V) ∉ component (contactGraph G (extendHeight pins β h) s₂) x) :
    A (Pi.single j 1) x = 0 := by
  have hn : ‖A (Pi.single j 1) x‖ ≤ 0 := by
    apply (hasDerivAt_coordinate _ h A hu x j).le_of_lip' le_rfl
    apply Metric.eventually_nhds_iff.mpr
    refine ⟨(s₂ - s₁) / 2, by linarith, ?_⟩
    intro t ht
    have ht' : |t| < (s₂ - s₁) / 2 := by simpa [Real.dist_eq] using ht
    have he := averagedShift_coordinate_zero G (contactGraph G (extendHeight pins β h) s₂) ground f
      (extendHeight pins β h) (extendHeight pins β h + t • Pi.single (j : V) 1) s₀ s₁ L hs hL hfground hfl
      (contactGraph_mono G _ hss.le) (coordinate_small_contact G _ j ht') j
      (by intro y hy; simp [Pi.single_eq_of_ne hy]) x hj
    simp only [freeShift, extendHeight_coordinate, zero_smul, add_zero, he, sub_self,
      norm_zero, zero_mul, le_refl]
  exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))

theorem freeShift_derivative_ground (G : SimpleGraph V) (ground pins : Finset V)
    (β f : V → ℝ) (h : FreeSites pins → ℝ) (s₀ s₁ : ℝ)
    (A : (FreeSites pins → ℝ) →L[ℝ] (FreeSites pins → ℝ))
    (hu : HasFDerivAt (freeShift G ground pins β f s₀ s₁) A h)
    (x j : FreeSites pins) (hx : (x : V) ∈ ground) : A (Pi.single j 1) x = 0 := by
  have hd := hasDerivAt_coordinate _ h A hu x j
  have he : (fun t : ℝ => freeShift G ground pins β f s₀ s₁ (h + t • Pi.single j 1) x) =
      fun _ : ℝ => (0 : ℝ) := by
    funext t
    exact averagedShift_ground G ground f _ s₀ s₁ hx
  rw [he] at hd
  exact hd.unique (hasDerivAt_const 0 0)

theorem freeShift_derivative_HS (G : SimpleGraph V) (ground pins : Finset V)
    (β f : V → ℝ) (h : FreeSites pins → ℝ)
    (s₀ s₁ s₂ L : ℝ) (D : ℕ) (hs : s₀ < s₁) (hss : s₁ < s₂)
    (hL : 0 ≤ L) (hfground : ∀ x ∈ ground, f x = 0)
    (hfl : ∀ x y, G.Adj x y → |f x - f y| ≤ L)
    (hD : ∀ x, (neighbors G x).card ≤ D)
    (A : (FreeSites pins → ℝ) →L[ℝ] (FreeSites pins → ℝ))
    (hu : HasFDerivAt (freeShift G ground pins β f s₀ s₁) A h) :
    ∑ x, ∑ j, (derivativeMatrix A x j)^2 ≤
      ((s₁ - s₀)⁻¹ * (4 * D * L)) ^ 2 *
        ∑ x : FreeSites pins, if (x : V) ∈ ground then 0 else
          ((component (contactGraph G (extendHeight pins β h) s₂) x).card : ℝ) ^ 3 := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  have hd : 0 < s₁ - s₀ := sub_pos.mpr hs
  by_cases hx : (x : V) ∈ ground
  · simp only [ite_eq_left hx, mul_zero, derivativeMatrix,
      freeShift_derivative_ground G ground pins β f h s₀ s₁ A hu x _ hx,
      zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, le_refl]
  rw [ite_eq_right hx]
  let C := component (contactGraph G (extendHeight pins β h) s₂) x
  let F : Finset (FreeSites pins) := Finset.univ.filter fun j => (j : V) ∈ C
  have hFc : F.card ≤ C.card := by
    apply Finset.card_le_card_of_injOn (fun j : FreeSites pins => (j : V))
    · intro j hj
      exact (Finset.mem_filter.mp hj).2
    · intro j hj k hk hjk
      exact Subtype.ext hjk
  have hsum : ∑ j, (derivativeMatrix A x j)^2 = ∑ j ∈ F, (derivativeMatrix A x j)^2 := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    have hj' : (j : V) ∉ C := by simpa [F] using hj
    rw [derivativeMatrix, freeShift_derivative_entry_zero G ground pins β f h s₀ s₁ s₂ L
      hs hss hL hfground hfl A hu x j hj', zero_pow (by decide : 2 ≠ 0)]
  rw [hsum]
  calc
    _ ≤ ∑ j ∈ F, (((s₁ - s₀)⁻¹ * (4 * D * L)) * C.card)^2 := by
      apply Finset.sum_le_sum
      intro j _
      rw [← sq_abs (derivativeMatrix A x j)]
      exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).2
        (freeShift_derivative_entry G ground pins β f h s₀ s₁ s₂ L D hs hss hL hfground hfl hD A hu x j)
    _ ≤ C.card * (((s₁ - s₀)⁻¹ * (4 * D * L)) * C.card)^2 := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hFc) (sq_nonneg _)
    _ = _ := by dsimp [C]; ring

theorem freeShift_ae_differentiable (G : SimpleGraph V) (ground pins : Finset V)
    (β f : V → ℝ) (s₀ s₁ M : ℝ) (hs : s₀ < s₁) (hM : 0 ≤ M)
    (hfb : ∀ x, |f x| ≤ M) :
    ∀ᵐ h ∂(volume : Measure (FreeSites pins → ℝ)),
      DifferentiableAt ℝ (freeShift G ground pins β f s₀ s₁) h :=
  (freeShift_lipschitz G ground pins β f s₀ s₁ M hs hM hfb).ae_differentiableAt

end FeasibleShift

end OAI
