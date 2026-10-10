import OAI.Combinatorics.TreewidthL1.ExpandedParticles

namespace OAI

universe treewidthLevel1 treewidthLevel2

namespace BoundedTreewidthL1.OrderedSweepFlow
open scoped BigOperators

variable {α β : Type*} [Fintype α] [LinearOrder α] [LinearOrder β]

noncomputable def fiber (b : α → β) (x : α) : Finset α := by
  classical
  exact Finset.univ.filter (fun y => b y = b x)

noncomputable def mass (μ : α → ℝ) (b : α → β) (x : α) : ℝ :=
  ∑ y ∈ fiber b x, μ y

noncomputable def bath (μ : α → ℝ) (b : α → β) (f : α → ℝ) (x : α) : ℝ :=
  (∑ y ∈ fiber b x, μ y * f y) / mass μ b x

noncomputable def total (μ f : α → ℝ) : ℝ := ∑ x, μ x * f x

noncomputable def risk (μ f : α → ℝ) (p : α → Bool) : ℝ :=
  ∑ x, μ x * (if p x then 1 - f x else f x)

end BoundedTreewidthL1.OrderedSweepFlow

namespace BoundedTreewidthL1.OrderedSweepFlow
variable {α β : Type*} [Fintype α] [LinearOrder α] [LinearOrder β]

lemma mem_fiber
    {α : Type treewidthLevel1} {β : Type treewidthLevel2} [Fintype α] [LinearOrder α]
    [LinearOrder β]
    (b : α → β) (x y : α) : y ∈ fiber b x ↔ b y = b x := by
  classical
  simp [fiber]

lemma fiber_eq (b : α → β) {x y : α} (h : b x = b y) : fiber b x = fiber b y := by
  classical
  ext z
  simp only [mem_fiber, h]

lemma mass_pos (μ : α → ℝ) (hμ : ∀ x, 0 < μ x) (b : α → β) (x : α) :
    0 < mass μ b x := by
  classical
  exact Finset.sum_pos (fun y _ => hμ y) ⟨x, (mem_fiber b x x).mpr rfl⟩

lemma bath_const_fiber (μ : α → ℝ) (b : α → β) (f : α → ℝ) {x y : α}
    (h : b x = b y) : bath μ b f x = bath μ b f y := by
  unfold bath mass
  rw [fiber_eq b h]

lemma bath_le (μ : α → ℝ) (hμ : ∀ x, 0 < μ x) (b : α → β)
    (f : α → ℝ) (x : α) (c : ℝ) (hc : ∀ y ∈ fiber b x, f y ≤ c) :
    bath μ b f x ≤ c := by
  rw [bath, div_le_iff₀ (mass_pos μ hμ b x)]
  unfold mass
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun y hy => by nlinarith [hμ y, hc y hy])

lemma le_bath (μ : α → ℝ) (hμ : ∀ x, 0 < μ x) (b : α → β)
    (f : α → ℝ) (x : α) (c : ℝ) (hc : ∀ y ∈ fiber b x, c ≤ f y) :
    c ≤ bath μ b f x := by
  rw [bath, le_div_iff₀ (mass_pos μ hμ b x)]
  unfold mass
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun y hy => by nlinarith [hμ y, hc y hy])

lemma fiber_lt (b : α → β) (hb : Monotone b) {x y s t : α}
    (hxy : b x < b y) (hs : s ∈ fiber b x) (ht : t ∈ fiber b y) : s < t := by
  have hs' := (mem_fiber b x s).mp hs
  have ht' := (mem_fiber b y t).mp ht
  by_contra h
  have := hb (le_of_not_gt h)
  rw [hs', ht'] at this
  exact (not_le_of_gt hxy) this

theorem bath_monotone (μ : α → ℝ) (hμ : ∀ x, 0 < μ x)
    (b : α → β) (hb : Monotone b) (f : α → ℝ) (hf : Monotone f) :
    Monotone (bath μ b f) := by
  intro x y hxy
  rcases (hb hxy).eq_or_lt with h | h
  · exact le_of_eq (bath_const_fiber μ b f h)
  · apply le_bath μ hμ b f y
    intro t ht
    apply bath_le μ hμ b f x
    intro s hs
    exact hf (fiber_lt b hb h hs ht).le

theorem bath_antitone (μ : α → ℝ) (hμ : ∀ x, 0 < μ x)
    (b : α → β) (hb : Monotone b) (f : α → ℝ) (hf : Antitone f) :
    Antitone (bath μ b f) := by
  intro x y hxy
  rcases (hb hxy).eq_or_lt with h | h
  · exact le_of_eq (bath_const_fiber μ b f h.symm)
  · apply le_bath μ hμ b f x
    intro s hs
    apply bath_le μ hμ b f y
    intro t ht
    exact hf (fiber_lt b hb h hs ht).le

lemma bath_bounds (μ : α → ℝ) (hμ : ∀ x, 0 < μ x) (b : α → β)
    (f : α → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (x : α) :
    0 ≤ bath μ b f x ∧ bath μ b f x ≤ 1 :=
  ⟨le_bath μ hμ b f x 0 (fun y _ => (hf y).1),
   bath_le μ hμ b f x 1 (fun y _ => (hf y).2)⟩

lemma bath_expand
    {α : Type treewidthLevel1} {β : Type treewidthLevel2} [Fintype α] [LinearOrder α]
    [LinearOrder β]
    (μ : α → ℝ) (b : α → β) (f : α → ℝ) (x : α) :
    bath μ b f x = ∑ y, if b y = b x then μ y * f y / mass μ b x else 0 := by
  classical
  simp [bath, fiber, Finset.sum_filter, Finset.sum_div, ite_div]

theorem bath_total (μ : α → ℝ) (hμ : ∀ x, 0 < μ x)
    (b : α → β) (f : α → ℝ) : total μ (bath μ b f) = total μ f := by
  classical
  unfold total
  simp_rw [bath_expand, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  have he (x : α) :
      μ x * (if b y = b x then μ y * f y / mass μ b x else 0) =
      (if b x = b y then μ x else 0) * (μ y * f y / mass μ b y) := by
    by_cases h : b x = b y
    · have hm : mass μ b x = mass μ b y := by unfold mass; rw [fiber_eq b h]
      simp [h, hm]
    · simp [h, Ne.symm h]
  simp_rw [he]
  rw [← Finset.sum_mul]
  have hm : (∑ x, if b x = b y then μ x else 0) = mass μ b y := by
    simp [mass, fiber, Finset.sum_filter]
  rw [hm]
  field_simp [ne_of_gt (mass_pos μ hμ b y)]

end BoundedTreewidthL1.OrderedSweepFlow

namespace BoundedTreewidthL1.OrderedSweepFlow
variable {α β : Type*} [Fintype α] [LinearOrder α] [LinearOrder β]

noncomputable def defect (μ f p : α → ℝ) : ℝ :=
  ∑ x, μ x * (f x + p x - 2 * f x * p x)

noncomputable def optimal (μ : α → ℝ) (b : α → β) (f : α → ℝ) : α → Bool :=
  fun x => decide (1 / 2 < bath μ b f x)

noncomputable def labelReal (p : α → Bool) : α → ℝ :=
  fun x => if p x then 1 else 0

end BoundedTreewidthL1.OrderedSweepFlow

namespace BoundedTreewidthL1.OrderedSweepFlow
variable {α β : Type*} [Fintype α] [LinearOrder α] [LinearOrder β]

lemma defect_eq
    {α : Type treewidthLevel1} [Fintype α] [LinearOrder α]
    (μ f p : α → ℝ) :
    defect μ f p = total μ f + total μ p - 2 * total μ (fun x => f x * p x) := by
  classical
  simp only [defect, total, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma bath_mul (μ : α → ℝ) (b : α → β) (f p : α → ℝ)
    (hp : ∀ x y, b x = b y → p x = p y) (x : α) :
    bath μ b (fun y => f y * p y) x = bath μ b f x * p x := by
  classical
  unfold bath
  have h : (∑ y ∈ fiber b x, μ y * (f y * p y)) =
      (∑ y ∈ fiber b x, μ y * f y) * p x := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y hy
    rw [hp y x ((mem_fiber b x y).mp hy)]
    ring
  rw [h]
  ring

lemma defect_bath (μ : α → ℝ) (hμ : ∀ x, 0 < μ x) (b : α → β)
    (f p : α → ℝ) (hp : ∀ x y, b x = b y → p x = p y) :
    defect μ (bath μ b f) p = defect μ f p := by
  rw [defect_eq, defect_eq, bath_total μ hμ b f]
  congr 1
  congr 1
  have h := bath_total μ hμ b (fun x => f x * p x)
  have hh : bath μ b (fun x => f x * p x) = (fun x => bath μ b f x * p x) :=
    funext (bath_mul μ b f p hp)
  rw [hh] at h
  exact h

lemma optimal_fiber (μ : α → ℝ) (b : α → β) (f : α → ℝ)
    {x y : α} (h : b x = b y) : optimal μ b f x = optimal μ b f y := by
  simp only [optimal, bath_const_fiber μ b f h]

theorem optimal_monotone (μ : α → ℝ) (hμ : ∀ x, 0 < μ x)
    (b : α → β) (hb : Monotone b) (f : α → ℝ) (hf : Monotone f) :
    Monotone (optimal μ b f) := by
  intro x y hxy
  have h := bath_monotone μ hμ b hb f hf hxy
  simp only [optimal]
  by_cases hx : 1 / 2 < bath μ b f x
  · have hy : 1 / 2 < bath μ b f y := hx.trans_le h
    simp only [hx, hy, decide_true, le_refl]
  · simp only [hx, decide_false, Bool.false_le]

theorem optimal_defect_le (μ : α → ℝ) (hμ : ∀ x, 0 < μ x)
    (b : α → β) (f p : α → ℝ) (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1)
    (hpb : ∀ x y, b x = b y → p x = p y) :
    defect μ f (labelReal (optimal μ b f)) ≤ defect μ f p := by
  classical
  have hc : ∀ x y, b x = b y →
      labelReal (optimal μ b f) x = labelReal (optimal μ b f) y := by
    intro x y h
    simp only [labelReal, optimal_fiber μ b f h]
  rw [← defect_bath μ hμ b f _ hc, ← defect_bath μ hμ b f p hpb]
  apply Finset.sum_le_sum
  intro x _
  apply mul_le_mul_of_nonneg_left _ (hμ x).le
  dsimp [labelReal, optimal]
  split_ifs with h
  · have h' : 1 / 2 < bath μ b f x := of_decide_eq_true h
    simp only [h, ↓reduceIte]
    nlinarith [(hp x).2]
  · have h' : ¬1 / 2 < bath μ b f x := by simpa only [decide_eq_true_eq] using h
    simp only [h, Bool.false_eq_true, ↓reduceIte]
    nlinarith [(hp x).1]

lemma labelReal_bounds
    {α : Type treewidthLevel1} [Fintype α] [LinearOrder α]
    (p : α → Bool) (x : α) :
    0 ≤ labelReal p x ∧ labelReal p x ≤ 1 := by
  simp only [labelReal]
  split <;> norm_num

lemma defect_mean_bound
    {α : Type treewidthLevel1} [Fintype α] [LinearOrder α]
    (μ f p : α → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1) :
    |total μ f - total μ p| ≤ defect μ f p := by
  classical
  have hl : total μ p - total μ f ≤ defect μ f p := by
    unfold total defect
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum (fun x _ => by
      nlinarith [mul_nonneg (hμ x) (mul_nonneg (hf x).1 (sub_nonneg.mpr (hp x).2))])
  have hr : total μ f - total μ p ≤ defect μ f p := by
    unfold total defect
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum (fun x _ => by
      nlinarith [mul_nonneg (hμ x) (mul_nonneg (hp x).1 (sub_nonneg.mpr (hf x).2))])
  exact abs_le.mpr ⟨by linarith, hr⟩

lemma pair_mean_bound (μ f g p : α → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1) :
    |total μ f - total μ g| ≤ defect μ f p + defect μ g p := by
  have h := abs_sub_le (total μ f) (total μ p) (total μ g)
  rw [abs_sub_comm (total μ p)] at h
  exact h.trans (add_le_add (defect_mean_bound μ f p hμ hf hp)
    (defect_mean_bound μ g p hμ hg hp))

end BoundedTreewidthL1.OrderedSweepFlow

namespace BoundedTreewidthL1.OrderedSweepFlow
variable {α β : Type*} [Fintype α] [LinearOrder α] [LinearOrder β]

/-- On a chain of nested cuts, a monotone classifier determined by its trace
on a bag is either constant or evaluation at one of that bag's vertices. -/
theorem monotone_classifier {P : Type*} (labels : α → P → Bool)
    (hl : ∀ p, Monotone (fun x => labels x p)) (c : α → Bool) (hc : Monotone c)
    (htrace : ∀ x y, (∀ p, labels x p = labels y p) → c x = c y) :
    c = (fun _ => false) ∨ c = (fun _ => true) ∨ ∃ p, c = (fun x => labels x p) := by
  classical
  by_cases hf : ∀ x, c x = false
  · exact Or.inl (funext hf)
  by_cases ht : ∀ x, c x = true
  · exact Or.inr (Or.inl (funext ht))
  push Not at hf ht
  obtain ⟨a, ha⟩ := ht
  obtain ⟨b, hb⟩ := hf
  have ha' : c a = false := by cases h : c a <;> simp_all
  have hb' : c b = true := by cases h : c b <;> simp_all
  let lo := Finset.univ.filter (fun x => c x = false)
  let hi := Finset.univ.filter (fun x => c x = true)
  have hlo : lo.Nonempty := ⟨a, by simp [lo, ha']⟩
  have hhi : hi.Nonempty := ⟨b, by simp [hi, hb']⟩
  let u := lo.max' hlo
  let v := hi.min' hhi
  have hu : c u = false := by simpa [lo] using lo.max'_mem hlo
  have hv : c v = true := by simpa [hi] using hi.min'_mem hhi
  have huv : u ≤ v := by
    by_contra h
    have hh := hc (le_of_lt (lt_of_not_ge h))
    rw [hu, hv] at hh
    contradiction
  have hn : ¬∀ p, labels u p = labels v p := by
    intro h
    have := htrace u v h
    rw [hu, hv] at this
    contradiction
  obtain ⟨p, hp⟩ := not_forall.mp hn
  have hlp : labels u p ≤ labels v p := hl p huv
  have hup : labels u p = false := by
    cases h : labels u p <;> cases h' : labels v p <;> simp_all
    exact Bool.noConfusion (hlp rfl)
  have hvp : labels v p = true := by
    cases h : labels u p <;> cases h' : labels v p <;> simp_all
  refine Or.inr (Or.inr ⟨p, funext (fun x => ?_)⟩)
  cases hx : c x with
  | false =>
    have hxu : x ≤ u := lo.le_max' x (by simp [lo, hx])
    have h : labels x p ≤ labels u p := hl p hxu
    rw [hup] at h
    cases hx' : labels x p <;> simp_all
    exact Bool.noConfusion (h rfl)
  | true =>
    have hvx : v ≤ x := hi.min'_le x (by simp [hi, hx])
    have h : labels v p ≤ labels x p := hl p hvx
    rw [hvp] at h
    cases hx' : labels x p <;> simp_all
    exact Bool.noConfusion (h rfl)

/-- The height-gap transport estimate for a retained ordered sweep. `f` is the
backward endpoint response; interval heat baths keep it monotone and preserve
its mean. The comparison predictor may be arbitrarily randomized by the past. -/
theorem height_transport {P : Type*} (μ : α → ℝ) (hμ : ∀ x, 0 < μ x)
    (b : α → β) (hb : Monotone b) (labels : α → P → Bool)
    (hl : ∀ p, Monotone (fun x => labels x p))
    (htrace : ∀ x y, (∀ p, labels x p = labels y p) → b x = b y)
    (f p : α → ℝ) (hf : Monotone f) (hfb : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1)
    (hpb : ∀ x y, b x = b y → p x = p y)
    (t : ℝ) (h0 : t ≤ total μ f) (h1 : t ≤ total μ (fun _ => 1) - total μ f)
    (hgap : ∀ v, t ≤ |total μ f - total μ (labelReal (fun x => labels x v))|) :
    t ≤ defect μ f p := by
  let c := optimal μ b f
  have hc := optimal_monotone μ hμ b hb f hf
  have hcTrace : ∀ x y, (∀ v, labels x v = labels y v) → c x = c y := by
    intro x y h
    exact optimal_fiber μ b f (htrace x y h)
  have ha := monotone_classifier labels hl c hc hcTrace
  have hmin := optimal_defect_le μ hμ b f p hp hpb
  have hmean := (defect_mean_bound μ f (labelReal c) (fun x => (hμ x).le) hfb
    (labelReal_bounds c)).trans hmin
  rcases ha with he | he | ⟨v, he⟩
  · have hm : total μ (labelReal c) = 0 := by simp [he, labelReal, total]
    rw [hm, sub_zero] at hmean
    have hn : 0 ≤ total μ f := Finset.sum_nonneg (fun x _ => mul_nonneg (hμ x).le (hfb x).1)
    rw [abs_of_nonneg hn] at hmean
    exact h0.trans hmean
  · have hm : total μ (labelReal c) = total μ (fun _ => 1) := by simp [he, labelReal, total]
    rw [hm] at hmean
    have hn : total μ f ≤ total μ (fun _ => 1) :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hfb x).2 (hμ x).le)
    rw [abs_of_nonpos (sub_nonpos.mpr hn)] at hmean
    exact h1.trans (by linarith)
  · rw [he] at hmean
    exact (hgap v).trans hmean

end BoundedTreewidthL1.OrderedSweepFlow

namespace BoundedTreewidthL1.OrderedSweepFlow
variable {α β : Type*} [Fintype α] [LinearOrder α] [LinearOrder β]

noncomputable def execute (μ : α → ℝ) (bs : List (α → β)) (f : α → ℝ) : α → ℝ :=
  bs.foldr (fun b g => bath μ b g) f

lemma execute_monotone (μ : α → ℝ) (hμ : ∀ x, 0 < μ x)
    (bs : List (α → β)) (hb : ∀ b ∈ bs, Monotone b)
    (f : α → ℝ) (hf : Monotone f) : Monotone (execute μ bs f) := by
  induction bs with
  | nil => exact hf
  | cons b bs ih =>
    exact bath_monotone μ hμ b (hb b (by simp)) _
      (ih (fun c hc => hb c (by simp [hc])))

lemma execute_total (μ : α → ℝ) (hμ : ∀ x, 0 < μ x)
    (bs : List (α → β)) (f : α → ℝ) : total μ (execute μ bs f) = total μ f := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    change total μ (bath μ b (execute μ bs f)) = _
    rw [bath_total μ hμ, ih]

lemma execute_bounds (μ : α → ℝ) (hμ : ∀ x, 0 < μ x)
    (bs : List (α → β)) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    ∀ x, 0 ≤ execute μ bs f x ∧ execute μ bs f x ≤ 1 := by
  induction bs with
  | nil => exact hf
  | cons b bs ih => exact bath_bounds μ hμ b _ ih
end BoundedTreewidthL1.OrderedSweepFlow

namespace BoundedTreewidthL1.OrderedReservation
attribute [local instance] Classical.decEq Classical.propDecidable
open MeasureTheory Set
open scoped BigOperators
variable {V : Type*} [Fintype V]

noncomputable def trueSet (ω : V → Bool) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => ω v = true)

def Carrier (M : ℝ) (F : V → ℝ) := {ω : V → Bool // 0 < (sweep M F).real {ω}}

noncomputable instance (M : ℝ) (F : V → ℝ) : Fintype (Carrier M F) := by
  unfold Carrier
  infer_instance

noncomputable def weight (M : ℝ) (F : V → ℝ) (ω : Carrier M F) : ℝ :=
  (sweep M F).real {ω.val}

lemma weight_pos
    {V : Type treewidthLevel1} [Fintype V]
    (M : ℝ) (F : V → ℝ) (ω : Carrier M F) : 0 < weight M F ω := ω.property

lemma exists_threshold (M : ℝ) (F : V → ℝ) (ω : Carrier M F) :
    ∃ t ∈ Icc (-M) M, thresholdLabels F t = ω.val := by
  have hp : 0 < (sweep M F).real {ω.val} := ω.property
  change 0 < ((volume.restrict (Icc (-M) M)).map (thresholdLabels F)).real {ω.val} at hp
  rw [map_measureReal_apply (measurable_thresholdLabels F) (measurableSet_singleton ω.val),
    measureReal_restrict_apply ((measurable_thresholdLabels F) (measurableSet_singleton ω.val))] at hp
  have hn : ((thresholdLabels F ⁻¹' {ω.val}) ∩ Icc (-M) M).Nonempty := by
    by_contra he
    rw [Set.not_nonempty_iff_eq_empty.mp he, measureReal_empty] at hp
    exact (lt_irrefl 0) hp
  obtain ⟨t, ht, hm⟩ := hn
  exact ⟨t, hm, ht⟩

lemma thresholds_nested (F : V → ℝ) (s t : ℝ) (hst : s ≤ t) :
    trueSet (thresholdLabels F t) ⊆ trueSet (thresholdLabels F s) := by
  classical
  intro v hv
  simp only [trueSet, Finset.mem_filter, Finset.mem_univ, true_and,
    thresholdLabels, decide_eq_true_eq] at hv ⊢
  exact hst.trans_lt hv

lemma carrier_nested (M : ℝ) (F : V → ℝ) (a b : Carrier M F) :
    trueSet a.val ⊆ trueSet b.val ∨ trueSet b.val ⊆ trueSet a.val := by
  obtain ⟨s, _, hs⟩ := exists_threshold M F a
  obtain ⟨t, _, ht⟩ := exists_threshold M F b
  rw [← hs, ← ht]
  rcases le_total s t with h | h
  · exact Or.inr (thresholds_nested F s t h)
  · exact Or.inl (thresholds_nested F t s h)

lemma trueSet_injective : Function.Injective (trueSet (V := V)) := by
  classical
  intro a b h
  funext v
  have he : v ∈ trueSet a ↔ v ∈ trueSet b := by rw [h]
  simp only [trueSet, Finset.mem_filter, Finset.mem_univ, true_and] at he
  cases ha : a v <;> cases hb : b v <;> simp_all

lemma rank_injective (M : ℝ) (F : V → ℝ) :
    Function.Injective (fun a : Carrier M F => (trueSet a.val).card) := by
  intro a b h
  apply Subtype.ext
  apply trueSet_injective
  rcases carrier_nested M F a b with hab | hba
  · exact Finset.eq_of_subset_of_card_le hab h.ge
  · exact (Finset.eq_of_subset_of_card_le hba h.le).symm

noncomputable instance carrierOrder (M : ℝ) (F : V → ℝ) : LinearOrder (Carrier M F) :=
  LinearOrder.lift' (fun a => (trueSet a.val).card) (rank_injective M F)

lemma labels_monotone (M : ℝ) (F : V → ℝ) (v : V) :
    Monotone (fun a : Carrier M F => a.val v) := by
  intro a b hab
  change (trueSet a.val).card ≤ (trueSet b.val).card at hab
  have hs : trueSet a.val ⊆ trueSet b.val := by
    rcases carrier_nested M F a b with h | h
    · exact h
    · exact (Finset.eq_of_subset_of_card_le h hab).symm.subset
  intro ha
  have hm : v ∈ trueSet a.val := by simp [trueSet, ha]
  simpa only [trueSet, Finset.mem_filter, Finset.mem_univ, true_and] using hs hm

noncomputable def traceRank (M : ℝ) (F : V → ℝ) (P : Finset V) (ω : Carrier M F) : ℕ :=
  (P.filter (fun v => ω.val v = true)).card

lemma traceRank_monotone (M : ℝ) (F : V → ℝ) (P : Finset V) :
    Monotone (traceRank M F P) := by
  classical
  intro a b hab
  apply Finset.card_le_card
  intro v hv
  simp only [Finset.mem_filter] at hv ⊢
  exact ⟨hv.1, labels_monotone M F v hab hv.2⟩

lemma traceRank_fiber (M : ℝ) (F : V → ℝ) (P : Finset V)
    (a b : Carrier M F) : traceRank M F P a = traceRank M F P b ↔
      ∀ v : P, a.val v = b.val v := by
  classical
  constructor
  · intro h
    have hn : (P.filter (fun v => a.val v = true)) ⊆ (P.filter (fun v => b.val v = true)) ∨
        (P.filter (fun v => b.val v = true)) ⊆ (P.filter (fun v => a.val v = true)) := by
      rcases le_total a b with hab | hba
      · left; intro v hv; simp only [Finset.mem_filter] at hv ⊢
        exact ⟨hv.1, labels_monotone M F v hab hv.2⟩
      · right; intro v hv; simp only [Finset.mem_filter] at hv ⊢
        exact ⟨hv.1, labels_monotone M F v hba hv.2⟩
    have he : (P.filter (fun v => a.val v = true)) = (P.filter (fun v => b.val v = true)) := by
      rcases hn with hab | hba
      · exact Finset.eq_of_subset_of_card_le hab h.ge
      · exact (Finset.eq_of_subset_of_card_le hba h.le).symm
    intro v
    have hv : v.val ∈ P.filter (fun v => a.val v = true) ↔
        v.val ∈ P.filter (fun v => b.val v = true) := by rw [he]
    simp only [Finset.mem_filter, v.property, true_and] at hv
    cases ha : a.val v <;> cases hb : b.val v <;> simp_all
  · intro h
    unfold traceRank
    congr 1
    apply Finset.filter_congr
    intro v hv
    rw [h ⟨v,hv⟩]

lemma sum_carrier (M : ℝ) (F : V → ℝ) (g : (V → Bool) → ℝ) :
    (∑ a : Carrier M F, weight M F a * g a.val) =
      ∑ a : V → Bool, (sweep M F).real {a} * g a := by
  classical
  have he := Fintype.sum_subtype_add_sum_subtype
    (fun a : V → Bool => 0 < (sweep M F).real {a})
    (fun a => (sweep M F).real {a} * g a)
  have hz : (∑ a : {a : V → Bool // ¬0 < (sweep M F).real {a}},
      (sweep M F).real {a.val} * g a.val) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    have ha : (sweep M F).real {a.val} = 0 :=
      le_antisymm (le_of_not_gt a.property) measureReal_nonneg
    simp [ha]
  rw [hz, add_zero] at he
  exact he

lemma sum_event (M : ℝ) (F : V → ℝ) (p : (V → Bool) → Prop) :
    (∑ a : V → Bool, (sweep M F).real {a} * (if p a then 1 else 0)) =
      (sweep M F).real {a | p a} := by
  classical
  have h := sum_measureReal_singleton (μ := sweep M F) (Finset.univ.filter p)
  simpa only [Finset.sum_filter, Finset.coe_filter, Finset.coe_univ,
    Set.ofPred_mem_eq, Set.mem_univ, Finset.mem_univ, true_and, mul_ite, mul_one, mul_zero] using h

lemma label_mean (M : ℝ) (F : V → ℝ) (v : V) (hv : -M ≤ F v ∧ F v ≤ M) :
    OrderedSweepFlow.total (weight M F)
      (OrderedSweepFlow.labelReal (fun a : Carrier M F => a.val v)) = F v + M := by
  classical
  rw [OrderedSweepFlow.total]
  change (∑ a : Carrier M F, weight M F a * (if a.val v then 1 else 0)) = _
  rw [sum_carrier M F (fun a => if a v then 1 else 0)]
  trans (sweep M F).real {a | a v = true}
  · convert sum_event M F (fun a => a v = true) using 1
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    split_ifs <;> rfl
  · rw [sweep, map_measureReal_apply (measurable_thresholdLabels F)
      ((Set.toFinite _).measurableSet),
      measureReal_restrict_apply ((measurable_thresholdLabels F) ((Set.toFinite _).measurableSet))]
    have he : (thresholdLabels F ⁻¹' {a | a v = true}) ∩ Icc (-M) M = Ico (-M) (F v) := by
      ext t
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq,
        thresholdLabels, decide_eq_true_eq, Set.mem_Icc, Set.mem_Ico]
      constructor
      · rintro ⟨h, h₁, _⟩; exact ⟨h₁,h⟩
      · rintro ⟨h₁,h⟩; exact ⟨h,h₁,h.le.trans hv.2⟩
    rw [he, Real.volume_real_Ico_of_le hv.1]
    ring

end BoundedTreewidthL1.OrderedReservation

namespace BoundedTreewidthL1.OrderedReservation
attribute [local instance] Classical.decEq Classical.propDecidable
open MeasureTheory Set OrderedSweepFlow
open scoped BigOperators
variable {V : Type*} [Fintype V]

lemma total_weight (M : ℝ) (hM : 0 ≤ M) (F : V → ℝ) :
    total (weight M F) (fun _ => 1) = 2*M := by
  rw [total, sum_carrier M F (fun _ => 1)]
  simp only [mul_one]
  have he := sum_measureReal_singleton (μ := sweep M F) (Finset.univ : Finset (V → Bool))
  rw [he]
  simp only [Finset.coe_univ]
  rw [sweep, map_measureReal_apply (measurable_thresholdLabels F) MeasurableSet.univ]
  simp only [Set.preimage_univ, measureReal_restrict_apply_univ]
  rw [Real.volume_real_Icc_of_le (by linarith)]
  ring

/-- Explicit descending-reservation transport on the original sweep measure.
The chain may have any length, and testing and intermediate bags may repeat.
There is no width assumption or Markov-flow hypothesis. -/
theorem sweep_height_transport (M : ℝ) (hM : 0 ≤ M) (F : V → ℝ)
    (hF : ∀ v, -M ≤ F v ∧ F v ≤ M) (z : V) (P : Finset V)
    (bags : List (Finset V)) (p : Carrier M F → ℝ)
    (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1)
    (hptrace : ∀ a b, (∀ v : P, a.val v = b.val v) → p a = p b)
    (t : ℝ) (hlo : t ≤ F z + M) (hhi : t ≤ M - F z)
    (hgap : ∀ v ∈ P, t ≤ |F z - F v|) :
    t ≤ defect (weight M F)
      (execute (weight M F) (bags.map (traceRank M F))
        (labelReal (fun a => a.val z))) p := by
  let f := execute (weight M F) (bags.map (traceRank M F))
    (labelReal (fun a => a.val z))
  have hm : total (weight M F) f = F z + M := by
    rw [execute_total _ (weight_pos M F), label_mean M F z (hF z)]
  have hf : Monotone f := by
    apply execute_monotone _ (weight_pos M F)
    · intro b hb
      obtain ⟨Q,_,rfl⟩ := List.mem_map.mp hb
      exact traceRank_monotone M F Q
    · intro a b hab
      dsimp [labelReal]
      have hl := labels_monotone M F z hab
      by_cases ha : a.val z = true
      · have hb : b.val z = true := hl ha
        simp [ha, hb]
      · simp [ha]
        split_ifs <;> norm_num
  apply height_transport (weight M F) (weight_pos M F)
    (traceRank M F P) (traceRank_monotone M F P)
    (fun a (v : P) => a.val v) (fun v => labels_monotone M F v)
    (fun a b h => (traceRank_fiber M F P a b).mpr h)
    f p hf (execute_bounds _ (weight_pos M F) _ _ (labelReal_bounds _)) hp
    (fun a b h => hptrace a b ((traceRank_fiber M F P a b).mp h))
  · exact hm ▸ hlo
  · rw [total_weight M hM F, hm]
    linarith
  · intro v
    rw [hm, label_mean M F v (hF v)]
    simpa using hgap v v.property
end BoundedTreewidthL1.OrderedReservation

end OAI
