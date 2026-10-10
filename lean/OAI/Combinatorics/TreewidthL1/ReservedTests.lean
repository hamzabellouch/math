import OAI.Combinatorics.TreewidthL1.ReservedCoupling

namespace OAI

universe treewidthLevel1 treewidthLevel2

namespace BoundedTreewidthL1.ReservedTests
open MeasureTheory ExpandedParticleLaw ReservationCoupling ReservedKernel
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V ι : Type*} [Fintype V] [Fintype ι]

noncomputable def part (M : ℝ) (F : ι → V → ℝ) (i : ι) (q : Bool)
    (f p : State ι V → ℝ) : ℝ :=
  ∑ ω : V → Bool, weight M F (i,q,ω) *
    (f (i,q,ω)+p (i,q,ω)-2*f (i,q,ω)*p (i,q,ω))

lemma part_nonneg (M : ℝ) (F : ι → V → ℝ) (i : ι) (q : Bool)
    (f p : State ι V → ℝ) (hf : ∀ a, 0 ≤ f a ∧ f a ≤ 1)
    (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1) : 0 ≤ part M F i q f p := by
  apply Finset.sum_nonneg
  intro ω _
  apply mul_nonneg (weight_nonneg _ _ _)
  have h₁ := mul_nonneg (hf (i,q,ω)).1 (sub_nonneg.mpr (hp (i,q,ω)).2)
  have h₂ := mul_nonneg (hp (i,q,ω)).1 (sub_nonneg.mpr (hf (i,q,ω)).2)
  nlinarith

lemma sum_part (M : ℝ) (F : ι → V → ℝ) (f p : State ι V → ℝ) :
    (∑ i, ∑ q, part M F i q f p) = defect (weight M F) f p := by
  simp only [defect, part, Fintype.sum_prod_type]

lemma part_le (M : ℝ) (F : ι → V → ℝ) (i : ι) (q : Bool)
    (f p : State ι V → ℝ) (hf : ∀ a, 0 ≤ f a ∧ f a ≤ 1)
    (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1) : part M F i q f p ≤ defect (weight M F) f p := by
  rw [← sum_part]
  exact (Finset.single_le_sum (fun b _ => part_nonneg M F i b f p hf hp)
    (Finset.mem_univ q)).trans (Finset.single_le_sum
      (fun j _ => Finset.sum_nonneg (fun b _ => part_nonneg M F j b f p hf hp)) (Finset.mem_univ i))

lemma pair_part_le (M : ℝ) (F : ι → V → ℝ) (i j : ι) (hij : i ≠ j)
    (f p : State ι V → ℝ) (hf : ∀ a, 0 ≤ f a ∧ f a ≤ 1)
    (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1) :
    part M F i false f p + part M F j false f p ≤ defect (weight M F) f p := by
  rw [← sum_part]
  have hb k : part M F k false f p ≤ ∑ q, part M F k q f p :=
    Finset.single_le_sum (fun b _ => part_nonneg M F k b f p hf hp) (Finset.mem_univ _)
  apply (add_le_add (hb i) (hb j)).trans
  have he : (∑ k ∈ ({i,j} : Finset ι), ∑ q, part M F k q f p) =
      (∑ q, part M F i q f p) + ∑ q, part M F j q f p := by simp [hij]
  rw [← he]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun k _ _ => Finset.sum_nonneg (fun q _ => part_nonneg M F k q f p hf hp))

lemma part_eq
    {V : Type treewidthLevel1} {ι : Type treewidthLevel2} [Fintype V] [Fintype ι]
    (M : ℝ) (F : ι → V → ℝ) (i : ι) (f p : State ι V → ℝ) :
    part M F i false f p =
      OrderedSweepFlow.defect (OrderedReservation.weight M (F i))
        (fun a => f (lift M (F i) i a)) (fun a => p (lift M (F i) i a)) / 2 := by
  unfold part OrderedSweepFlow.defect
  have he := OrderedReservation.sum_carrier M (F i)
    (fun ω => f (i,false,ω)+p (i,false,ω)-2*f (i,false,ω)*p (i,false,ω))
  change (∑ ω : V → Bool, (sweep M (F i)).real {ω}/2 *
    (f (i,false,ω)+p (i,false,ω)-2*f (i,false,ω)*p (i,false,ω))) = _
  trans (∑ ω : V → Bool, (sweep M (F i)).real {ω} *
    (f (i,false,ω)+p (i,false,ω)-2*f (i,false,ω)*p (i,false,ω)))/2
  · rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro ω _
    ring
  · rw [← he]
    rfl

lemma departure_isCoupling (M : ℝ) (F : ι → V → ℝ) (P : Finset V) (i j : ι) :
    IsCoupling (weight M F) (weight M F) (departure M F P i j) := by
  obtain ⟨hn,hr,hc,ht,hk⟩ := departure_coupling M F P i j
  exact ⟨hn,hr,hc⟩

/-- The exact single OLD-particle height test for the real expanded departure
coupling. The suffix is the proved interval-resampling response. -/
theorem height_test (M : ℝ) (hM : 0 ≤ M) (F : ι → V → ℝ) (P : Finset V)
    (i j r : ι) (hir : r ≠ i) (hjr : r ≠ j)
    (hF : ∀ v, -M ≤ F r v ∧ F r v ≤ M) (z : V) (bags : List (Finset V))
    (f p : State ι V → ℝ) (hf : ∀ a, 0 ≤ f a ∧ f a ≤ 1) (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1)
    (hresponse : ∀ a : OrderedReservation.Carrier M (F r),
      f (lift M (F r) r a) = OrderedSweepFlow.execute (OrderedReservation.weight M (F r))
        (bags.map (OrderedReservation.traceRank M (F r)))
        (OrderedSweepFlow.labelReal (fun a => a.val z)) a)
    (t : ℝ) (hlo : t ≤ F r z + M) (hhi : t ≤ M - F r z)
    (hgap : ∀ v ∈ P, t ≤ |F r z - F r v|) :
    t/2 ≤ defect (weight M F) (action (weight M F) (departure M F P i j) f) p := by
  let q := action (weight M F) (departure M F P i j) p
  have hQ := departure_isCoupling M F P i j
  have hq (a : State ι V) : 0 ≤ q a ∧ q a ≤ 1 := action_bounds hQ p hp a
  have ht : ∀ a b : OrderedReservation.Carrier M (F r),
      (∀ v : P, a.val v = b.val v) → q (lift M (F r) r a) = q (lift M (F r) r b) := by
    intro a b hab
    dsimp [q]
    rw [departure_action_old M F P i j r hir hjr, departure_action_old M F P i j r hir hjr]
    apply OrderedSweepFlow.bath_const_fiber
    exact (OrderedReservation.traceRank_fiber M (F r) P a b).mpr hab
  have hl := OrderedReservation.sweep_height_transport M hM (F r) hF z P bags
    (fun a => q (lift M (F r) r a)) (fun a => hq _) ht t hlo hhi hgap
  have he : (fun a : OrderedReservation.Carrier M (F r) => f (lift M (F r) r a)) =
      OrderedSweepFlow.execute (OrderedReservation.weight M (F r))
        (bags.map (OrderedReservation.traceRank M (F r)))
        (OrderedSweepFlow.labelReal (fun a => a.val z)) := funext hresponse
  rw [transfer_defect hQ]
  have hs : (fun b a => departure M F P i j a b) = departure M F P i j := by
    funext b a
    exact departure_symmetric M F P i j a b
  rw [hs]
  apply le_trans _ (part_le M F r false f q hf hq)
  rw [part_eq, he]
  exact div_le_div_of_nonneg_right hl (by norm_num)

lemma sum_marginal_eval {A C : Type*} [Fintype A] [Fintype C]
    (key : A → C) (μ : A → ℝ) (g : C → ℝ) :
    (∑ a, μ a * g (key a)) = ∑ c, marginal key μ c * g c := by
  unfold marginal
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

lemma sweep_trace_marginal_eq (M : ℝ) (F H : V → ℝ) (P : Finset V)
    (h : ∀ v ∈ P, F v = H v) (b : P → Bool) :
    marginal (fun ω : V → Bool => fun v : P => ω v) (fun ω => (sweep M F).real {ω}) b =
    marginal (fun ω : V → Bool => fun v : P => ω v) (fun ω => (sweep M H).real {ω}) b := by
  unfold marginal
  rw [finite_event, finite_event]
  rw [sweep, sweep, map_measureReal_apply (measurable_thresholdLabels _) (Set.toFinite _).measurableSet,
    map_measureReal_apply (measurable_thresholdLabels _) (Set.toFinite _).measurableSet]
  congr 1
  ext t
  have he : (fun v : P => thresholdLabels F t v) = (fun v : P => thresholdLabels H t v) := by
    funext v
    simp [thresholdLabels, h v v.property]
  change ((fun v : P => thresholdLabels F t v) = b) ↔ ((fun v : P => thresholdLabels H t v) = b)
  rw [he]

noncomputable def traceAverage (M : ℝ) (F : ι → V → ℝ) (P : Finset V)
    (i j : ι) (p : State ι V → ℝ) (c : (ι × Bool) × (P → Bool)) : ℝ :=
  (∑ b, if (departureKey i j b, trace P b) = c then weight M F b * p b else 0) /
    marginal (fun a => (departureKey i j a, trace P a)) (weight M F) c

lemma action_average (M : ℝ) (F : ι → V → ℝ) (P : Finset V) (i j : ι)
    (p : State ι V → ℝ) (a : State ι V) (ha : weight M F a ≠ 0) :
    action (weight M F) (departure M F P i j) p a =
      traceAverage M F P i j p (departureKey i j a,trace P a) := by
  unfold departure
  rw [glue_action _ _ _ _ _ _ ha]
  unfold traceAverage
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> rfl

lemma fresh_keys
    {V : Type treewidthLevel1} {ι : Type treewidthLevel2} [Fintype V] [Fintype ι]
    (i j : ι) (hij : i ≠ j) (q : Bool) (ω : V → Bool) :
    departureKey i j (i,q,ω) = (i,q) ∧ departureKey i j (j,q,ω) = (i,q) := by
  simp [departureKey, hij]

lemma fresh_predictor_mean (M : ℝ) (F : ι → V → ℝ) (P : Finset V)
    (i j : ι) (hij : i ≠ j) (hbag : ∀ v ∈ P, F i v = F j v)
    (p : State ι V → ℝ) :
    (∑ ω : V → Bool, weight M F (i,false,ω) *
      action (weight M F) (departure M F P i j) p (i,false,ω)) =
    ∑ ω : V → Bool, weight M F (j,false,ω) *
      action (weight M F) (departure M F P i j) p (j,false,ω) := by
  let h (b : P → Bool) := traceAverage M F P i j p ((i,false),b)
  have he (r : ι) (hr : r = i ∨ r = j) :
      (∑ ω : V → Bool, weight M F (r,false,ω) *
        action (weight M F) (departure M F P i j) p (r,false,ω)) =
      (∑ ω : V → Bool, (sweep M (F r)).real {ω} * h (fun v : P => ω v))/2 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hz : weight M F (r,false,ω) = 0
    · have hz' : (sweep M (F r)).real {ω} = 0 := by simpa [weight] using hz
      simp [hz, hz']
    · rw [action_average M F P i j p _ hz]
      have hk : departureKey i j (r,false,ω) = (i,false) := by
        rcases hr with hr | hr
        · rw [hr]
          exact (fresh_keys i j hij _ ω).1
        · rw [hr]
          exact (fresh_keys i j hij _ ω).2
      simp only [hk, ]
      change ((sweep M (F r)).real {ω}/2) * h (fun v : P => ω v) = _
      ring
  rw [he i (Or.inl rfl), he j (Or.inr rfl)]
  congr 1
  rw [sum_marginal_eval (fun ω : V → Bool => fun v : P => ω v)
    (fun ω => (sweep M (F i)).real {ω}) h,
    sum_marginal_eval (fun ω : V → Bool => fun v : P => ω v)
      (fun ω => (sweep M (F j)).real {ω}) h]
  apply Finset.sum_congr rfl
  intro b _
  rw [sweep_trace_marginal_eq M (F i) (F j) P hbag]

lemma part_mean_bound (M : ℝ) (F : ι → V → ℝ) (i : ι)
    (f p : State ι V → ℝ) (hf : ∀ a, 0 ≤ f a ∧ f a ≤ 1) (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1) :
    |(∑ ω : V → Bool, weight M F (i,false,ω)*f (i,false,ω)) -
      ∑ ω : V → Bool, weight M F (i,false,ω)*p (i,false,ω)| ≤ part M F i false f p := by
  have hl : (∑ ω : V → Bool, weight M F (i,false,ω)*p (i,false,ω)) -
      (∑ ω : V → Bool, weight M F (i,false,ω)*f (i,false,ω)) ≤ part M F i false f p := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro ω _
    have h := mul_nonneg (weight_nonneg M F (i,false,ω))
      (mul_nonneg (hf (i,false,ω)).1 (sub_nonneg.mpr (hp (i,false,ω)).2))
    nlinarith
  have hr : (∑ ω : V → Bool, weight M F (i,false,ω)*f (i,false,ω)) -
      (∑ ω : V → Bool, weight M F (i,false,ω)*p (i,false,ω)) ≤ part M F i false f p := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro ω _
    have h := mul_nonneg (weight_nonneg M F (i,false,ω))
      (mul_nonneg (hp (i,false,ω)).1 (sub_nonneg.mpr (hf (i,false,ω)).2))
    nlinarith
  exact abs_le.mpr ⟨by linarith,hr⟩

/-- EXACT fresh pair departure test. Only equal bag values, distinct reserved
indices and the true per-particle suffix means are required. -/
theorem launch_test (M : ℝ) (F : ι → V → ℝ) (P : Finset V) (i j : ι)
    (hij : i ≠ j) (hbag : ∀ v ∈ P, F i v = F j v) (z : V)
    (f p : State ι V → ℝ) (hf : ∀ a, 0 ≤ f a ∧ f a ≤ 1) (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1)
    (hi : (∑ ω : V → Bool, weight M F (i,false,ω)*f (i,false,ω)) = (F i z + M)/2)
    (hj : (∑ ω : V → Bool, weight M F (j,false,ω)*f (j,false,ω)) = (F j z + M)/2) :
    |F i z - F j z|/2 ≤ defect (weight M F) (action (weight M F) (departure M F P i j) f) p := by
  let q := action (weight M F) (departure M F P i j) p
  have hQ := departure_isCoupling M F P i j
  have hq (a : State ι V) : 0 ≤ q a ∧ q a ≤ 1 := action_bounds hQ p hp a
  have hm := fresh_predictor_mean M F P i j hij hbag p
  have h₁ := part_mean_bound M F i f q hf hq
  have h₂ := part_mean_bound M F j f q hf hq
  rw [hi] at h₁
  rw [hj] at h₂
  have ha := abs_sub_le ((F i z + M)/2)
    (∑ ω : V → Bool, weight M F (i,false,ω)*q (i,false,ω)) ((F j z+M)/2)
  rw [abs_sub_comm (∑ ω : V → Bool, weight M F (i,false,ω)*q (i,false,ω))] at ha
  change (∑ ω : V → Bool, weight M F (i,false,ω)*q (i,false,ω)) =
    (∑ ω : V → Bool, weight M F (j,false,ω)*q (j,false,ω)) at hm
  rw [← hm] at h₂
  have hab : |F i z - F j z|/2 ≤ part M F i false f q + part M F j false f q := by
    have he : (F i z+M)/2 - (F j z+M)/2 = (F i z-F j z)/2 := by ring
    rw [he, abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)] at ha
    exact ha.trans (add_le_add h₁ h₂)
  rw [transfer_defect hQ]
  have hs : (fun b a => departure M F P i j a b) = departure M F P i j := by
    funext b a
    exact departure_symmetric M F P i j a b
  rw [hs]
  exact hab.trans (pair_part_le M F i j hij f q hf hq)

end BoundedTreewidthL1.ReservedTests

namespace BoundedTreewidthL1.ReservedSuffix
open ExpandedParticleLaw ReservationCoupling ReservedKernel
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V ι : Type*} [Fintype V] [Fintype ι]

/-- The actual parent departure followed by the actual child incoming update. -/
noncomputable def edge (M : ℝ) (F H : ι → V → ℝ) (P Q : Finset V)
    (i j : ι) (C : Finset ι) : State ι V → State ι V → ℝ :=
  ExpandedParticleKernel.compose (weight M F) (departure M F P i j) (incoming M F H Q C)

lemma edge_coupling (M : ℝ) (F H : ι → V → ℝ) (P Q : Finset V) (i j : ι) (C : Finset ι)
    (hret : ∀ r ∈ C, F r = H r) (htrace : particleTrace M F Q = particleTrace M H Q) :
    IsCoupling (weight M F) (weight M H) (edge M F H P Q i j C) := by
  obtain ⟨hd, hdr, hdc, _, _⟩ := departure_coupling M F P i j
  obtain ⟨hi, hir, hic, _, _⟩ := incoming_coupling M F H Q C hret htrace
  obtain ⟨hn,hr,hc⟩ := ExpandedParticleKernel.compose_coupling (weight M F) (weight M F)
    (weight M H) (departure M F P i j) (incoming M F H Q C)
    (weight_nonneg M F) (weight_nonneg M F) (weight_nonneg M H) hd hi hdr hdc hir hic
  exact ⟨hn,hr,hc⟩

lemma edge_restrict (M : ℝ) (F H : ι → V → ℝ) (P Q : Finset V) (i j r : ι) (C : Finset ι)
    (hir : r ≠ i) (hjr : r ≠ j) (hrC : r ∈ C)
    (hret : ∀ r ∈ C, F r = H r) (htrace : particleTrace M F Q = particleTrace M H Q)
    (a : OrderedReservation.Carrier M (F r)) (f : State ι V → ℝ) :
    action (weight M F) (edge M F H P Q i j C) f (lift M (F r) r a) =
      OrderedSweepFlow.bath (OrderedReservation.weight M (F r))
        (OrderedReservation.traceRank M (F r) P) (fun b => f (lift M (F r) r b)) a := by
  rw [edge, action_compose, departure_action_old M F P i j r hir hjr]
  congr 1
  funext b
  exact incoming_action_retained M F H Q C hret htrace _ hrC
    (ne_of_gt (div_pos b.property (by norm_num))) f

noncomputable def kernels (M : ℝ) (F : ℕ → ι → V → ℝ) (P : ℕ → Finset V)
    (fresh₁ fresh₂ : ℕ → ι) (C : ℕ → Finset ι) (t : ℕ) :=
  edge M (F t) (F (t+1)) (P t) (P (t+1)) (fresh₁ t) (fresh₂ t) (C t)

noncomputable def bags (P : ℕ → Finset V) (t n : ℕ) : List (Finset V) :=
  (List.range n).map (fun s => P (t+s))

lemma bags_succ
    {V : Type treewidthLevel1} [Fintype V]
    (P : ℕ → Finset V) (t n : ℕ) :
    bags P t (n+1) = P t :: bags P (t+1) n := by
  simp only [bags, List.range_succ_eq_map, List.map_cons, Nat.add_zero, List.map_map]
  congr 2
  funext s
  simp only [Function.comp_apply]
  congr 1
  omega

/-- A reserved old particle's true suffix response is exactly a sequence of
ordered interval heat baths. All transitions are the expanded preparation ones. -/
theorem response_restrict (M : ℝ) (F : ℕ → ι → V → ℝ) (P : ℕ → Finset V)
    (fresh₁ fresh₂ : ℕ → ι) (C : ℕ → Finset ι)
    (hret : ∀ s r, r ∈ C s → F s r = F (s+1) r)
    (htrace : ∀ s, particleTrace M (F s) (P (s+1)) = particleTrace M (F (s+1)) (P (s+1)))
    (t n : ℕ) (r : ι) (G : V → ℝ)
    (hfixed : ∀ s, t ≤ s → s ≤ t+n → F s r = G)
    (hkeep : ∀ s, t ≤ s → s < t+n → r ∈ C s ∧ r ≠ fresh₁ s ∧ r ≠ fresh₂ s)
    (z : V) (a : OrderedReservation.Carrier M G) :
    response (fun s => weight M (F s)) (kernels M F P fresh₁ fresh₂ C) t n
      (fun b => if label b z then 1 else 0) (lift M G r a) =
      OrderedSweepFlow.execute (OrderedReservation.weight M G)
        ((bags P t n).map (OrderedReservation.traceRank M G))
        (OrderedSweepFlow.labelReal (fun b => b.val z)) a := by
  induction n generalizing t a with
  | zero => rfl
  | succ n ih =>
    have ht : F t r = G := hfixed t le_rfl (by omega)
    subst G
    have hk := hkeep t le_rfl (by omega)
    change action (weight M (F t)) (kernels M F P fresh₁ fresh₂ C t)
      (response (fun s => weight M (F s)) (kernels M F P fresh₁ fresh₂ C) (t+1) n
        (fun b => if label b z then 1 else 0)) (lift M (F t r) r a) = _
    unfold kernels
    rw [edge_restrict M (F t) (F (t+1)) (P t) (P (t+1)) (fresh₁ t) (fresh₂ t) r (C t)
      hk.2.1 hk.2.2 hk.1 (hret t) (htrace t)]
    have hfixed' : ∀ s, t+1 ≤ s → s ≤ (t+1)+n → F s r = F t r := by
      intro s hs hs'
      exact hfixed s (by omega) (by omega)
    have hkeep' : ∀ s, t+1 ≤ s → s < (t+1)+n → r ∈ C s ∧ r ≠ fresh₁ s ∧ r ≠ fresh₂ s := by
      intro s hs hs'
      exact hkeep s (by omega) (by omega)
    rw [bags_succ, List.map_cons, OrderedSweepFlow.execute]
    congr 1
    funext b
    exact ih (t+1) hfixed' hkeep' b
end BoundedTreewidthL1.ReservedSuffix

end OAI
