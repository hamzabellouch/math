import OAI.Combinatorics.TreewidthL1.OrderedSweep

namespace OAI

universe treewidthLevel1 treewidthLevel2

namespace BoundedTreewidthL1.ReservationCoupling
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable
variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

structure IsCoupling (μ : A → ℝ) (ν : B → ℝ) (Q : A → B → ℝ) : Prop where
  nonneg : ∀ a b, 0 ≤ Q a b
  row : ∀ a, ∑ b, Q a b = μ a
  col : ∀ b, ∑ a, Q a b = ν b

noncomputable def action (μ : A → ℝ) (Q : A → B → ℝ) (f : B → ℝ) (a : A) : ℝ :=
  (∑ b, Q a b * f b) / μ a

noncomputable def total (μ f : A → ℝ) : ℝ := ∑ a, μ a * f a
noncomputable def defect (μ f p : A → ℝ) : ℝ :=
  ∑ a, μ a * (f a + p a - 2*f a*p a)

lemma IsCoupling.symm {μ : A → ℝ} {ν : B → ℝ} {Q : A → B → ℝ}
    (h : IsCoupling μ ν Q) : IsCoupling ν μ (fun b a => Q a b) :=
  ⟨fun b a => h.nonneg a b, h.col, h.row⟩

lemma IsCoupling.left_nonneg {μ : A → ℝ} {ν : B → ℝ} {Q : A → B → ℝ}
    (h : IsCoupling μ ν Q) (a : A) : 0 ≤ μ a := by
  rw [← h.row]
  exact Finset.sum_nonneg (fun b _ => h.nonneg a b)

lemma IsCoupling.right_nonneg {μ : A → ℝ} {ν : B → ℝ} {Q : A → B → ℝ}
    (h : IsCoupling μ ν Q) (b : B) : 0 ≤ ν b := h.symm.left_nonneg b

lemma IsCoupling.row_zero {μ : A → ℝ} {ν : B → ℝ} {Q : A → B → ℝ}
    (h : IsCoupling μ ν Q) (a : A) (ha : μ a = 0) (b : B) : Q a b = 0 := by
  have hr := h.row a
  rw [ha] at hr
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => h.nonneg a x)).mp hr b (Finset.mem_univ _)

lemma weighted_action {μ : A → ℝ} {ν : B → ℝ} {Q : A → B → ℝ}
    (h : IsCoupling μ ν Q) (f : B → ℝ) (a : A) :
    μ a * action μ Q f a = ∑ b, Q a b * f b := by
  by_cases ha : μ a = 0
  · simp [action, ha, h.row_zero a ha]
  · unfold action
    field_simp

lemma action_bounds {μ : A → ℝ} {ν : B → ℝ} {Q : A → B → ℝ}
    (h : IsCoupling μ ν Q) (f : B → ℝ) (hf : ∀ b, 0 ≤ f b ∧ f b ≤ 1) (a : A) :
    0 ≤ action μ Q f a ∧ action μ Q f a ≤ 1 := by
  have hn : 0 ≤ ∑ b, Q a b * f b :=
    Finset.sum_nonneg (fun b _ => mul_nonneg (h.nonneg a b) (hf b).1)
  have hl : (∑ b, Q a b * f b) ≤ μ a := by
    rw [← h.row a]
    apply Finset.sum_le_sum
    intro b _
    simpa using mul_le_mul_of_nonneg_left (hf b).2 (h.nonneg a b)
  refine ⟨div_nonneg hn (h.left_nonneg a), ?_⟩
  by_cases ha : μ a = 0
  · simp [action, ha]
  · exact (div_le_one (lt_of_le_of_ne (h.left_nonneg a) (Ne.symm ha))).mpr hl

lemma action_total {μ : A → ℝ} {ν : B → ℝ} {Q : A → B → ℝ}
    (h : IsCoupling μ ν Q) (f : B → ℝ) : total μ (action μ Q f) = total ν f := by
  unfold total
  simp_rw [weighted_action h]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, h.col]

lemma action_adjoint {μ : A → ℝ} {ν : B → ℝ} {Q : A → B → ℝ}
    (h : IsCoupling μ ν Q) (f : B → ℝ) (p : A → ℝ) :
    total μ (fun a => p a * action μ Q f a) =
      total ν (fun b => f b * action ν (fun b a => Q a b) p b) := by
  unfold total
  conv_lhs =>
    arg 2; ext a
    rw [← mul_assoc, mul_right_comm, weighted_action h, Finset.sum_mul]
  conv_rhs =>
    arg 2; ext b
    rw [← mul_assoc, mul_right_comm, weighted_action h.symm, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma defect_form (μ f p : A → ℝ) :
    defect μ f p = total μ f + total μ p - 2*total μ (fun a => p a*f a) := by
  unfold defect total
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma defect_nonneg (μ f p : A → ℝ) (hμ : ∀ a, 0 ≤ μ a)
    (hf : ∀ a, 0 ≤ f a ∧ f a ≤ 1) (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1) :
    0 ≤ defect μ f p := by
  apply Finset.sum_nonneg
  intro a _
  apply mul_nonneg (hμ a)
  have h₁ := mul_nonneg (hf a).1 (sub_nonneg.mpr (hp a).2)
  have h₂ := mul_nonneg (hp a).1 (sub_nonneg.mpr (hf a).2)
  nlinarith

/-- Move one true finite Markov transition from the endpoint response to the
past predictor. This does not lose any mass, even with zero-probability states. -/
theorem transfer_defect {μ : A → ℝ} {ν : B → ℝ} {Q : A → B → ℝ}
    (h : IsCoupling μ ν Q) (f : B → ℝ) (p : A → ℝ) :
    defect μ (action μ Q f) p = defect ν f (action ν (fun b a => Q a b) p) := by
  rw [defect_form, defect_form, action_total h, action_total h.symm,
    action_adjoint h f p]
  congr 1
  congr 1
  unfold total
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Responses through a constant finite state space, with time-dependent laws. -/
noncomputable def response (μ : ℕ → A → ℝ) (Q : ℕ → A → A → ℝ)
    (t : ℕ) : ℕ → (A → ℝ) → (A → ℝ)
  | 0, f => f
  | n+1, f => action (μ t) (Q t) (response μ Q (t+1) n f)

lemma response_bounds (μ : ℕ → A → ℝ) (Q : ℕ → A → A → ℝ)
    (hQ : ∀ t, IsCoupling (μ t) (μ (t+1)) (Q t)) (t n : ℕ) (f : A → ℝ)
    (hf : ∀ a, 0 ≤ f a ∧ f a ≤ 1) :
    ∀ a, 0 ≤ response μ Q t n f a ∧ response μ Q t n f a ≤ 1 := by
  induction n generalizing t with
  | zero => exact hf
  | succ n ih => exact action_bounds (hQ t) _ (ih (t+1))

lemma response_total (μ : ℕ → A → ℝ) (Q : ℕ → A → A → ℝ)
    (hQ : ∀ t, IsCoupling (μ t) (μ (t+1)) (Q t)) (t n : ℕ) (f : A → ℝ) :
    total (μ t) (response μ Q t n f) = total (μ (t+n)) f := by
  induction n generalizing t with
  | zero => simp [response]
  | succ n ih =>
    change total (μ t) (action (μ t) (Q t) _) = _
    rw [action_total (hQ t), ih]
    congr 2
    omega
end BoundedTreewidthL1.ReservationCoupling

namespace BoundedTreewidthL1.ReservedKernel
open MeasureTheory ExpandedParticleLaw ReservationCoupling
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V ι : Type*} [Fintype V] [Fintype ι]

noncomputable def lift (M : ℝ) (F : V → ℝ) (i : ι) (a : OrderedReservation.Carrier M F) : State ι V :=
  (i,false,a.val)

lemma glue_action {A B C : Type*} [Fintype A] [Fintype B]
    (key : A → C) (key' : B → C) (μ : A → ℝ) (ν : B → ℝ) (f : B → ℝ)
    (a : A) (ha : μ a ≠ 0) :
    action μ (glueWeights key key' μ ν) f a =
    (∑ b, if key' b = key a then ν b*f b else 0) / marginal key μ (key a) := by
  unfold action
  have he : (∑ b, glueWeights key key' μ ν a b * f b) =
      μ a * (∑ b, if key' b = key a then ν b*f b else 0) / marginal key μ (key a) := by
    rw [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro b _
    unfold glueWeights
    by_cases h : key' b = key a
    · simp only [h, ↓reduceIte]
      ring
    · simp [h, Ne.symm h]
  rw [he]
  field_simp

lemma old_key
    {V : Type treewidthLevel1} {ι : Type treewidthLevel2} [Fintype V] [Fintype ι]
    (i j r : ι) (q : Bool) (hir : r ≠ i) (hjr : r ≠ j)
    (x : State ι V) : departureKey i j x = (r,q) ↔ x.1 = r ∧ x.2.1 = q := by
  unfold departureKey
  simp only [Prod.mk.injEq]
  by_cases hx : x.1 = j
  · simp [hx, Ne.symm hir, Ne.symm hjr]
  · simp [hx]

lemma sum_old_key (i j r : ι) (q : Bool) (hir : r ≠ i) (hjr : r ≠ j)
    (f : State ι V → ℝ) :
    (∑ x, if departureKey i j x = (r,q) then f x else 0) =
      ∑ ω : V → Bool, f (r,q,ω) := by
  simp_rw [old_key i j r q hir hjr]
  simp only [Fintype.sum_prod_type]
  cases q <;> simp [ite_and]

lemma positive_trace_sum (M : ℝ) (F : V → ℝ) (P : Finset V)
    (a : OrderedReservation.Carrier M F) (g : (V → Bool) → ℝ) :
    (∑ ω : V → Bool, if (fun v : P => ω v) = (fun v : P => a.val v) then
      (sweep M F).real {ω} * g ω else 0) =
    ∑ b : OrderedReservation.Carrier M F,
      if OrderedReservation.traceRank M F P b = OrderedReservation.traceRank M F P a then
        OrderedReservation.weight M F b * g b.val else 0 := by
  have he := OrderedReservation.sum_carrier M F
    (fun ω => if (fun v : P => ω v) = (fun v : P => a.val v) then g ω else 0)
  simp only [mul_ite,mul_zero] at he
  rw [← he]
  apply Finset.sum_congr rfl
  intro b _
  have hb : ((fun v : P => b.val v) = (fun v : P => a.val v)) ↔
      OrderedReservation.traceRank M F P b = OrderedReservation.traceRank M F P a := by
    rw [OrderedReservation.traceRank_fiber]
    exact funext_iff
  simp only [hb]

lemma departure_old_numerator (M : ℝ) (F : ι → V → ℝ) (P : Finset V) (i j r : ι)
    (hir : r ≠ i) (hjr : r ≠ j) (a : OrderedReservation.Carrier M (F r))
    (f : State ι V → ℝ) :
    (∑ b, if (departureKey i j b, trace P b) =
      (departureKey i j (lift M (F r) r a), trace P (lift M (F r) r a)) then
      weight M F b * f b else 0) =
    (∑ b : OrderedReservation.Carrier M (F r),
      if OrderedReservation.traceRank M (F r) P b = OrderedReservation.traceRank M (F r) P a then
        OrderedReservation.weight M (F r) b * f (lift M (F r) r b) else 0)/2 := by
  have hk : departureKey i j (lift M (F r) r a) = (r,false) := by simp [departureKey,lift,hjr]
  simp only [hk, Prod.mk.injEq, ite_and]
  rw [sum_old_key i j r false hir hjr]
  change (∑ ω : V → Bool, if (fun v : P => ω v) = (fun v : P => a.val v) then
    (sweep M (F r)).real {ω} / 2 * f (r,false,ω) else 0) = _
  have he := positive_trace_sum M (F r) P a (fun ω => f (r,false,ω))
  erw [← he, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> ring

/-- Restrict the ACTUAL departure kernel to an old retained particle: it is
exactly the monotone interval heat bath, not an arbitrary common submeasure. -/
theorem departure_action_old (M : ℝ) (F : ι → V → ℝ) (P : Finset V) (i j r : ι)
    (hir : r ≠ i) (hjr : r ≠ j) (a : OrderedReservation.Carrier M (F r))
    (f : State ι V → ℝ) :
    action (weight M F) (departure M F P i j) f (lift M (F r) r a) =
      OrderedSweepFlow.bath (OrderedReservation.weight M (F r))
        (OrderedReservation.traceRank M (F r) P) (fun b => f (lift M (F r) r b)) a := by
  have hpos : 0 < weight M F (lift M (F r) r a) :=
    div_pos a.property (by norm_num)
  unfold departure
  rw [glue_action _ _ _ _ _ _ hpos.ne']
  trans ((∑ b : OrderedReservation.Carrier M (F r),
      if OrderedReservation.traceRank M (F r) P b = OrderedReservation.traceRank M (F r) P a then
        OrderedReservation.weight M (F r) b * f (lift M (F r) r b) else 0)/2) /
      marginal (fun x => (departureKey i j x, trace P x)) (weight M F)
        (departureKey i j (lift M (F r) r a), trace P (lift M (F r) r a))
  · congr 1
    convert departure_old_numerator M F P i j r hir hjr a f using 1
    apply Finset.sum_congr rfl
    intro b _
    split_ifs <;> rfl
  have hd := departure_old_numerator M F P i j r hir hjr a (fun _ => 1)
  simp only [mul_one] at hd
  have hd' : marginal (fun x : State ι V => (departureKey i j x, trace P x)) (weight M F)
      (departureKey i j (lift M (F r) r a), trace P (lift M (F r) r a)) =
      (∑ b : OrderedReservation.Carrier M (F r),
        if OrderedReservation.traceRank M (F r) P b = OrderedReservation.traceRank M (F r) P a then
          OrderedReservation.weight M (F r) b else 0)/2 := by
    unfold marginal
    convert hd using 1
    apply Finset.sum_congr rfl
    intro b _
    split_ifs <;> rfl
  rw [hd']
  unfold OrderedSweepFlow.bath OrderedSweepFlow.mass OrderedSweepFlow.fiber
  simp only [Finset.sum_filter]
  ring

/-- A retained incoming particle is copied exactly, as a whole global cut. -/
lemma incoming_action_retained (M : ℝ) (F H : ι → V → ℝ) (P : Finset V) (C : Finset ι)
    (hret : ∀ i ∈ C, F i = H i) (htrace : particleTrace M F P = particleTrace M H P)
    (a : State ι V) (ha : a.1 ∈ C) (hpos : weight M F a ≠ 0) (f : State ι V → ℝ) :
    action (weight M F) (incoming M F H P C) f a = f a := by
  obtain ⟨hn, hr, hc, ht, hs⟩ := incoming_coupling M F H P C hret htrace
  unfold action
  have he : (∑ b, incoming M F H P C a b * f b) = weight M F a * f a := by
    rw [← hr a, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : a = b
    · rw [← hb]
    · rw [hs a b ha hb, zero_mul, zero_mul]
  rw [he, mul_div_cancel_left₀ _ hpos]

lemma action_compose {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (μ : A → ℝ) (ν : B → ℝ) (J : A → B → ℝ) (K : B → C → ℝ) (f : C → ℝ) :
    action μ (ExpandedParticleKernel.compose ν J K) f = action μ J (action ν K f) := by
  funext a
  unfold action ExpandedParticleKernel.compose
  congr 1
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [← mul_div_assoc, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro c _
  ring

/-- Departure is symmetric: predictors are reheated by the same kernel. -/
lemma departure_symmetric (M : ℝ) (F : ι → V → ℝ) (P : Finset V) (i j : ι) :
    ∀ a b, departure M F P i j a b = departure M F P i j b a := by
  intro a b
  unfold departure glueWeights
  by_cases h : (departureKey i j a, trace P a) = (departureKey i j b, trace P b)
  · simp only [h, ↓reduceIte]
    ring
  · simp [h, Ne.symm h]

end BoundedTreewidthL1.ReservedKernel

end OAI
