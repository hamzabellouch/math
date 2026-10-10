import OAI.Combinatorics.TreewidthL1.MarkovProduct

namespace OAI

universe treewidthLevel1 treewidthLevel2

namespace BoundedTreewidthL1.ExpandedChain
open scoped BigOperators
open ReservationCoupling
attribute [local instance] Classical.decEq Classical.propDecidable
variable {A : Type*} [Fintype A]

noncomputable def past (μ : ℕ → A → ℝ) (Q : ℕ → A → A → ℝ) (f : A → ℝ) : ℕ → A → ℝ
  | 0 => f
  | n+1 => action (μ (n+1)) (fun b a => Q n a b) (past μ Q f n)

lemma past_bounds (μ : ℕ → A → ℝ) (Q : ℕ → A → A → ℝ)
    (hQ : ∀ n, IsCoupling (μ n) (μ (n+1)) (Q n)) (f : A → ℝ)
    (hf : ∀ a, 0 ≤ f a ∧ f a ≤ 1) (n : ℕ) :
    ∀ a, 0 ≤ past μ Q f n a ∧ past μ Q f n a ≤ 1 := by
  induction n with
  | zero => exact hf
  | succ n ih => exact action_bounds (hQ n).symm _ ih

lemma sum_fiber_mul {B : Type*} [Fintype B] (k : A → B) (w : A → ℝ) (g : B → ℝ) :
    (∑ a, w a * g (k a)) = ∑ b, (∑ a, if k a = b then w a else 0) * g b := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [ite_mul, zero_mul]
  simp

/-- Conditional past means in the actual finite product law, not an assumed
Markov response. This identity includes all zero-mass states. -/
lemma weighted_terminal (μ : ℕ → A → ℝ) (Q : ℕ → A → A → ℝ)
    (hQ : ∀ n, IsCoupling (μ n) (μ (n+1)) (Q n)) (f : A → ℝ) (n : ℕ) (b : A) :
    (∑ x : MarkovProduct.History (fun _ => A) n,
      if x (Fin.last n) = b then
        MarkovProduct.weight (fun _ => A) (μ 0) (MarkovProduct.couplingKernel (fun _ => A) μ Q) n x * f (x 0)
      else 0) = μ n b * past μ Q f n b := by
  induction n generalizing b with
  | zero =>
    let e : A ≃ (Fin 1 → A) := (Equiv.piUnique (fun _ : Fin 1 => A)).symm
    rw [← e.sum_comp]
    simp [e, MarkovProduct.weight, past, Equiv.piUnique, uniqueElim]
  | succ n ih =>
    rw [MarkovProduct.sum_history_snoc (fun _ => A)]
    simp only [Fin.snoc_last, MarkovProduct.weight_snoc]
    have hzero (x : Fin (n+1) → A) (c : A) :
        @Fin.snoc (n+1) (fun _ : Fin (n+2) => A) x c 0 = x 0 := by
      exact @Fin.snoc_castSucc (n+1) (fun _ => A) c x 0
    simp only [hzero]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    let w : (Fin (n+1) → A) → ℝ := fun x =>
      MarkovProduct.weight (fun _ => A) (μ 0) (MarkovProduct.couplingKernel (fun _ => A) μ Q) n x * f (x 0)
    have he : (∑ x : Fin (n+1) → A,
      MarkovProduct.weight (fun _ => A) (μ 0) (MarkovProduct.couplingKernel (fun _ => A) μ Q) n x *
      MarkovProduct.couplingKernel (fun _ => A) μ Q n (x (Fin.last n)) b * f (x 0)) =
       ∑ a, μ n a * past μ Q f n a * MarkovProduct.couplingKernel (fun _ => A) μ Q n a b := by
      trans ∑ x, w x * MarkovProduct.couplingKernel (fun _ => A) μ Q n (x (Fin.last n)) b
      · apply Finset.sum_congr rfl
        intro x _
        dsimp [w]
        ring
      · rw [sum_fiber_mul (fun x : Fin (n+1) → A => x (Fin.last n)) w
          (fun a => MarkovProduct.couplingKernel (fun _ => A) μ Q n a b)]
        apply Finset.sum_congr rfl
        intro a _
        rw [show (∑ x, if x (Fin.last n) = a then w x else 0) = μ n a * past μ Q f n a from ih a]
    rw [he]
    change _ = μ (n+1) b * action (μ (n+1)) (fun b a => Q n a b) (past μ Q f n) b
    rw [weighted_action (hQ n).symm]
    apply Finset.sum_congr rfl
    intro a _
    rw [mul_right_comm, MarkovProduct.couplingKernel_balance (fun _ => A) μ Q
      (fun n => (hQ n).nonneg) (fun n => (hQ n).row)]

/-- Separation of endpoint labels in the genuine product density is precisely
its conditional-predictor defect. The identity holds for all bounded or unbounded
real endpoint observables; bounds are needed only for the subsequent tests. -/
theorem endpoint_defect (μ : ℕ → A → ℝ) (Q : ℕ → A → A → ℝ)
    (hQ : ∀ n, IsCoupling (μ n) (μ (n+1)) (Q n)) (f g : A → ℝ) (n : ℕ) :
    (∑ x : MarkovProduct.History (fun _ => A) n,
      MarkovProduct.weight (fun _ => A) (μ 0) (MarkovProduct.couplingKernel (fun _ => A) μ Q) n x *
        (f (x 0) + g (x (Fin.last n)) - 2*f (x 0)*g (x (Fin.last n)))) =
      defect (μ n) g (past μ Q f n) := by
  let w : (Fin (n+1) → A) → ℝ := MarkovProduct.weight (fun _ => A) (μ 0)
    (MarkovProduct.couplingKernel (fun _ => A) μ Q) n
  have hm (b : A) : (∑ x : Fin (n+1) → A, if x (Fin.last n) = b then w x else 0) = μ n b := by
    exact (MarkovProduct.terminal_marginal (fun _ => A) (μ 0)
      (MarkovProduct.couplingKernel (fun _ => A) μ Q) n b).trans
        (MarkovProduct.coupling_forward (fun _ => A) μ Q
          (fun n => (hQ n).nonneg) (fun n => (hQ n).row) (fun n => (hQ n).col) n b)
  have hw (b : A) : (∑ x : Fin (n+1) → A, if x (Fin.last n) = b then w x * f (x 0) else 0) =
      μ n b * past μ Q f n b := weighted_terminal μ Q hQ f n b
  have he : (∑ x : Fin (n+1) → A, w x * f (x 0)) =
      ∑ b, μ n b * past μ Q f n b := by
    simpa only [mul_one, hw] using
      (sum_fiber_mul (fun x : Fin (n+1) → A => x (Fin.last n)) (fun x => w x*f (x 0)) (fun _ => (1:ℝ)))
  have hg : (∑ x : Fin (n+1) → A, w x * g (x (Fin.last n))) = ∑ b, μ n b*g b := by
    simpa only [hm] using (sum_fiber_mul (fun x : Fin (n+1) → A => x (Fin.last n)) w g)
  have hfg : (∑ x : Fin (n+1) → A, w x * f (x 0) * g (x (Fin.last n))) =
      ∑ b, μ n b * past μ Q f n b * g b := by
    simpa only [hw] using (sum_fiber_mul (fun x : Fin (n+1) → A => x (Fin.last n))
      (fun x => w x*f (x 0)) g)
  change (∑ x, w x * _) = _
  calc
    _ = (∑ x, w x*f (x 0)) + (∑ x, w x*g (x (Fin.last n))) -
        2*(∑ x, w x*f (x 0)*g (x (Fin.last n))) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by
      rw [he,hg,hfg]
      unfold defect
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro b _
      ring

lemma response_past (μ : ℕ → A → ℝ) (Q : ℕ → A → A → ℝ)
    (hQ : ∀ n, IsCoupling (μ n) (μ (n+1)) (Q n)) (f g : A → ℝ) (t n : ℕ) :
    defect (μ t) (response μ Q t n g) (past μ Q f t) =
      defect (μ (t+n)) g (past μ Q f (t+n)) := by
  induction n generalizing t with
  | zero => simp only [response, Nat.add_zero]
  | succ n ih =>
    change defect (μ t) (action (μ t) (Q t) (response μ Q (t+1) n g)) (past μ Q f t) = _
    rw [transfer_defect (hQ t)]
    change defect (μ (t+1)) (response μ Q (t+1) n g) (past μ Q f (t+1)) = _
    rw [ih, show (t+1)+n = t+(n+1) by omega]

/-- One may test at ANY interior location: past and future are the honest
conditional responses of the already constructed product law. -/
theorem endpoint_defect_at (μ : ℕ → A → ℝ) (Q : ℕ → A → A → ℝ)
    (hQ : ∀ n, IsCoupling (μ n) (μ (n+1)) (Q n)) (f g : A → ℝ) (t n : ℕ) (ht : t ≤ n) :
    (∑ x : MarkovProduct.History (fun _ => A) n,
      MarkovProduct.weight (fun _ => A) (μ 0) (MarkovProduct.couplingKernel (fun _ => A) μ Q) n x *
        (f (x 0) + g (x (Fin.last n)) - 2*f (x 0)*g (x (Fin.last n)))) =
      defect (μ t) (response μ Q t (n-t) g) (past μ Q f t) := by
  rw [endpoint_defect μ Q hQ, response_past μ Q hQ, Nat.add_sub_of_le ht]
end BoundedTreewidthL1.ExpandedChain

namespace BoundedTreewidthL1.ReservedSuffix
open ExpandedParticleLaw ReservationCoupling ReservedKernel
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V ι : Type*} [Fintype V] [Fintype ι]

/-- Local version: the arbitrary past of the path is immaterial. Only the true
reserved suffix edges are prescribed. -/
theorem response_restrict_local (M : ℝ) (F : ℕ → ι → V → ℝ) (P : ℕ → Finset V)
    (fresh₁ fresh₂ : ℕ → ι) (C : ℕ → Finset ι)
    (Q : ℕ → State ι V → State ι V → ℝ)
    (t n : ℕ) (r : ι) (G : V → ℝ)
    (hQ : ∀ s, t ≤ s → s < t+n → Q s = kernels M F P fresh₁ fresh₂ C s)
    (hret : ∀ s, t ≤ s → s < t+n → ∀ r ∈ C s, F s r = F (s+1) r)
    (htrace : ∀ s, t ≤ s → s < t+n →
      particleTrace M (F s) (P (s+1)) = particleTrace M (F (s+1)) (P (s+1)))
    (hfixed : ∀ s, t ≤ s → s ≤ t+n → F s r = G)
    (hkeep : ∀ s, t ≤ s → s < t+n → r ∈ C s ∧ r ≠ fresh₁ s ∧ r ≠ fresh₂ s)
    (z : V) (a : OrderedReservation.Carrier M G) :
    response (fun s => weight M (F s)) Q t n
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
    change action (weight M (F t)) (Q t)
      (response (fun s => weight M (F s)) Q (t+1) n
        (fun b => if label b z then 1 else 0)) (lift M (F t r) r a) = _
    rw [hQ t le_rfl (by omega)]
    unfold kernels
    rw [edge_restrict M (F t) (F (t+1)) (P t) (P (t+1)) (fresh₁ t) (fresh₂ t) r (C t)
      hk.2.1 hk.2.2 hk.1 (hret t le_rfl (by omega)) (htrace t le_rfl (by omega))]
    rw [bags_succ, List.map_cons, OrderedSweepFlow.execute]
    congr 1
    funext b
    apply ih (t+1)
    · intro s hs hs'; exact hQ s (by omega) (by omega)
    · intro s hs hs'; exact hret s (by omega) (by omega)
    · intro s hs hs'; exact htrace s (by omega) (by omega)
    · intro s hs hs'; exact hfixed s (by omega) (by omega)
    · intro s hs hs'; exact hkeep s (by omega) (by omega)

lemma ordered_mean
    {V : Type treewidthLevel1} {ι : Type treewidthLevel2} [Fintype V] [Fintype ι]
    (M : ℝ) (_ : 0 ≤ M) (G : V → ℝ)
    (hG : ∀ v, -M ≤ G v ∧ G v ≤ M) (r : ι) (z : V)
    (bags : List (Finset V)) (f : State ι V → ℝ)
    (hres : ∀ a : OrderedReservation.Carrier M G, f (lift M G r a) =
      OrderedSweepFlow.execute (OrderedReservation.weight M G)
        (bags.map (OrderedReservation.traceRank M G))
        (OrderedSweepFlow.labelReal (fun a => a.val z)) a) :
    (∑ ω : V → Bool, (sweep M G).real {ω}/2 * f (r,false,ω)) = (G z+M)/2 := by
  have he := OrderedReservation.sum_carrier M G (fun ω => f (r,false,ω))
  have he' : (∑ a : OrderedReservation.Carrier M G,
      OrderedReservation.weight M G a * f (lift M G r a)) =
      ∑ ω : V → Bool, (sweep M G).real {ω}*f (r,false,ω) := he
  have hr := congrArg (fun h : OrderedReservation.Carrier M G → ℝ =>
      ∑ a, OrderedReservation.weight M G a * h a) (funext hres)
  rw [he'] at hr
  change _ = OrderedSweepFlow.total (OrderedReservation.weight M G)
    (OrderedSweepFlow.execute (OrderedReservation.weight M G)
      (bags.map (OrderedReservation.traceRank M G))
      (OrderedSweepFlow.labelReal (fun a => a.val z))) at hr
  rw [OrderedSweepFlow.execute_total _ (OrderedReservation.weight_pos M G),
    OrderedReservation.label_mean M G z (hG z)] at hr
  calc
    _ = (∑ ω : V → Bool, (sweep M G).real {ω}*f (r,false,ω))/2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro ω _
      ring
    _ = _ := by rw [hr]
end BoundedTreewidthL1.ReservedSuffix

namespace BoundedTreewidthL1.ReservedSuffix
open ExpandedParticleLaw ReservationCoupling ReservedKernel
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V ι : Type*} [Fintype V] [Fintype ι]

lemma incoming_response_restrict (M : ℝ) (F : ℕ → ι → V → ℝ) (P : ℕ → Finset V)
    (fresh₁ fresh₂ : ℕ → ι) (C : ℕ → Finset ι)
    (Q : ℕ → State ι V → State ι V → ℝ) (t n : ℕ) (r : ι)
    (hQ : ∀ s, t+1 ≤ s → s < t+1+n → Q s = kernels M F P fresh₁ fresh₂ C s)
    (hret : ∀ s, t ≤ s → s < t+1+n → ∀ r ∈ C s, F s r = F (s+1) r)
    (htrace : ∀ s, t ≤ s → s < t+1+n →
      particleTrace M (F s) (P (s+1)) = particleTrace M (F (s+1)) (P (s+1)))
    (hfixed : ∀ s, t ≤ s → s ≤ t+1+n → F s r = F t r)
    (hr : r ∈ C t)
    (hkeep : ∀ s, t+1 ≤ s → s < t+1+n → r ∈ C s ∧ r ≠ fresh₁ s ∧ r ≠ fresh₂ s)
    (z : V) (a : OrderedReservation.Carrier M (F t r)) :
    action (weight M (F t)) (incoming M (F t) (F (t+1)) (P (t+1)) (C t))
      (response (fun s => weight M (F s)) Q (t+1) n
        (fun b => if label b z then 1 else 0)) (lift M (F t r) r a) =
      OrderedSweepFlow.execute (OrderedReservation.weight M (F t r))
        ((bags P (t+1) n).map (OrderedReservation.traceRank M (F t r)))
        (OrderedSweepFlow.labelReal (fun b => b.val z)) a := by
  rw [incoming_action_retained M (F t) (F (t+1)) (P (t+1)) (C t)
    (hret t le_rfl (by omega)) (htrace t le_rfl (by omega)) _ hr
    (ne_of_gt (div_pos a.property (by norm_num)))]
  apply response_restrict_local M F P fresh₁ fresh₂ C Q (t+1) n r (F t r) hQ
  · intro s hs hs'; exact hret s (by omega) hs'
  · intro s hs hs'; exact htrace s (by omega) hs'
  · intro s hs hs'; exact hfixed s (by omega) hs'
  · exact hkeep
end BoundedTreewidthL1.ReservedSuffix

namespace BoundedTreewidthL1.ExpandedPathTests
open ExpandedParticleLaw ReservationCoupling ReservedKernel ReservedSuffix ExpandedChain
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V ι : Type*} [Fintype V] [Fintype ι]

noncomputable def distance (M : ℝ) (F : ℕ → ι → V → ℝ)
    (Q : ℕ → State ι V → State ι V → ℝ) (n : ℕ) (y z : V) : ℝ :=
  ∑ x : Fin (n+1) → State ι V,
    MarkovProduct.weight (fun _ => State ι V) (weight M (F 0))
      (MarkovProduct.couplingKernel (fun _ => State ι V) (fun s => weight M (F s)) Q) n x *
      (if label (x 0) y = label (x (Fin.last n)) z then 0 else 1)

lemma distance_at (M : ℝ) (F : ℕ → ι → V → ℝ)
    (Q : ℕ → State ι V → State ι V → ℝ)
    (hQ : ∀ s, IsCoupling (weight M (F s)) (weight M (F (s+1))) (Q s))
    (t n : ℕ) (y z : V) :
    distance M F Q (t+(n+1)) y z =
      defect (weight M (F t)) (action (weight M (F t)) (Q t)
        (response (fun s => weight M (F s)) Q (t+1) n (fun b => if label b z then 1 else 0)))
        (past (fun s => weight M (F s)) Q (fun b => if label b y then 1 else 0) t) := by
  have he := endpoint_defect_at (fun s => weight M (F s)) Q hQ
    (fun b => if label b y then 1 else 0) (fun b => if label b z then 1 else 0)
    t (t+(n+1)) (by omega)
  rw [Nat.add_sub_cancel_left, response] at he
  rw [← he]
  unfold distance
  apply Finset.sum_congr rfl
  intro x _
  cases hy : label (x 0) y <;> cases hz : label (x (Fin.last (t+(n+1)))) z <;> norm_num [hy,hz]

/-- Height test for the ACTUAL arbitrarily prefixed product path. All suffix
transport and both past/future responses are derived from its couplings. -/
theorem height_test (M : ℝ) (hM : 0 ≤ M) (F : ℕ → ι → V → ℝ) (P : ℕ → Finset V)
    (fresh₁ fresh₂ : ℕ → ι) (C : ℕ → Finset ι)
    (Q : ℕ → State ι V → State ι V → ℝ)
    (hQ : ∀ s, IsCoupling (weight M (F s)) (weight M (F (s+1))) (Q s))
    (t n : ℕ) (r : ι)
    (hEq : ∀ s, t ≤ s → s < t+1+n → Q s = kernels M F P fresh₁ fresh₂ C s)
    (hret : ∀ s, t ≤ s → s < t+1+n → ∀ r ∈ C s, F s r = F (s+1) r)
    (htrace : ∀ s, t ≤ s → s < t+1+n →
      particleTrace M (F s) (P (s+1)) = particleTrace M (F (s+1)) (P (s+1)))
    (hfixed : ∀ s, t ≤ s → s ≤ t+1+n → F s r = F t r)
    (hkeep : ∀ s, t ≤ s → s < t+1+n → r ∈ C s ∧ r ≠ fresh₁ s ∧ r ≠ fresh₂ s)
    (hF : ∀ v, -M ≤ F t r v ∧ F t r v ≤ M) (y z : V)
    (ε : ℝ) (hlo : ε ≤ F t r z + M) (hhi : ε ≤ M-F t r z)
    (hgap : ∀ v ∈ P t, ε ≤ |F t r z-F t r v|) :
    ε/2 ≤ distance M F Q (t+(n+1)) y z := by
  rw [distance_at M F Q hQ t n y z, hEq t le_rfl (by omega)]
  unfold kernels edge
  rw [action_compose]
  have hb (v : V) (a : State ι V) : 0 ≤ (if label a v then (1:ℝ) else 0) ∧
      (if label a v then (1:ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  have hin : IsCoupling (weight M (F t)) (weight M (F (t+1)))
      (incoming M (F t) (F (t+1)) (P (t+1)) (C t)) := by
    obtain ⟨hn,hr,hc,_,_⟩ := incoming_coupling M (F t) (F (t+1)) (P (t+1)) (C t)
      (hret t le_rfl (by omega)) (htrace t le_rfl (by omega))
    exact ⟨hn,hr,hc⟩
  have hk := hkeep t le_rfl (by omega)
  apply ReservedTests.height_test M hM (F t) (P t) (fresh₁ t) (fresh₂ t) r
    hk.2.1 hk.2.2 hF z (bags P (t+1) n)
  · exact action_bounds hin _ (response_bounds _ Q hQ (t+1) n _ (hb z))
  · exact past_bounds _ Q hQ _ (hb y) t
  · intro a
    apply incoming_response_restrict M F P fresh₁ fresh₂ C Q t n r
      (fun s hs hs' => hEq s (by omega) hs') hret htrace hfixed hk.1
      (fun s hs hs' => hkeep s (by omega) hs') z a
  · exact hlo
  · exact hhi
  · exact hgap
/-- Fresh-pair test on the actual product law with an arbitrary prefix. -/
theorem launch_test (M : ℝ) (hM : 0 ≤ M) (F : ℕ → ι → V → ℝ) (P : ℕ → Finset V)
    (fresh₁ fresh₂ : ℕ → ι) (C : ℕ → Finset ι)
    (Q : ℕ → State ι V → State ι V → ℝ)
    (hQ : ∀ s, IsCoupling (weight M (F s)) (weight M (F (s+1))) (Q s))
    (t n : ℕ) (hij : fresh₁ t ≠ fresh₂ t)
    (hbag : ∀ v ∈ P t, F t (fresh₁ t) v = F t (fresh₂ t) v)
    (hEq : ∀ s, t ≤ s → s < t+1+n → Q s = kernels M F P fresh₁ fresh₂ C s)
    (hret : ∀ s, t ≤ s → s < t+1+n → ∀ r ∈ C s, F s r = F (s+1) r)
    (htrace : ∀ s, t ≤ s → s < t+1+n →
      particleTrace M (F s) (P (s+1)) = particleTrace M (F (s+1)) (P (s+1)))
    (hfixed : ∀ r ∈ ({fresh₁ t, fresh₂ t} : Finset ι),
      ∀ s, t ≤ s → s ≤ t+1+n → F s r = F t r)
    (hinit : fresh₁ t ∈ C t ∧ fresh₂ t ∈ C t)
    (hkeep : ∀ r ∈ ({fresh₁ t, fresh₂ t} : Finset ι),
      ∀ s, t+1 ≤ s → s < t+1+n → r ∈ C s ∧ r ≠ fresh₁ s ∧ r ≠ fresh₂ s)
    (hF : ∀ r ∈ ({fresh₁ t, fresh₂ t} : Finset ι), ∀ v, -M ≤ F t r v ∧ F t r v ≤ M)
    (y z : V) :
    |F t (fresh₁ t) z - F t (fresh₂ t) z|/2 ≤ distance M F Q (t+(n+1)) y z := by
  rw [distance_at M F Q hQ t n y z, hEq t le_rfl (by omega)]
  unfold kernels edge
  rw [action_compose]
  have hb (v : V) (a : State ι V) : 0 ≤ (if label a v then (1:ℝ) else 0) ∧
      (if label a v then (1:ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  have hin : IsCoupling (weight M (F t)) (weight M (F (t+1)))
      (incoming M (F t) (F (t+1)) (P (t+1)) (C t)) := by
    obtain ⟨hn,hr,hc,_,_⟩ := incoming_coupling M (F t) (F (t+1)) (P (t+1)) (C t)
      (hret t le_rfl (by omega)) (htrace t le_rfl (by omega))
    exact ⟨hn,hr,hc⟩
  have hm (r : ι) (hr : r ∈ ({fresh₁ t, fresh₂ t} : Finset ι)) (hc : r ∈ C t) :
      (∑ ω : V → Bool, weight M (F t) (r,false,ω) *
        action (weight M (F t)) (incoming M (F t) (F (t+1)) (P (t+1)) (C t))
          (response (fun s => weight M (F s)) Q (t+1) n
            (fun b => if label b z then 1 else 0)) (r,false,ω)) = (F t r z+M)/2 := by
    apply ordered_mean M hM (F t r) (hF r hr) r z (bags P (t+1) n)
    intro a
    exact incoming_response_restrict M F P fresh₁ fresh₂ C Q t n r
      (fun s hs hs' => hEq s (by omega) hs') hret htrace (hfixed r hr) hc (hkeep r hr) z a
  apply ReservedTests.launch_test M (F t) (P t) (fresh₁ t) (fresh₂ t) hij hbag z
  · exact action_bounds hin _ (response_bounds _ Q hQ (t+1) n _ (hb z))
  · exact past_bounds _ Q hQ _ (hb y) t
  · exact hm _ (by simp) hinit.1
  · exact hm _ (by simp) hinit.2
end BoundedTreewidthL1.ExpandedPathTests

end OAI
