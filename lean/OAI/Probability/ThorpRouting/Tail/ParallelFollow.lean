import Mathlib
import OAI.Probability.ThorpRouting.Tail.PriorPaths

namespace OAI

namespace ThorpNine.Tail

namespace Thorp
open scoped BigOperators
open Filter
section ParallelButterfly
variable {α B : Type*} [Fintype α] [DecidableEq α] [Fintype B] [DecidableEq B] {d : ℕ}
omit [DecidableEq B] in
lemma parallel_entropy (pre : α ≃ B × Card d) (ω : B × SwitchIndex d → Bool) (S : Finset α) :
    (∑ i : B × SwitchIndex d,
      if (parallelUsers pre ω i).1 ∈ S ∧ (parallelUsers pre ω i).2 ∈ S then (1:ℝ) else 0) ≤
      (S.card : ℝ) * Real.log S.card / (2 * Real.log 2) := by
  classical
  rw [Fintype.sum_prod_type]
  calc
    _ ≤ ∑ b : B, (blockMarks pre S b).card * Real.log (blockMarks pre S b).card / (2*Real.log 2) := by
      apply Finset.sum_le_sum
      intro b _
      simpa only [←mem_blockMarks,parallelUsers] using
        marked_switch_entropy_bound d (decodeButterfly d (fun i => ω (b,i))) (blockMarks pre S b)
    _ ≤ ∑ b : B, (blockMarks pre S b).card * Real.log S.card / (2*Real.log 2) := by
      apply Finset.sum_le_sum
      intro b _
      by_cases hz : (blockMarks pre S b).card = 0
      · simp [hz]
      · apply div_le_div_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hz)
          (by exact_mod_cast card_blockMarks_le pre S b)
    _ = _ := by rw [←Finset.sum_div,←Finset.sum_mul,←Nat.cast_sum,sum_card_blockMarks]

noncomputable def parallelFollow (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x : α) (k : α → QueryTree (B × SwitchIndex d)) : QueryTree (B × SwitchIndex d) :=
  QueryTree.followPath d (fun i => ((pre x).1,i)) (pre x).2 (fun y => k (post ((pre x).1,y)))

omit [Fintype α] [DecidableEq α] [Fintype B] [DecidableEq B] in
lemma parallelFollow_succeeds (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x : α) (k : α → QueryTree (B × SwitchIndex d)) (ω : B × SwitchIndex d → Bool) :
    (parallelFollow pre post x k).succeeds ω = (k (relabeledPerm pre post ω x)).succeeds ω := by
  exact QueryTree.followPath_succeeds _ _ _ _ _

omit [Fintype α] [DecidableEq α] [Fintype B] [DecidableEq B] in
lemma parallelFollow_raw_charge (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x : α) (k : α → QueryTree (B × SwitchIndex d)) (ω : B × SwitchIndex d → Bool) :
    (parallelFollow pre post x k).charge ω = (k (relabeledPerm pre post ω x)).charge ω := by
  exact QueryTree.followPath_raw_charge _ _ _ _ _

omit [Fintype α] [DecidableEq α] [Fintype B] in
lemma parallelFollow_stale_charge (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x : α) (k : α → QueryTree (B × SwitchIndex d)) (R : Finset (B × SwitchIndex d))
    (ω : B × SwitchIndex d → Bool) :
    (parallelFollow pre post x k).staleCharge R ω =
      (k (relabeledPerm pre post ω x)).staleCharge (R ∪ parallelPath pre ω x) ω := by
  exact QueryTree.followPath_stale_charge _ _ _ _ _ _

noncomputable def closingDomain (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x y : α) : Finset (B × SwitchIndex d) :=
  (routeDomain d (pre x).2 (post.symm y).2).image (fun i => ((pre x).1,i))

def closingValue (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x y : α) (i : B × SwitchIndex d) : Bool := routeValue d (pre x).2 (post.symm y).2 i.2

omit [Fintype α] [DecidableEq α] [Fintype B] [DecidableEq B] in
lemma relabeled_endpoint_pair (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (ω : B × SwitchIndex d → Bool) (x y : α) :
    relabeledPerm pre post ω x = y ↔
      (pre x).1 = (post.symm y).1 ∧
      butterflyPerm d (decodeButterfly d (fun i => ω ((pre x).1,i))) (pre x).2 = (post.symm y).2 := by
  change post ((pre x).1,_) = y ↔ _
  rw [←post.eq_symm_apply,Prod.mk.injEq]

omit [Fintype α] [DecidableEq α] [Fintype B] in
lemma relabeled_endpoint_iff (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (ω : B × SwitchIndex d → Bool) (x y : α) :
    relabeledPerm pre post ω x = y ↔
      (pre x).1 = (post.symm y).1 ∧
        ∀ i ∈ closingDomain pre post x y, ω i = closingValue pre post x y i := by
  classical
  rw [relabeled_endpoint_pair,butterfly_endpoint_iff]
  simp only [closingDomain,Finset.forall_mem_image,closingValue]

omit [Fintype α] [DecidableEq α] [Fintype B] in
lemma closingDomain_eq (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (ω : B × SwitchIndex d → Bool) (x y : α) (h : relabeledPerm pre post ω x = y) :
    closingDomain pre post x y = parallelPath pre ω x := by
  rw [closingDomain,parallelPath,(relabeled_endpoint_pair _ _ _ _ _).mp h |>.2]

noncomputable def parallelClose (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x y : α) (k : QueryTree (B × SwitchIndex d)) : QueryTree (B × SwitchIndex d) :=
  if (pre x).1 = (post.symm y).1 then
    QueryTree.forceList (closingDomain pre post x y).toList (closingValue pre post x y) k
  else QueryTree.reject

omit [Fintype α] in
lemma parallelClose_succeeds (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x y : α) (k : QueryTree (B × SwitchIndex d)) (ω : B × SwitchIndex d → Bool) :
    (parallelClose pre post x y k).succeeds ω =
      if relabeledPerm pre post ω x = y then k.succeeds ω else false := by
  classical
  simp only [relabeled_endpoint_iff,parallelClose]
  by_cases hb : (pre x).1 = (post.symm y).1
  · rw [ite_eq_left hb,QueryTree.forceList_succeeds]
    simp only [Finset.mem_toList,hb,true_and]
  · simp [hb,QueryTree.succeeds]

omit [Fintype α] [DecidableEq α] [Fintype B] in
lemma parallelClose_raw_charge (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x y : α) (k : QueryTree (B × SwitchIndex d)) (ω : B × SwitchIndex d → Bool)
    (h : relabeledPerm pre post ω x = y) :
    (parallelClose pre post x y k).charge ω = k.charge ω + d := by
  have hh := (relabeled_endpoint_iff _ _ _ _ _).mp h
  rw [parallelClose,ite_eq_left hh.1,QueryTree.forceList_raw_charge _ _ _ _
    (by simpa only [Finset.mem_toList] using hh.2),Finset.length_toList,
    closingDomain_eq _ _ _ _ _ h,card_parallelPath]

omit [Fintype α] [DecidableEq α] [Fintype B] in
lemma parallelClose_fresh_charge (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x y : α) (k : QueryTree (B × SwitchIndex d)) (R : Finset (B × SwitchIndex d))
    (ω : B × SwitchIndex d → Bool) (h : relabeledPerm pre post ω x = y) :
    (parallelClose pre post x y k).freshCharge R ω =
      k.freshCharge (R ∪ parallelPath pre ω x) ω + (parallelPath pre ω x \ R).card := by
  have hh := (relabeled_endpoint_iff _ _ _ _ _).mp h
  rw [parallelClose,ite_eq_left hh.1,QueryTree.forceList_charge _ _ _ _ _
    (by simpa only [Finset.mem_toList] using hh.2),Finset.toList_toFinset,
    closingDomain_eq _ _ _ _ _ h]

omit [Fintype α] [DecidableEq α] [Fintype B] in
lemma parallelClose_stale_charge (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x y : α) (k : QueryTree (B × SwitchIndex d)) (R : Finset (B × SwitchIndex d))
    (ω : B × SwitchIndex d → Bool) (h : relabeledPerm pre post ω x = y) :
    (parallelClose pre post x y k).staleCharge R ω =
      k.staleCharge (R ∪ parallelPath pre ω x) ω + (parallelPath pre ω x ∩ R).card := by
  have h₀ := QueryTree.fresh_add_stale (parallelClose pre post x y k) R ω
  have h₁ := QueryTree.fresh_add_stale k (R ∪ parallelPath pre ω x) ω
  rw [parallelClose_raw_charge _ _ _ _ _ _ h,parallelClose_fresh_charge _ _ _ _ _ _ _ h] at h₀
  have h₂ : (parallelPath pre ω x \ R).card + (parallelPath pre ω x ∩ R).card = d := by
    rw [Finset.card_sdiff_add_card_inter,card_parallelPath]
  omega

noncomputable def parallelNetwork (pre : α ≃ B × Card d) (post : B × Card d ≃ α) :
    RoutingNetwork α (B × SwitchIndex d) d where
  perm := relabeledPerm pre post
  path := parallelPath pre
  users := parallelUsers pre
  users_ne := parallelUsers_ne pre
  mem_path := mem_parallelPath pre
  card_path := card_parallelPath pre
  entropy := parallel_entropy pre
  follow := parallelFollow pre post
  close := parallelClose pre post
  follow_succeeds := parallelFollow_succeeds pre post
  follow_raw_charge := parallelFollow_raw_charge pre post
  follow_stale_charge := parallelFollow_stale_charge pre post
  close_succeeds := parallelClose_succeeds pre post
  close_raw_charge := parallelClose_raw_charge pre post
  close_stale_charge := parallelClose_stale_charge pre post

lemma parallel_cycle_log_mgf (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (S : Finset α) (J : ℕ) (hJ : 0 < J) (q : ℝ) (hq : 1 ≤ q) :
    Real.log (finiteMean (fun ω : B × SwitchIndex d → Bool =>
      q^(Fintype.card (RoutingNetwork.SelectedCycle (relabeledPerm pre post ω) S)))) ≤
      (S.card : ℝ)/J * Real.log q + 2*q*S.card*Real.sqrt J / Real.sqrt ((2:ℝ)^d) := by
  exact (parallelNetwork pre post).butterfly_cycle_log_mgf S J hJ q hq

end ParallelButterfly

def cardSplit : (r s : ℕ) → Card (s+r) ≃ Card r × Card s
  | 0, s =>
    { toFun := fun x => ((fun i => Fin.elim0 i), x)
      invFun := fun x => x.2
      left_inv := fun _ => rfl
      right_inv := fun x => by
        apply Prod.ext
        · exact Subsingleton.elim _ _
        · rfl }
  | r+1, s =>
    { toFun := fun x => (Fin.cons (x 0) ((cardSplit r s (Fin.tail x)).1),
        (cardSplit r s (Fin.tail x)).2)
      invFun := fun x => Fin.cons (x.1 0) ((cardSplit r s).symm (Fin.tail x.1,x.2))
      left_inv := by
        intro x
        simp only [Fin.cons_zero, Fin.tail_cons, Prod.mk.eta, Equiv.symm_apply_apply, Fin.cons_self_tail]
      right_inv := by
        intro x
        simp only [Fin.cons_zero, Fin.tail_cons, Equiv.apply_symm_apply, Fin.cons_self_tail] }

def assembleBits : (r s : ℕ) → (Card r × SwitchIndex s → Bool) →
    (Card s × SwitchIndex r → Bool) → SwitchIndex (s+r) → Bool
  | 0, _, lo, _, i => lo ((fun j => Fin.elim0 j), i)
  | r+1, s, _, hi, Sum.inl y => hi ((cardSplit r s y).2,Sum.inl (cardSplit r s y).1)
  | r+1, s, lo, hi, Sum.inr (b,i) => assembleBits r s
      (fun j => lo (Fin.cons b j.1,j.2)) (fun j => hi (j.1,Sum.inr (b,j.2))) i

lemma butterfly_split (r s : ℕ) (lo : Card r × SwitchIndex s → Bool)
    (hi : Card s × SwitchIndex r → Bool) (x : Card (s+r)) :
    cardSplit r s (butterflyPerm (s+r) (decodeButterfly (s+r) (assembleBits r s lo hi)) x) =
      let y := cardSplit r s x
      let z := butterflyPerm s (decodeButterfly s (fun i => lo (y.1,i))) y.2
      (butterflyPerm r (decodeButterfly r (fun i => hi (z,i))) y.1,z) := by
  induction r with
  | zero =>
    apply Prod.ext
    · funext i
      exact Fin.elim0 i
    · rfl
  | succ r ih =>
    let lo' : Card r × SwitchIndex s → Bool := fun j => lo (Fin.cons (x 0) j.1,j.2)
    let hi' : Card s × SwitchIndex r → Bool := fun j => hi (j.1,Sum.inr (x 0,j.2))
    have hh := ih lo' hi' (Fin.tail x)
    let u := butterflyPerm (s+r) (decodeButterfly (s+r) (assembleBits r s lo' hi')) (Fin.tail x)
    let y := cardSplit r s (Fin.tail x)
    let z := butterflyPerm s (decodeButterfly s (fun i => lo' (y.1,i))) y.2
    let w := butterflyPerm r (decodeButterfly r (fun i => hi' (z,i))) y.1
    change cardSplit r s u = (w,z) at hh
    change ((Fin.cons (Bool.xor (x 0) (hi ((cardSplit r s u).2,Sum.inl (cardSplit r s u).1)))
        ((cardSplit r s u).1) : Card (r+1)), (cardSplit r s u).2) =
      ((Fin.cons (Bool.xor (x 0) (hi (z,Sum.inl w))) w : Card (r+1)),z)
    rw [hh]

def splitSwitch : (r s : ℕ) → SwitchIndex (s+r) ≃
    (Card r × SwitchIndex s) ⊕ (Card s × SwitchIndex r)
  | 0, _ =>
    { toFun := fun i => Sum.inl ((fun j => Fin.elim0 j),i)
      invFun := fun i => match i with
        | Sum.inl (_,j) => j
        | Sum.inr (_,j) => nomatch j
      left_inv := fun _ => rfl
      right_inv := by
        intro i
        rcases i with ⟨x,j⟩ | ⟨x,j⟩
        · exact congrArg Sum.inl (Prod.ext (Subsingleton.elim _ _) rfl)
        · exact Empty.elim j }
  | r+1, s =>
    { toFun := fun i => match i with
        | Sum.inl y => Sum.inr ((cardSplit r s y).2,Sum.inl (cardSplit r s y).1)
        | Sum.inr (b,j) => match splitSwitch r s j with
          | Sum.inl (p,j) => Sum.inl (Fin.cons b p,j)
          | Sum.inr (q,j) => Sum.inr (q,Sum.inr (b,j))
      invFun := fun i => match i with
        | Sum.inl (p,j) => Sum.inr (p 0,(splitSwitch r s).symm (Sum.inl (Fin.tail p,j)))
        | Sum.inr (q,Sum.inl p) => Sum.inl ((cardSplit r s).symm (p,q))
        | Sum.inr (q,Sum.inr (b,j)) => Sum.inr (b,(splitSwitch r s).symm (Sum.inr (q,j)))
      left_inv := by
        intro i
        rcases i with y | ⟨b,j⟩
        · dsimp only
          rw [Prod.mk.eta, Equiv.symm_apply_apply]
        · dsimp only
          cases hz : splitSwitch r s j with
          | inl z =>
            rcases z with ⟨p,k⟩
            simp only [Fin.cons_zero, Fin.tail_cons]
            rw [←hz,Equiv.symm_apply_apply]
          | inr z =>
            rcases z with ⟨q,k⟩
            dsimp only
            rw [←hz,Equiv.symm_apply_apply]
      right_inv := by
        intro i
        rcases i with ⟨p,j⟩ | ⟨q,j⟩
        · simp only [Equiv.apply_symm_apply, Fin.cons_self_tail]
        · rcases j with p | ⟨b,j⟩ <;> simp only [Equiv.apply_symm_apply] }

lemma assembleBits_eq (r s : ℕ) (lo : Card r × SwitchIndex s → Bool)
    (hi : Card s × SwitchIndex r → Bool) (i : SwitchIndex (s+r)) :
    assembleBits r s lo hi i = Sum.elim lo hi (splitSwitch r s i) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rcases i with y | ⟨b,j⟩
    · rfl
    · simp only [assembleBits,splitSwitch,Equiv.coe_fn_mk]
      rw [ih]
      cases splitSwitch r s j <;> rfl

def splitCoinEquiv (r s : ℕ) :
    ((Card r × SwitchIndex s → Bool) × (Card s × SwitchIndex r → Bool)) ≃
      (SwitchIndex (s+r) → Bool) :=
  (Equiv.sumArrowEquivProdArrow _ _ Bool).symm.trans
    (Equiv.arrowCongr (splitSwitch r s).symm (Equiv.refl Bool))

lemma splitCoinEquiv_apply (r s : ℕ) (lo : Card r × SwitchIndex s → Bool)
    (hi : Card s × SwitchIndex r → Bool) :
    splitCoinEquiv r s (lo,hi) = assembleBits r s lo hi := by
  funext i
  exact (assembleBits_eq r s lo hi i).symm

lemma finiteMean_prod {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω'] (f : Ω × Ω' → ℝ) :
    finiteMean f = finiteMean (fun x => finiteMean (fun y => f (x,y))) := by
  simp only [finiteMean, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    ←Finset.sum_div, div_div, mul_comm]

lemma finiteMean_split (r s : ℕ) (f : (SwitchIndex (s+r) → Bool) → ℝ) :
    finiteMean f = finiteMean (fun lo : Card r × SwitchIndex s → Bool =>
      finiteMean (fun hi : Card s × SwitchIndex r → Bool => f (assembleBits r s lo hi))) := by
  rw [finiteMean_equiv (splitCoinEquiv r s).symm]
  simp only [Equiv.symm_symm]
  rw [finiteMean_prod]
  apply finiteMean_congr
  intro lo
  apply finiteMean_congr
  intro hi
  rw [splitCoinEquiv_apply]

section PartiallyExposed
variable {α : Type*} {r s : ℕ}

def freshPre (pre : α ≃ Card (s+r)) (lo : Card r × SwitchIndex s → Bool) :
    α ≃ Card s × Card r :=
  ((pre.trans (cardSplit r s)).trans (parallelPerm lo)).trans (Equiv.prodComm _ _)

def freshPost (post : Card (s+r) ≃ α) : Card s × Card r ≃ α :=
  ((Equiv.prodComm _ _).trans (cardSplit r s).symm).trans post

lemma exposed_perm_eq (pre : α ≃ Card (s+r)) (post : Card (s+r) ≃ α)
    (lo : Card r × SwitchIndex s → Bool) (hi : Card s × SwitchIndex r → Bool) :
    (pre.trans (butterflyPerm (s+r) (decodeButterfly (s+r) (assembleBits r s lo hi)))).trans post =
      relabeledPerm (freshPre pre lo) (freshPost post) hi := by
  ext x
  simpa only [relabeledPerm, freshPre, freshPost, parallelPerm, Equiv.trans_apply,
    Equiv.coe_fn_mk, Equiv.prodComm_apply, Prod.swap, Equiv.symm_apply_apply] using
    congrArg (fun y => post ((cardSplit r s).symm y)) (butterfly_split r s lo hi (pre x))

lemma partially_exposed_cycle_log_mgf [Fintype α] [DecidableEq α]
    (pre : α ≃ Card (s+r)) (post : Card (s+r) ≃ α)
    (lo : Card r × SwitchIndex s → Bool) (S : Finset α)
    (J : ℕ) (hJ : 0 < J) (q : ℝ) (hq : 1 ≤ q) :
    Real.log (finiteMean (fun hi : Card s × SwitchIndex r → Bool =>
      q^(Fintype.card (RoutingNetwork.SelectedCycle
        ((pre.trans (butterflyPerm (s+r)
          (decodeButterfly (s+r) (assembleBits r s lo hi)))).trans post) S)))) ≤
      (S.card : ℝ)/J * Real.log q + 2*q*S.card*Real.sqrt J / Real.sqrt ((2:ℝ)^r) := by
  simp only [exposed_perm_eq]
  exact parallel_cycle_log_mgf (freshPre pre lo) (freshPost post) S J hJ q hq

end PartiallyExposed

lemma inclusionMoment_eq {α Ω : Type*} [DecidableEq α] [Fintype Ω]
    (F : Ω → Finset α) (S : Finset α) :
    inclusionMoment F S = finiteMean (fun ω => if S ⊆ F ω then (1:ℝ) else 0) := by
  unfold inclusionMoment
  apply finiteMean_congr
  intro ω
  split_ifs <;> rfl

lemma finiteMean_bool (f : Bool → ℝ) : finiteMean f = (f false+f true)/2 := by
  simp only [finiteMean, Fintype.sum_bool, Fintype.card_bool, Nat.cast_ofNat]
  ring

lemma finiteMean_const {Ω : Type*} [Fintype Ω] [Nonempty Ω] (c : ℝ) :
    finiteMean (fun _ : Ω => c) = c := by
  simp only [finiteMean,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  exact mul_div_cancel_left₀ c (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

lemma finiteMean_pi_prod {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*}
    [∀ i, Fintype (Ω i)] (f : (i : ι) → Ω i → ℝ) :
    finiteMean (fun ω : (i : ι) → Ω i => ∏ i, f i (ω i)) = ∏ i, finiteMean (f i) := by
  simp only [finiteMean,←Fintype.prod_sum,Fintype.card_pi,Nat.cast_prod,Finset.prod_div_distrib]

section ParallelFairLayer
variable {β : Type*} [Fintype β] [DecidableEq β]

def pairLayer (ξ : β → Bool) : Equiv.Perm (Bool × β) where
  toFun x := (Bool.xor x.1 (ξ x.2),x.2)
  invFun x := (Bool.xor x.1 (ξ x.2),x.2)
  left_inv x := by
    rcases x with ⟨b,x⟩
    change (Bool.xor (Bool.xor b (ξ x)) (ξ x),x) = (b,x)
    cases b <;> cases ξ x <;> rfl
  right_inv x := by
    rcases x with ⟨b,x⟩
    change (Bool.xor (Bool.xor b (ξ x)) (ξ x),x) = (b,x)
    cases b <;> cases ξ x <;> rfl

noncomputable def pairFiber (S : Finset (Bool × β)) (b : β) : Finset Bool :=
  Finset.univ.filter (fun ε => (ε,b) ∈ S)

lemma prod_pairFiber (S : Finset (Bool × β)) (f : Bool × β → ℝ) :
    (∏ x ∈ S, f x) = ∏ b : β, ∏ ε ∈ pairFiber S b, f (ε,b) := by
  classical
  simp only [pairFiber,Finset.prod_filter]
  rw [Finset.prod_comm,←Fintype.prod_prod_type (fun x : Bool × β => if x ∈ S then f x else 1)]
  rw [←Finset.prod_filter]
  congr 1
  ext x
  simp

lemma fiber_average_bound (S : Finset Bool) (p : Bool → ℝ) (hp : ∀ b, 0 ≤ p b) :
    finiteMean (fun c : Bool => ∏ ε ∈ S, p (Bool.xor ε c)) ≤
      ∏ ε ∈ S, (p ε + p (!ε))/2 := by
  rw [finiteMean_bool]
  have hxor : ∀ ε : Bool, Bool.xor ε true = Equiv.swap false true ε := by decide
  simp only [Bool.xor_false,hxor]
  calc
    _ ≤ ∏ ε ∈ S, (p ε+p (Equiv.swap false true ε))/2 :=
      swap_average_product S p hp false true
    _ = _ := Finset.prod_congr rfl (fun ε _ => by cases ε <;> rfl)

lemma CylinderBound.fair_parallel {m : Finset (Bool × β) → ℝ} {p : Bool × β → ℝ}
    (h : CylinderBound m p) (hp : ∀ x, 0 ≤ p x) :
    CylinderBound (fun S => finiteMean (fun ξ : β → Bool => m (S.image (pairLayer ξ))))
      (fun x => (p x+p (!x.1,x.2))/2) := by
  intro S
  calc
    _ ≤ finiteMean (fun ξ : β → Bool => ∏ x ∈ S, p (pairLayer ξ x)) := by
      apply finiteMean_mono
      intro ξ
      simpa only [Finset.prod_image (pairLayer ξ).injective.injOn] using h (S.image (pairLayer ξ))
    _ = ∏ b : β, finiteMean (fun c : Bool => ∏ ε ∈ pairFiber S b, p (Bool.xor ε c,b)) := by
      calc
        _ = finiteMean (fun ξ : β → Bool => ∏ b : β,
            ∏ ε ∈ pairFiber S b, p (Bool.xor ε (ξ b),b)) :=
          finiteMean_congr (fun ξ => prod_pairFiber S (fun x => p (pairLayer ξ x)))
        _ = _ := finiteMean_pi_prod (fun b c => ∏ ε ∈ pairFiber S b, p (Bool.xor ε c,b))
    _ ≤ ∏ b : β, ∏ ε ∈ pairFiber S b, (p (ε,b)+p (!ε,b))/2 := by
      apply Finset.prod_le_prod₀
      · intro b _
        exact div_nonneg (Finset.sum_nonneg (fun c _ =>
          Finset.prod_nonneg (fun ε _ => hp (Bool.xor ε c,b)))) (Nat.cast_nonneg _)
      · intro b _
        exact fiber_average_bound (pairFiber S b) (fun ε => p (ε,b)) (fun ε => hp (ε,b))
    _ = _ := (prod_pairFiber S (fun x => (p x+p (!x.1,x.2))/2)).symm

omit [Fintype β] in
lemma subset_pairLayer_image_iff (S A : Finset (Bool × β)) (ξ : β → Bool) :
    S ⊆ A.image (pairLayer ξ) ↔ S.image (pairLayer ξ) ⊆ A := by
  have hi (x : Bool × β) : pairLayer ξ (pairLayer ξ x) = x := (pairLayer ξ).left_inv x
  constructor
  · intro h
    have h' := Finset.image_subset_image h (f := pairLayer ξ)
    simpa only [Finset.image_image,Function.comp_def,hi,Finset.image_id'] using h'
  · intro h
    have h' := Finset.image_subset_image h (f := pairLayer ξ)
    simpa only [Finset.image_image,Function.comp_def,hi,Finset.image_id'] using h'

noncomputable def fairSetLayer {Ω : Type*} (F : Ω → Finset (Bool × β)) :
    Ω × (β → Bool) → Finset (Bool × β) := fun ω => (F ω.1).image (pairLayer ω.2)

lemma finiteMean_comm {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω'] (f : Ω → Ω' → ℝ) :
    finiteMean (fun x => finiteMean (f x)) = finiteMean (fun y => finiteMean (fun x => f x y)) := by
  simp only [finiteMean,←Finset.sum_div,div_div]
  rw [Finset.sum_comm,mul_comm]

lemma inclusionMoment_fairSetLayer {Ω : Type*} [Fintype Ω]
    (F : Ω → Finset (Bool × β)) (S : Finset (Bool × β)) :
    inclusionMoment (fairSetLayer F) S =
      finiteMean (fun ξ : β → Bool => inclusionMoment F (S.image (pairLayer ξ))) := by
  classical
  simp only [inclusionMoment_eq]
  have he : (fun ω : Ω × (β → Bool) => if S ⊆ fairSetLayer F ω then (1:ℝ) else 0) =
      (fun ω : Ω × (β → Bool) => if S.image (pairLayer ω.2) ⊆ F ω.1 then (1:ℝ) else 0) := by
    funext ω
    simp only [fairSetLayer,subset_pairLayer_image_iff]
  apply (congrArg finiteMean he).trans
  exact (finiteMean_prod (fun ω : Ω × (β → Bool) =>
    if S.image (pairLayer ω.2) ⊆ F ω.1 then (1:ℝ) else 0)).trans
      (finiteMean_comm (fun ω ξ => if S.image (pairLayer ξ) ⊆ F ω then (1:ℝ) else 0))

lemma inclusionMoment_fairSetLayer_singleton {Ω : Type*} [Fintype Ω]
    (F : Ω → Finset (Bool × β)) (x : Bool × β) :
    inclusionMoment (fairSetLayer F) {x} =
      (inclusionMoment F {x}+inclusionMoment F {(!x.1,x.2)})/2 := by
  rw [inclusionMoment_fairSetLayer]
  simp only [Finset.image_singleton,pairLayer,Equiv.coe_fn_mk]
  rw [finiteMean_pi_eval (A := fun _ : β => Bool) x.2 (fun c : Bool => inclusionMoment F {(Bool.xor x.1 c,x.2)})]
  rw [finiteMean_bool]
  rcases x with ⟨b,x⟩
  cases b <;> simp only [Bool.xor_false,Bool.false_xor,Bool.true_xor, Bool.not_false,Bool.not_true]

lemma cylinder_fairSetLayer {Ω : Type*} [Fintype Ω]
    (F : Ω → Finset (Bool × β))
    (h : CylinderBound (inclusionMoment F) (fun x => inclusionMoment F {x})) :
    CylinderBound (inclusionMoment (fairSetLayer F))
      (fun x => inclusionMoment (fairSetLayer F) {x}) := by
  have hh := h.fair_parallel (fun x => inclusionMoment_nonneg F {x})
  intro S
  rw [inclusionMoment_fairSetLayer]
  simp only [inclusionMoment_fairSetLayer_singleton]
  exact hh S

end ParallelFairLayer

section RelabelMarks
variable {α β Ω Ω' : Type*} [DecidableEq α] [DecidableEq β] [Fintype Ω] [Fintype Ω']

omit [Fintype Ω] [Fintype Ω'] in
lemma subset_image_equiv_iff (e : α ≃ β) (A : Finset α) (S : Finset β) :
    S ⊆ A.image e ↔ S.image e.symm ⊆ A := by
  constructor
  · intro h x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨x,hx,hxy⟩ := Finset.mem_image.mp (h hy)
    simpa only [←hxy,Equiv.symm_apply_apply] using hx
  · intro h y hy
    exact Finset.mem_image.mpr ⟨e.symm y,h (Finset.mem_image_of_mem _ hy),e.apply_symm_apply y⟩

omit [Fintype Ω'] in
lemma inclusionMoment_image_equiv (e : α ≃ β) (F : Ω → Finset α) (S : Finset β) :
    inclusionMoment (fun ω => (F ω).image e) S = inclusionMoment F (S.image e.symm) := by
  classical
  simp only [inclusionMoment_eq]
  apply finiteMean_congr
  intro ω
  simp only [subset_image_equiv_iff]

omit [Fintype Ω'] in
lemma cylinder_image_equiv (e : α ≃ β) (F : Ω → Finset α)
    (h : CylinderBound (inclusionMoment F) (fun x => inclusionMoment F {x})) :
    CylinderBound (inclusionMoment (fun ω => (F ω).image e))
      (fun x => inclusionMoment (fun ω => (F ω).image e) {x}) := by
  intro S
  simp only [inclusionMoment_image_equiv,Finset.image_singleton]
  have hh := h (S.image e.symm)
  simpa only [Finset.prod_image e.symm.injective.injOn] using hh

omit [DecidableEq β] in
lemma inclusionMoment_comp_equiv (e : Ω ≃ Ω') (F : Ω' → Finset α) (S : Finset α) :
    inclusionMoment (fun ω => F (e ω)) S = inclusionMoment F S := by
  classical
  simp only [inclusionMoment_eq]
  simpa only [Equiv.apply_symm_apply] using
    finiteMean_equiv e (fun ω => if S ⊆ F (e ω) then (1 : ℝ) else 0)

omit [DecidableEq β] in
lemma cylinder_comp_equiv (e : Ω ≃ Ω') (F : Ω' → Finset α)
    (h : CylinderBound (inclusionMoment F) (fun x => inclusionMoment F {x})) :
    CylinderBound (inclusionMoment (fun ω => F (e ω)))
      (fun x => inclusionMoment (fun ω => F (e ω)) {x}) := by
  intro S
  simpa only [inclusionMoment_comp_equiv] using h S
end RelabelMarks

lemma finiteMean_prod_mul {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω']
    (f : Ω → ℝ) (g : Ω' → ℝ) :
    finiteMean (fun ω : Ω × Ω' => f ω.1*g ω.2) = finiteMean f * finiteMean g := by
  simp only [finiteMean,Fintype.sum_prod_type,Fintype.card_prod,Nat.cast_mul,
    ←Finset.mul_sum,←Finset.sum_mul]
  ring

section JoinChildren
variable {β : Type*} [DecidableEq β]

noncomputable def childJoin (A B : Finset β) : Finset (Bool × β) :=
  A.image (fun x => (false,x)) ∪ B.image (fun x => (true,x))

lemma mem_childJoin (A B : Finset β) (b : Bool) (x : β) :
    (b,x) ∈ childJoin A B ↔ (if b then x ∈ B else x ∈ A) := by
  cases b <;> simp [childJoin]

noncomputable def boolFiber (S : Finset (Bool × β)) (b : Bool) : Finset β :=
  (S.filter (fun x => x.1 = b)).image Prod.snd

lemma mem_boolFiber (S : Finset (Bool × β)) (b : Bool) (x : β) :
    x ∈ boolFiber S b ↔ (b,x) ∈ S := by
  constructor
  · intro h
    obtain ⟨⟨c,y⟩,hy,hxy⟩ := Finset.mem_image.mp h
    obtain ⟨hy,hc⟩ := Finset.mem_filter.mp hy
    change c = b at hc
    change y = x at hxy
    simpa only [hc,hxy] using hy
  · intro h
    exact Finset.mem_image.mpr ⟨(b,x),Finset.mem_filter.mpr ⟨h,rfl⟩,rfl⟩

lemma childJoin_boolFiber (S : Finset (Bool × β)) :
    childJoin (boolFiber S false) (boolFiber S true) = S := by
  ext ⟨b,x⟩
  rw [mem_childJoin]
  cases b <;> simp only [Bool.false_eq_true,↓reduceIte,mem_boolFiber]

lemma subset_childJoin_iff (S : Finset (Bool × β)) (A B : Finset β) :
    S ⊆ childJoin A B ↔ boolFiber S false ⊆ A ∧ boolFiber S true ⊆ B := by
  constructor
  · intro h
    constructor
    · intro x hx
      exact (mem_childJoin A B false x).mp (h ((mem_boolFiber S false x).mp hx))
    · intro x hx
      exact (mem_childJoin A B true x).mp (h ((mem_boolFiber S true x).mp hx))
  · rintro ⟨h₀,h₁⟩ ⟨b,x⟩ hx
    rw [mem_childJoin]
    cases b
    · exact h₀ ((mem_boolFiber S false x).mpr hx)
    · exact h₁ ((mem_boolFiber S true x).mpr hx)

lemma prod_childJoin (A B : Finset β) (f : Bool × β → ℝ) :
    (∏ x ∈ childJoin A B, f x) = (∏ x ∈ A, f (false,x)) * ∏ x ∈ B, f (true,x) := by
  classical
  have hd : Disjoint (A.image (fun x => (false,x))) (B.image (fun x => (true,x))) := by
    apply Finset.disjoint_left.mpr
    rintro x hx hy
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b,hb,hba⟩ := Finset.mem_image.mp hy
    exact Bool.false_ne_true (congrArg Prod.fst hba).symm
  rw [childJoin,Finset.prod_union hd,
    Finset.prod_image (fun _ _ _ _ h => congrArg Prod.snd h),
    Finset.prod_image (fun _ _ _ _ h => congrArg Prod.snd h)]

lemma prod_boolFibers (S : Finset (Bool × β)) (f : Bool × β → ℝ) :
    (∏ x ∈ S, f x) = (∏ x ∈ boolFiber S false, f (false,x)) *
      ∏ x ∈ boolFiber S true, f (true,x) := by
  rw [←prod_childJoin,childJoin_boolFiber]

lemma inclusionMoment_childJoin {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω']
    (F : Ω → Finset β) (G : Ω' → Finset β) (S : Finset (Bool × β)) :
    inclusionMoment (fun ω : Ω × Ω' => childJoin (F ω.1) (G ω.2)) S =
      inclusionMoment F (boolFiber S false) * inclusionMoment G (boolFiber S true) := by
  classical
  simp only [inclusionMoment_eq]
  rw [←finiteMean_prod_mul]
  apply finiteMean_congr
  intro ω
  simp only [subset_childJoin_iff]
  split_ifs <;> simp_all

lemma cylinder_childJoin {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω'] [Nonempty Ω] [Nonempty Ω']
    (F : Ω → Finset β) (G : Ω' → Finset β)
    (hF : CylinderBound (inclusionMoment F) (fun x => inclusionMoment F {x}))
    (hG : CylinderBound (inclusionMoment G) (fun x => inclusionMoment G {x})) :
    CylinderBound (inclusionMoment (fun ω : Ω × Ω' => childJoin (F ω.1) (G ω.2)))
      (fun x => inclusionMoment (fun ω : Ω × Ω' => childJoin (F ω.1) (G ω.2)) {x}) := by
  intro S
  rw [inclusionMoment_childJoin,prod_boolFibers]
  have hf (b : Bool) (x : β) : boolFiber {(b,x)} b = {x} := by
    ext y
    simp only [mem_boolFiber,Finset.mem_singleton,Prod.mk.injEq,true_and]
  have hn (b : Bool) (x : β) : boolFiber {(!b,x)} b = ∅ := by
    ext y
    cases b <;> simp [mem_boolFiber]
  have h₀ (x : β) : inclusionMoment (fun ω : Ω × Ω' => childJoin (F ω.1) (G ω.2)) {(false,x)} =
      inclusionMoment F {x} * inclusionMoment G ∅ := by
    rw [inclusionMoment_childJoin,hf]
    have hh := hn true x
    exact congrArg (fun T => inclusionMoment F {x} * inclusionMoment G T) hh
  have h₁ (x : β) : inclusionMoment (fun ω : Ω × Ω' => childJoin (F ω.1) (G ω.2)) {(true,x)} =
      inclusionMoment F ∅ * inclusionMoment G {x} := by
    rw [inclusionMoment_childJoin,hf]
    have hh := hn false x
    exact congrArg (fun T => inclusionMoment F T * inclusionMoment G {x}) hh
  have emF : inclusionMoment F ∅ = 1 := by simp [inclusionMoment,finiteMean_const]
  have emG : inclusionMoment G ∅ = 1 := by simp [inclusionMoment,finiteMean_const]
  simp only [h₀,h₁,emF,emG,mul_one,one_mul]
  exact mul_le_mul (hF _) (hG _) (inclusionMoment_nonneg _ _)
    (Finset.prod_nonneg (fun x _ => inclusionMoment_nonneg F {x}))
end JoinChildren

def coinStepEquiv (d : ℕ) : (SwitchIndex (d+1) → Bool) ≃
    ((SwitchIndex d → Bool) × (SwitchIndex d → Bool)) × (Card d → Bool) where
  toFun ω := ((fun i => ω (Sum.inr (false,i)),fun i => ω (Sum.inr (true,i))),
    fun x => ω (Sum.inl x))
  invFun ω := Sum.elim ω.2 (fun bi => if bi.1 then ω.1.2 bi.2 else ω.1.1 bi.2)
  left_inv ω := by
    funext i
    cases i with
    | inl x => rfl
    | inr bi => cases bi with | mk b i => cases b <;> rfl
  right_inv ω := by
    rcases ω with ⟨⟨ω₀,ω₁⟩,ξ⟩
    rfl

def headTailEquiv (d : ℕ) : Card (d+1) ≃ Bool × Card d :=
  (Fin.consEquiv (fun _ : Fin (d+1) => Bool)).symm

lemma childMarks_join (d : ℕ) (A : Finset (Card (d+1))) :
    A = (childMarks A false).image (Fin.cons false) ∪
      (childMarks A true).image (Fin.cons true) := by
  classical
  ext x
  constructor
  · intro hx
    cases hb : x 0
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨Fin.tail x,(mem_childMarks _ _ _).mpr (by simpa only [←hb,Fin.cons_self_tail] using hx),
          by simp only [←hb,Fin.cons_self_tail]⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨Fin.tail x,(mem_childMarks _ _ _).mpr (by simpa only [←hb,Fin.cons_self_tail] using hx),
          by simp only [←hb,Fin.cons_self_tail]⟩)
  · intro hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
      exact (mem_childMarks _ _ _).mp hy
    · obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
      exact (mem_childMarks _ _ _).mp hy

noncomputable def butterflyMarks (d : ℕ) (A : Finset (Card d))
    (ω : SwitchIndex d → Bool) : Finset (Card d) :=
  A.image (butterflyPerm d (decodeButterfly d ω))

lemma butterflyMarks_succ (d : ℕ) (A : Finset (Card (d+1))) (ω : SwitchIndex (d+1) → Bool) :
    butterflyMarks (d+1) A ω =
      (fairSetLayer (fun p : (SwitchIndex d → Bool) × (SwitchIndex d → Bool) =>
        childJoin (butterflyMarks d (childMarks A false) p.1)
          (butterflyMarks d (childMarks A true) p.2)) (coinStepEquiv d ω)).image
            (headTailEquiv d).symm := by
  classical
  unfold butterflyMarks fairSetLayer childJoin
  rw [Finset.image_union,Finset.image_union]
  simp only [Finset.image_image]
  conv_lhs => rw [childMarks_join d A]
  rw [Finset.image_union]
  simp only [Finset.image_image]
  apply congrArg₂ (· ∪ ·)
  · apply Finset.image_congr
    intro x _
    simp only [Function.comp_def,butterflyPerm,decodeButterfly,Equiv.Perm.coe_mul,
      childLift,pairSwitch,switchFun,Equiv.coe_fn_mk,Fin.cons_zero,Fin.tail_cons,
      coinStepEquiv,headTailEquiv,Equiv.symm_symm,pairLayer]
    rfl
  · apply Finset.image_congr
    intro x _
    simp only [Function.comp_def,butterflyPerm,decodeButterfly,Equiv.Perm.coe_mul,
      childLift,pairSwitch,switchFun,Equiv.coe_fn_mk,Fin.cons_zero,Fin.tail_cons,
      coinStepEquiv,headTailEquiv,Equiv.symm_symm,pairLayer]
    rfl

lemma butterflyMarks_cylinder (d : ℕ) (A : Finset (Card d)) :
    CylinderBound (inclusionMoment (butterflyMarks d A))
      (fun x => inclusionMoment (butterflyMarks d A) {x}) := by
  induction d with
  | zero =>
    have he : butterflyMarks 0 A = fun _ : SwitchIndex 0 → Bool => A := by
      funext ω
      simp [butterflyMarks,butterflyPerm]
    rw [he]
    exact cylinder_const A
  | succ d ih =>
    have h := cylinder_childJoin (butterflyMarks d (childMarks A false))
      (butterflyMarks d (childMarks A true)) (ih _) (ih _)
    have hh := cylinder_image_equiv (headTailEquiv d).symm _ (cylinder_fairSetLayer _ h)
    have hs := cylinder_comp_equiv (coinStepEquiv d) _ hh
    simpa only [←butterflyMarks_succ] using hs

lemma indicator_mem_image_perm {α : Type*} [DecidableEq α]
    (A : Finset α) (p : Equiv.Perm α) (y : α) :
    (if y ∈ A.image p then (1 : ℝ) else 0) = ∑ x ∈ A, if p x = y then 1 else 0 := by
  classical
  by_cases h : y ∈ A.image p
  · obtain ⟨x,hx,hxy⟩ := Finset.mem_image.mp h
    rw [ite_eq_left (Finset.mem_image.mpr ⟨x,hx,hxy⟩)]
    symm
    calc
      _ = (if p x = y then (1:ℝ) else 0) := Finset.sum_eq_single_of_mem x hx (by
        intro z _ hzx
        exact ite_eq_right (fun hz => hzx (p.injective (hz.trans hxy.symm))))
      _ = 1 := ite_eq_left hxy
  · rw [ite_eq_right h]
    symm
    apply Finset.sum_eq_zero
    intro x hx
    exact ite_eq_right (fun hxy => h (Finset.mem_image.mpr ⟨x,hx,hxy⟩))

lemma butterflyMarks_singleton (d : ℕ) (A : Finset (Card d)) (y : Card d) :
    inclusionMoment (butterflyMarks d A) {y} = (A.card : ℝ)/(2:ℝ)^d := by
  classical
  unfold inclusionMoment
  simp only [Finset.singleton_subset_iff,butterflyMarks,indicator_mem_image_perm]
  rw [finiteMean_sum]
  simp only [butterfly_single_card_uniform,Finset.sum_const,nsmul_eq_mul]
  ring

lemma butterflyMarks_inclusion (d : ℕ) (A S : Finset (Card d)) :
    inclusionMoment (butterflyMarks d A) S ≤ ((A.card : ℝ)/(2:ℝ)^d)^S.card := by
  have h := butterflyMarks_cylinder d A S
  simpa only [butterflyMarks_singleton,Finset.prod_const] using h

namespace CycleColoring
variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev Coloring (p : Equiv.Perm α) (S : Finset α) :=
  {f : α → Bool // (∀ x, x ∉ S → f x = false) ∧
    ∀ x ∈ S, p x ∈ S → f (p x) = f x}

noncomputable instance (p : Equiv.Perm α) (S : Finset α) : Fintype (Coloring p S) :=
  Fintype.ofFinite _

noncomputable def boundary (p : Equiv.Perm α) (S : Finset α) : Finset α :=
  S.filter (fun x => p.symm x ∉ S)

noncomputable def root {p : Equiv.Perm α} {S : Finset α}
    (C : RoutingNetwork.SelectedCycle p S) : α := C.nonempty.choose

lemma root_mem {p : Equiv.Perm α} {S : Finset α} (C : RoutingNetwork.SelectedCycle p S) :
    root C ∈ C.val := C.nonempty.choose_spec

abbrev Seed (p : Equiv.Perm α) (S : Finset α) :=
  {x // x ∈ boundary p S} ⊕ RoutingNetwork.SelectedCycle p S

noncomputable def record {p : Equiv.Perm α} {S : Finset α}
    (f : Coloring p S) : Seed p S → Bool :=
  Sum.elim (fun x => f.val x.val) (fun C => f.val (root C))

lemma orbit_subset_of_predecessor_closed (p : Equiv.Perm α) (D : Finset α)
    (hD : ∀ x ∈ D, p.symm x ∈ D) {x : α} (hx : x ∈ D) : orbitSet p x ⊆ D := by
  intro y hy
  have hh := ((mem_orbitSet p x y).mp hy).inv
  obtain ⟨n,hn⟩ := hh.exists_nat_pow_eq
  have hp (k : ℕ) : (p⁻¹ ^ k) x ∈ D := by
    induction k with
    | zero => simpa using hx
    | succ k ih => simpa only [pow_succ',Equiv.Perm.mul_apply,Equiv.Perm.coe_inv] using hD _ ih
  exact hn ▸ hp n

lemma record_injective (p : Equiv.Perm α) (S : Finset α) :
    Function.Injective (record (p := p) (S := S)) := by
  classical
  intro f g hfg
  apply Subtype.ext
  funext x
  by_contra hne
  have hx : x ∈ S := by
    by_contra h
    exact hne ((f.property.1 x h).trans (g.property.1 x h).symm)
  let D := S.filter (fun y => f.val y ≠ g.val y)
  have hxD : x ∈ D := Finset.mem_filter.mpr ⟨hx,hne⟩
  have hprev (y : α) (hy : y ∈ D) : p.symm y ∈ D := by
    obtain ⟨hyS,hyne⟩ := Finset.mem_filter.mp hy
    have hpS : p.symm y ∈ S := by
      by_contra hn
      have hseed : y ∈ boundary p S := Finset.mem_filter.mpr ⟨hyS,hn⟩
      exact hyne (congrFun hfg (Sum.inl ⟨y,hseed⟩))
    refine Finset.mem_filter.mpr ⟨hpS,?_⟩
    have hf := f.property.2 (p.symm y) hpS (by simpa only [Equiv.apply_symm_apply] using hyS)
    have hg := g.property.2 (p.symm y) hpS (by simpa only [Equiv.apply_symm_apply] using hyS)
    simp only [Equiv.apply_symm_apply] at hf hg
    intro he
    exact hyne (hf.trans (he.trans hg.symm))
  have horb := orbit_subset_of_predecessor_closed p D hprev hxD
  let C : RoutingNetwork.SelectedCycle p S :=
    ⟨orbitSet p x,⟨x,rfl⟩,fun y hy => (Finset.mem_filter.mp (horb hy)).1⟩
  have hrD : root C ∈ D := horb (root_mem C)
  have hrne := (Finset.mem_filter.mp hrD).2
  exact hrne (congrFun hfg (Sum.inr C))

lemma card_coloring_le (p : Equiv.Perm α) (S : Finset α) :
    Fintype.card (Coloring p S) ≤
      2 ^ ((boundary p S).card + Fintype.card (RoutingNetwork.SelectedCycle p S)) := by
  have h := Fintype.card_le_of_injective (record (p := p) (S := S)) (record_injective p S)
  simpa only [Fintype.card_fun,Fintype.card_sum,Fintype.card_coe,Fintype.card_bool] using h

omit [Fintype α] in
lemma boundary_card (p : Equiv.Perm α) (S : Finset α) :
    (boundary p S).card = S.card - (S.filter (fun x => p.symm x ∈ S)).card := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := S) (fun x => p.symm x ∈ S)
  unfold boundary
  omega

lemma card_coloring_le_edges (p : Equiv.Perm α) (S : Finset α) :
    Fintype.card (Coloring p S) ≤
      2 ^ (S.card - (S.filter (fun x => p.symm x ∈ S)).card +
        Fintype.card (RoutingNetwork.SelectedCycle p S)) := by
  simpa only [boundary_card] using card_coloring_le p S


abbrev OppositeColoring (p : Equiv.Perm α) (S : Finset α) :=
  {f : α → Bool // (∀ x, x ∉ S → f x = false) ∧
    ∀ x ∈ S, p x ∈ S → f (p x) = !(f x)}

noncomputable instance (p : Equiv.Perm α) (S : Finset α) : Fintype (OppositeColoring p S) :=
  Fintype.ofFinite _

noncomputable def bipartitionFlip (p : Equiv.Perm α) (S : Finset α)
    (χ : α → Bool) (hχ : ∀ x, χ (p x) = !(χ x))
    (f : OppositeColoring p S) : Coloring p S := by
  classical
  refine ⟨(fun x => if x ∈ S then Bool.xor (f.val x) (χ x) else false),?_,?_⟩
  · intro x hx
    exact ite_eq_right hx
  · intro x hx hpx
    simp only [ite_eq_left hx,ite_eq_left hpx,f.property.2 x hx hpx,hχ x]
    cases f.val x <;> cases χ x <;> rfl

end CycleColoring
end Thorp

end ThorpNine.Tail

end OAI
