import Mathlib

namespace OAI

universe u_ι u_X

noncomputable section

namespace Problem310.RoutingPath

variable {ι : Type u_ι} {X : Type u_X}

/-- Route from a node by appending the locally selected child at each step.
The choice rule is abstract: a first-success/default selector can be supplied. -/
def routeFrom (choose : List ι → X → ι) : ℕ → List ι → X → List ι
  | 0, P, _ => P
  | n + 1, P, x =>
      let Q := routeFrom choose n P x
      Q ++ [choose Q x]

@[simp] theorem routeFrom_zero (choose : List ι → X → ι) (P : List ι) (x : X) :
    routeFrom choose 0 P x = P := rfl

@[simp] theorem routeFrom_succ (choose : List ι → X → ι) (n : ℕ) (P : List ι) (x : X) :
    routeFrom choose (n + 1) P x =
      routeFrom choose n P x ++ [choose (routeFrom choose n P x) x] := rfl

@[simp] theorem length_routeFrom (choose : List ι → X → ι)
    (n : ℕ) (P : List ι) (x : X) :
    (routeFrom choose n P x).length = P.length + n := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, Nat.add_assoc]

/-- A route can be resumed at any intermediate node. -/
theorem routeFrom_add (choose : List ι → X → ι)
    (n m : ℕ) (P : List ι) (x : X) :
    routeFrom choose (n + m) P x =
      routeFrom choose m (routeFrom choose n P x) x := by
  induction m with
  | zero => simp
  | succ m ih => simp only [Nat.add_succ, routeFrom_succ, ih]

/-- Every routed node extends the starting node. -/
theorem prefix_routeFrom (choose : List ι → X → ι)
    (n : ℕ) (P : List ι) (x : X) : P.IsPrefix (routeFrom choose n P x) := by
  induction n with
  | zero => exact List.prefix_refl _
  | succ n ih =>
      exact ih.trans (List.prefix_append _ _)

/-- Earlier decisions along one path suffice to preserve the full common prefix.
No restriction is imposed on decisions off that path. -/
theorem routeFrom_eq_of_choices_eq (choose : List ι → X → ι)
    (n : ℕ) (P : List ι) (x y : X)
    (hchoice : ∀ k < n,
      choose (routeFrom choose k P x) y = choose (routeFrom choose k P x) x) :
    routeFrom choose n P y = routeFrom choose n P x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hp := ih (fun k hk => hchoice k (Nat.lt_trans hk (Nat.lt_succ_self n)))
      simp only [routeFrom_succ, hp, hchoice n (Nat.lt_succ_self n)]

/-- Preservation through an ancestor prefix followed by one specified local child
identifies the actual terminal leaf with the locally routed leaf. -/
theorem routeFrom_eq_local_route (choose : List ι → X → ι)
    (k r : ℕ) (P U : List ι) (x y : X) (i : ι)
    (hU : routeFrom choose k P x = U)
    (hchoice : ∀ l < k,
      choose (routeFrom choose l P x) y = choose (routeFrom choose l P x) x)
    (hi : choose U y = i) :
    routeFrom choose (k + 1 + r) P y = routeFrom choose r (U ++ [i]) y := by
  have hp := routeFrom_eq_of_choices_eq choose k P x y hchoice
  rw [hU] at hp
  rw [routeFrom_add, routeFrom_succ, hp, hi]

/-- Generic local-success implication used by random routing: once the prefix is
preserved and child `i` is selected, the local terminal predicate is exactly the
terminal predicate of the actual root route. -/
theorem terminal_success_of_local_success (choose : List ι → X → ι)
    (terminal : List ι → X → Prop) (k r : ℕ) (P U : List ι)
    (x y : X) (i : ι)
    (hU : routeFrom choose k P x = U)
    (hchoice : ∀ l < k,
      choose (routeFrom choose l P x) y = choose (routeFrom choose l P x) x)
    (hi : choose U y = i)
    (hlocal : terminal (routeFrom choose r (U ++ [i]) y) y) :
    terminal (routeFrom choose (k + 1 + r) P y) y := by
  rw [routeFrom_eq_local_route choose k r P U x y i hU hchoice hi]
  exact hlocal

/-- Every earlier routed node is a prefix of every later routed node. -/
theorem routeFrom_prefix_of_le (choose : List ι → X → ι)
    (P : List ι) (x : X) {k d : ℕ} (hkd : k ≤ d) :
    (routeFrom choose k P x).IsPrefix (routeFrom choose d P x) := by
  have h := prefix_routeFrom choose (d - k) (routeFrom choose k P x) x
  rw [← routeFrom_add, Nat.add_sub_of_le hkd] at h
  exact h

/-- Truncating a routed leaf recovers the intermediate routed node. -/
theorem take_routeFrom (choose : List ι → X → ι)
    (P : List ι) (x : X) {k d : ℕ} (hkd : k ≤ d) :
    (routeFrom choose d P x).take (P.length + k) = routeFrom choose k P x := by
  obtain ⟨suffix, heq⟩ := routeFrom_prefix_of_le choose P x hkd
  rw [← heq]
  have h : (routeFrom choose k P x ++ suffix).take
      (routeFrom choose k P x).length = routeFrom choose k P x := by simp
  simpa only [length_routeFrom] using h

/-- Prescribed decisions on all initial segments determine a route. -/
theorem routeFrom_eq_take_of_choices (choose : List ι → X → ι)
    (L : List ι) (x : X)
    (hchoice : ∀ (k : ℕ) (hk : k < L.length), choose (L.take k) x = L[k])
    {n : ℕ} (hn : n ≤ L.length) : routeFrom choose n [] x = L.take n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hnl : n < L.length := by omega
      rw [routeFrom_succ, ih (by omega), hchoice n hnl,
        List.take_succ_eq_append_getElem hnl]

/-- Path-cylinder characterization: a terminal route equals a prescribed list
exactly when each successive decision follows that list. -/
theorem routeFrom_eq_iff_choices (choose : List ι → X → ι) (L : List ι) (x : X) :
    routeFrom choose L.length [] x = L ↔
      ∀ (k : ℕ) (hk : k < L.length), choose (L.take k) x = L[k] := by
  constructor
  · intro hroute k hk
    have hk0 := take_routeFrom choose [] x (Nat.le_of_lt hk)
    have hk1 := take_routeFrom choose [] x (Nat.succ_le_of_lt hk)
    rw [hroute] at hk0 hk1
    simp only [List.length_nil, Nat.zero_add] at hk0 hk1
    rw [routeFrom_succ, ← hk0, List.take_succ_eq_append_getElem hk] at hk1
    have h := List.append_cancel_left hk1
    simpa only [List.singleton_inj] using h.symm
  · intro hchoice
    simpa using routeFrom_eq_take_of_choices choose L x hchoice (le_refl L.length)

/-- Avoiding a default at every decision is the same as avoiding it in the
terminal path (for a route starting at the root). -/
theorem noDefault_iff_not_mem (choose : List ι → X → ι)
    (default : ι) (d : ℕ) (x : X) :
    (∀ k < d, choose (routeFrom choose k [] x) x ≠ default) ↔
      default ∉ routeFrom choose d [] x := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [routeFrom_succ, List.mem_append, List.mem_singleton, not_or]
      constructor
      · intro h
        refine ⟨ih.mp (fun k hk => h k (Nat.lt_trans hk (Nat.lt_succ_self d))), ?_⟩
        exact (h d (Nat.lt_succ_self d)).symm
      · rintro ⟨hprev, hlast⟩ k hk
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hkd | rfl
        · exact ih.mpr hprev k hkd
        · intro heq
          exact hlast heq.symm

/-- A route with no default child is represented by a vector of nondefault
children. This is the deterministic event equality needed for path-cylinder
probability estimates. -/
theorem noDefault_iff_exists_path {M : ℕ}
    (choose : List (Fin (M + 1)) → X → Fin (M + 1)) (d : ℕ) (x : X) :
    (∀ k < d, choose (routeFrom choose k [] x) x ≠ Fin.last M) ↔
      ∃ f : Fin d → Fin M,
        routeFrom choose d [] x = List.ofFn (fun i => (f i).castSucc) := by
  rw [noDefault_iff_not_mem]
  constructor
  · intro h
    let L := routeFrom choose d [] x
    have hL : L.length = d := by simp [L]
    have hentry : ∀ i : Fin d, L[i.val]'(by rw [hL]; exact i.isLt) ≠ Fin.last M := by
      intro i heq
      apply h
      rw [← heq]
      exact List.getElem_mem _
    let f : Fin d → Fin M := fun i =>
      (L[i.val]'(by rw [hL]; exact i.isLt)).castPred (hentry i)
    refine ⟨f, ?_⟩
    change L = _
    apply List.ext_getElem
    · simp [hL]
    · intro i hi hi'
      simp only [List.getElem_ofFn]
      simp only [f, Fin.castSucc_castPred]
  · rintro ⟨f, hf⟩
    rw [hf]
    simp only [List.mem_ofFn]
    rintro ⟨i, hi⟩
    exact Fin.castSucc_ne_last (f i) hi

/-- The no-default event is a union of the prescribed nondefault path cylinders. -/
theorem noDefault_iff_exists_choices {M : ℕ}
    (choose : List (Fin (M + 1)) → X → Fin (M + 1)) (d : ℕ) (x : X) :
    (∀ k < d, choose (routeFrom choose k [] x) x ≠ Fin.last M) ↔
      ∃ f : Fin d → Fin M, ∀ (k : ℕ) (hk : k < d),
        choose ((List.ofFn (fun i => (f i).castSucc)).take k) x =
          (f ⟨k, hk⟩).castSucc := by
  rw [noDefault_iff_exists_path]
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f, ?_⟩
    have hc := (routeFrom_eq_iff_choices choose
      (List.ofFn (fun i => (f i).castSucc)) x).mp (by simpa using hf)
    simpa only [List.length_ofFn, List.getElem_ofFn] using hc
  · rintro ⟨f, hf⟩
    refine ⟨f, ?_⟩
    have hc := (routeFrom_eq_iff_choices choose
      (List.ofFn (fun i => (f i).castSucc)) x).mpr (by
        simpa only [List.length_ofFn, List.getElem_ofFn] using hf)
    simpa only [List.length_ofFn] using hc

/-- Two different immediate child subtrees cannot share a descendant. -/
theorem child_eq_of_prefix {P L : List ι} {i j : ι}
    (hi : (P ++ [i]).IsPrefix L) (hj : (P ++ [j]).IsPrefix L) : i = j := by
  obtain ⟨s, hs⟩ := hi
  obtain ⟨t, ht⟩ := hj
  have h : P ++ (i :: s) = P ++ (j :: t) := by
    simpa only [List.append_assoc, List.singleton_append] using hs.trans ht.symm
  exact (List.cons.inj (List.append_cancel_left h)).1

/-- Local terminal leaves in different child subtrees have distinct addresses,
regardless of how the selectors route inside either subtree. -/
theorem routeFrom_ne_of_distinct_children (choose : List ι → X → ι)
    (r s : ℕ) (P : List ι) (x y : X) {i j : ι} (hij : i ≠ j) :
    routeFrom choose r (P ++ [i]) x ≠ routeFrom choose s (P ++ [j]) y := by
  intro heq
  apply hij
  apply child_eq_of_prefix (prefix_routeFrom choose r (P ++ [i]) x)
  rw [heq]
  exact prefix_routeFrom choose s (P ++ [j]) y

/-- A first default on a finite route has a well-defined first occurrence. -/
theorem exists_first_default (choose : List ι → X → ι)
    (d : ℕ) (P : List ι) (x : X) (default : ι)
    (h : ∃ k < d, choose (routeFrom choose k P x) x = default) :
    ∃ k < d, choose (routeFrom choose k P x) x = default ∧
      ∀ l < k, choose (routeFrom choose l P x) x ≠ default := by
  classical
  refine ⟨Nat.find h, (Nat.find_spec h).1, (Nat.find_spec h).2, ?_⟩
  intro l hl hdefault
  exact Nat.find_min h hl ⟨Nat.lt_trans hl (Nat.find_spec h).1, hdefault⟩

/-- Periodic node choices give periodic routed leaves. -/
theorem routeFrom_periodic (choose : List ι → ℝ → ι)
    (hchoose : ∀ P x, choose P (x + 1) = choose P x)
    (n : ℕ) (P : List ι) (x : ℝ) :
    routeFrom choose n P (x + 1) = routeFrom choose n P x := by
  apply routeFrom_eq_of_choices_eq
  intro k hk
  exact hchoose _ x

/-- Measurability of the finite router over a countable discrete child alphabet.
The joint node-choice map is the only input required from the table model. -/
theorem measurable_routeFrom [Countable ι]
    [MeasurableSpace X] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace (List ι)] [MeasurableSingletonClass (List ι)]
    (choose : List ι → X → ι)
    (hchoose : Measurable (Function.uncurry choose)) (n : ℕ) (P : List ι) :
    Measurable (routeFrom choose n P) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      have hnext : Measurable (fun x => choose (routeFrom choose n P x) x) :=
        hchoose.comp (ih.prodMk measurable_id)
      exact (measurable_of_countable (fun z : List ι × ι => z.1 ++ [z.2])).comp
        (ih.prodMk hnext)

end Problem310.RoutingPath

end

end OAI
