import OAI.Computability.WLIdentification.CycleSums

namespace OAI

namespace WLIdentification

/-- A finite-slot bijective extension system. The extra slot is genuine:
a k-tuple is extended before any one of its slots is discarded. -/
structure BijectionSystem (G H : Graph) (K : ℕ) where
  relates : (m : ℕ) → (Fin m → Fin G.order) → (Fin m → Fin H.order) → Prop
  empty : ∀ v w, relates 0 v w
  restrict : ∀ {m n} {v w}, relates m v w → ∀ f : Fin n → Fin m,
    relates n (v ∘ f) (w ∘ f)
  atomic : ∀ {m v w}, relates m v w →
    (∀ i j, v i = v j ↔ w i = w j) ∧
    (∀ i j, G.edge (v i) (v j) = H.edge (w i) (w j))
  extend : ∀ {m}, m < K → ∀ {v w}, relates m v w →
    ∃ e : Fin G.order ≃ Fin H.order, ∀ z,
      relates (m + 1) (Fin.snoc v z) (Fin.snoc w (e z))

namespace BijectionSystem

/-- Deleting a slot after an extension simultaneously preserves every possible
replacement, as required by the joint (not independent-marginal) WL update. -/
theorem replace {G H : Graph} {K m : ℕ} (S : BijectionSystem G H K)
    {v : Fin m → Fin G.order} {w : Fin m → Fin H.order}
    {z : Fin G.order} {z' : Fin H.order}
    (h : S.relates (m + 1) (Fin.snoc v z) (Fin.snoc w z')) (i : Fin m) :
    S.relates m (Function.update v i z) (Function.update w i z') := by
  let f (j : Fin m) : Fin (m + 1) := if j = i then Fin.last m else j.castSucc
  have hv : Fin.snoc v z ∘ f = Function.update v i z := by
    funext j
    by_cases hj : j = i
    · subst j; simp [f]
    · simp [f, hj]
  have hw : Fin.snoc w z' ∘ f = Function.update w i z' := by
    funext j
    by_cases hj : j = i
    · subst j; simp [f]
    · simp [f, hj]
  simpa only [hv, hw] using S.restrict h f

/-- Every maintained tuple has equal colors at every actual finite joint round. -/
theorem tupleColor_eq {G H : Graph} {K k : ℕ} (S : BijectionSystem G H K)
    (hk : k < K) {v : Fin k → Fin G.order} {w : Fin k → Fin H.order}
    (h : S.relates k v w) (round : ℕ) : tupleColor G k round v = tupleColor H k round w := by
  induction round generalizing v w with
  | zero =>
    apply Prod.ext
    · funext i j
      exact decide_eq_decide.mpr ((S.atomic h).1 i j)
    · funext i j
      exact (S.atomic h).2 i j
  | succ r ih =>
    obtain ⟨e, he⟩ := S.extend hk h
    apply Prod.ext
    · exact ih h
    · apply histogram_eq_of_equiv e
      intro z
      funext i
      exact ih (S.replace (he z) i)

def tupleSnocEquiv (V : Type) (m : ℕ) : ((Fin m → V) × V) ≃ (Fin (m + 1) → V) where
  toFun p := Fin.snoc p.1 p.2
  invFun v := (Fin.init v, v (Fin.last m))
  left_inv _ := by simp
  right_inv _ := Fin.snoc_init_self _

/-- Sequentially chosen vertex bijections give a bijection of all ordered tuples;
there is no unsupported inference from mere existence of a mate for each tuple. -/
theorem tupleBijection {G H : Graph} {K : ℕ} (S : BijectionSystem G H K)
    (m : ℕ) (hm : m ≤ K) :
    ∃ E : (Fin m → Fin G.order) ≃ (Fin m → Fin H.order), ∀ v, S.relates m v (E v) := by
  induction m with
  | zero => exact ⟨Equiv.ofUnique _ _, fun v => S.empty v _⟩
  | succ m ih =>
    obtain ⟨E, hE⟩ := ih (by omega)
    have hext (v : Fin m → Fin G.order) :
        ∃ e : Fin G.order ≃ Fin H.order, ∀ z,
          S.relates (m + 1) (Fin.snoc v z) (Fin.snoc (E v) (e z)) :=
      S.extend (by omega) (hE v)
    choose e he using hext
    let P := (Equiv.prodCongrRight e).trans (Equiv.prodCongr E (Equiv.refl _))
    let E' := (tupleSnocEquiv (Fin G.order) m).symm.trans
      (P.trans (tupleSnocEquiv (Fin H.order) m))
    refine ⟨E', ?_⟩
    intro v
    change S.relates (m + 1) v (Fin.snoc (E (Fin.init v)) (e (Fin.init v) (v (Fin.last m))))
    simpa only [Fin.snoc_init_self] using he (Fin.init v) (v (Fin.last m))

/-- A genuine k+1-slot system proves equivalence for the literal joint k-WL colors. -/
theorem equivalent {G H : Graph} {K k : ℕ} (S : BijectionSystem G H K)
    (hk : 2 ≤ k) (hkK : k < K) : Equivalent k G H := by
  rw [Equivalent, ite_eq_right (by omega : k ≠ 1)]
  intro round
  obtain ⟨E, hE⟩ := S.tupleBijection k (by omega)
  exact histogram_eq_of_equiv E _ _ (fun v => S.tupleColor_eq hkK (hE v) round)

end BijectionSystem

/-- Finite descending choice, used only for actual finite vertex/tuple bijections. -/
theorem finite_descending_choice {A : Type} [Fintype A]
    (P : ℕ → A → Prop) (hm : ∀ n a, P (n + 1) a → P n a)
    (he : ∀ n, ∃ a, P n a) : ∃ a, ∀ n, P n a := by
  classical
  by_contra h
  have hn : ∀ a : A, ∃ n, ¬ P n a := by simpa only [not_exists, not_forall] using h
  choose n hn using hn
  let N : ℕ := ∑ a : A, n a
  obtain ⟨a, ha⟩ := he N
  have hle : n a ≤ N := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
  have hdown : ∀ j l, j ≤ l → P l a → P j a := by
    intro j l hj
    induction l, hj using Nat.le_induction with
    | base => exact id
    | succ l _ ih => exact fun hp => ih (hm l a hp)
  exact hn a (hdown (n a) N hle ha)

def StableTuple {G H : Graph} (k : ℕ) (v : Fin k → Fin G.order) (w : Fin k → Fin H.order) : Prop :=
  ∀ round, tupleColor G k round v = tupleColor H k round w

theorem stableTuple_exists {G H : Graph} {k : ℕ} (hk : k ≠ 1)
    (h : Equivalent k G H) (v : Fin k → Fin G.order) :
    ∃ w : Fin k → Fin H.order, StableTuple k v w := by
  rw [Equivalent, ite_eq_right hk] at h
  apply finite_descending_choice (fun r w => tupleColor G k r v = tupleColor H k r w)
  · intro r w hh
    exact congrArg Prod.fst hh
  · intro r
    obtain ⟨E, hE⟩ := tupleRound_bijection (h r)
    exact ⟨E v, hE v⟩

/-- Stable joint colors supply one permanent finite vertex bijection for all
replacement coordinates and all refinement rounds, not a separate round choice. -/
theorem stableTuple_extension {G H : Graph} {k : ℕ}
    {v : Fin k → Fin G.order} {w : Fin k → Fin H.order} (h : StableTuple k v w) :
    ∃ e : Fin G.order ≃ Fin H.order, ∀ z i,
      StableTuple k (Function.update v i z) (Function.update w i (e z)) := by
  classical
  let P (r : ℕ) (e : Fin G.order ≃ Fin H.order) : Prop := ∀ z i,
    tupleColor G k r (Function.update v i z) = tupleColor H k r (Function.update w i (e z))
  have hmono (r : ℕ) (e : Fin G.order ≃ Fin H.order) (he : P (r + 1) e) : P r e := by
    intro z i
    exact congrArg Prod.fst (he z i)
  have hn (r : ℕ) : ∃ e, P r e := by
    have hh := congrArg Prod.snd (h (r + 1))
    change Finset.univ.val.map (fun z => fun i => tupleColor G k r (Function.update v i z)) =
      Finset.univ.val.map (fun z => fun i => tupleColor H k r (Function.update w i z)) at hh
    obtain ⟨e, he⟩ := exists_colorEquiv _ _ hh
    exact ⟨e, fun z i => congrFun (he z) i⟩
  obtain ⟨e, he⟩ := finite_descending_choice P hmono hn
  exact ⟨e, fun z i r => he r z i⟩

/-- Such an extension fixes all currently paired vertices and preserves adjacency
to every current slot, as can be tested in a different replacement coordinate. -/
theorem stableTuple_extension_local {G H : Graph} {k : ℕ} (hk : 2 ≤ k)
    {v : Fin k → Fin G.order} {w : Fin k → Fin H.order} (h : StableTuple k v w) :
    ∃ e : Fin G.order ≃ Fin H.order,
      (∀ z i, StableTuple k (Function.update v i z) (Function.update w i (e z))) ∧
      (∀ i, e (v i) = w i) ∧
      (∀ z i, G.edge (v i) z = H.edge (w i) (e z)) ∧
      (∀ z, degree G z = degree H (e z)) := by
  obtain ⟨e, he⟩ := stableTuple_extension h
  have hdif (i : Fin k) : ∃ j : Fin k, i ≠ j := by
    let a : Fin k := ⟨0, by omega⟩
    let b : Fin k := ⟨1, by omega⟩
    by_cases hia : i = a
    · refine ⟨b, ?_⟩
      subst i
      intro hh
      have := congrArg Fin.val hh
      simp [a, b] at this
    · exact ⟨a, hia⟩
  refine ⟨e, he, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨j, hij⟩ := hdif i
    have hh := (round_one_local hk (he (v i) j 1)).1 i j
    have hh' : w i = e (v i) := by
      simpa only [Function.update_of_ne hij, Function.update_self] using hh.mp (by simp only [Function.update_of_ne hij, Function.update_self])
    exact hh'.symm
  · intro z i
    obtain ⟨j, hij⟩ := hdif i
    have hh := (round_one_local hk (he z j 1)).2.1 i j
    simpa only [Function.update_of_ne hij, Function.update_self] using hh
  · intro z
    let i : Fin k := ⟨0, by omega⟩
    simpa only [Function.update_self] using (round_one_local hk (he z i 1)).2.2 i

end WLIdentification

end OAI
