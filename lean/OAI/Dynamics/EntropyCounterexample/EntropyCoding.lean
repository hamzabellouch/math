import Mathlib

namespace OAI

namespace Problem340.EntropyCoding

abbrev SparseCode (n k : ℕ) (P Q : Type*) :=
  Σ s : {s : Finset (Fin n) // s.card ≤ k}, (Fin n → P) × (s.1 → Q)

theorem card_sparseCode_le (n k : ℕ) (P Q : Type*)
    [Fintype P] [Fintype Q] [Nonempty Q] :
    Fintype.card (SparseCode n k P Q) ≤
      2 ^ n * Fintype.card P ^ n * Fintype.card Q ^ k := by
  classical
  unfold SparseCode
  rw [Fintype.card_sigma]
  calc
    ∑ s : {s : Finset (Fin n) // s.card ≤ k},
        Fintype.card ((Fin n → P) × (s.1 → Q))
      ≤ ∑ _s : {s : Finset (Fin n) // s.card ≤ k},
          Fintype.card P ^ n * Fintype.card Q ^ k := by
            apply Finset.sum_le_sum
            intro s _
            simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
              Fintype.card_coe]
            exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Fintype.card_pos) s.2)
    _ = Fintype.card {s : Finset (Fin n) // s.card ≤ k} *
        (Fintype.card P ^ n * Fintype.card Q ^ k) := by simp
    _ ≤ 2 ^ n * (Fintype.card P ^ n * Fintype.card Q ^ k) := by
      apply Nat.mul_le_mul_right
      simpa only [Fintype.card_finset, Fintype.card_fin] using
        Fintype.card_subtype_le (fun s : Finset (Fin n) => s.card ≤ k)
    _ = _ := by ac_rfl

open Set SetRel Dynamics

theorem exists_dynCover_of_finite_code {X C : Type*} [Nonempty X] [Fintype C]
    (T : X → X) (U : SetRel X X) (n : ℕ) (code : X → C)
    (hcode : ∀ x y, code x = code y → (x, y) ∈ dynEntourage T U n) :
    ∃ s : Finset X, IsDynCoverOf T Set.univ U n s ∧ s.card ≤ Fintype.card C := by
  classical
  let repr : C → X := fun c =>
    if h : ∃ x, code x = c then Classical.choose h else Classical.arbitrary X
  have hrepr (x : X) : code (repr (code x)) = code x := by
    simp only [repr, dite_eq_left (show ∃ y, code y = code x from ⟨x, rfl⟩)]
    exact Classical.choose_spec (show ∃ y, code y = code x from ⟨x, rfl⟩)
  refine ⟨Finset.univ.image repr, ?_, ?_⟩
  · intro x _
    refine ⟨repr (code x), ?_, hcode x (repr (code x)) (hrepr x).symm⟩
    exact Finset.mem_image.mpr ⟨code x, Finset.mem_univ _, rfl⟩
  · exact (Finset.card_image_le).trans_eq (Finset.card_univ)

noncomputable def center {X P Q : Type*} {r k : ℕ}
    (p : P → X) (q : Q → X) (c : SparseCode r k P Q) (i : Fin r) : X := by
  classical
  exact if h : i ∈ c.1.1 then q (c.2.2 ⟨i, h⟩) else p (c.2.1 i)

theorem exists_dynCover_of_sparse_code {X P Q : Type*}
    [Nonempty X] [Fintype P] [Fintype Q] [Nonempty Q]
    (T : X → X) (U : SetRel X X) [U.IsSymm] (m r k : ℕ)
    (p : P → X) (q : Q → X) (code : X → SparseCode r k P Q)
    (hcode : ∀ x (i : Fin r),
      (T^[m * i.val] x, center p q (code x) i) ∈ dynEntourage T U m) :
    ∃ s : Finset X, IsDynCoverOf T Set.univ (U ○ U) (m * r) s ∧
      s.card ≤ 2 ^ r * Fintype.card P ^ r * Fintype.card Q ^ k := by
  classical
  obtain ⟨s, hs, hcard⟩ := exists_dynCover_of_finite_code T (U ○ U) (m * r) code (by
    intro x y hxy
    rw [mem_dynEntourage]
    intro j hj
    have hm : 0 < m := by nlinarith
    have hi : j / m < r := Nat.div_lt_of_lt_mul hj
    let i : Fin r := ⟨j / m, hi⟩
    have hx := (mem_dynEntourage.mp (hcode x i)) (j % m) (Nat.mod_lt j hm)
    have hy := (mem_dynEntourage.mp (hcode y i)) (j % m) (Nat.mod_lt j hm)
    rw [hxy] at hx
    have hstep : (T^[j % m] (T^[m * i.val] x),
        T^[j % m] (T^[m * i.val] y)) ∈ U ○ U :=
      ⟨T^[j % m] (center p q (code y) i), hx, U.symm hy⟩
    simpa only [i, ← Function.iterate_add_apply, Nat.mod_add_div] using hstep)
  exact ⟨s, hs, hcard.trans (card_sparseCode_le r k P Q)⟩

theorem card_filter_fin_eq_range (r : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun i : Fin r => p i.val)).card =
      ((Finset.range r).filter p).card := by
  classical
  have hmap : (Finset.univ.filter (fun i : Fin r => p i.val)).map Fin.valEmbedding =
      (Finset.range r).filter p := by
    ext j
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_range, Fin.valEmbedding_apply]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i.isLt, hi⟩
    · rintro ⟨hj, hp⟩
      exact ⟨⟨j, hj⟩, hp, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, hmap]

noncomputable def exceptionalBlocks {X : Type*} (T : X → X) (V : Set X)
    (m r : ℕ) (x : X) : Finset (Fin r) := by
  classical
  exact Finset.univ.filter (fun i : Fin r => T^[m * i.val] x ∉ V)

theorem exists_dynCover_of_sparse_visits {X P Q : Type*}
    [Nonempty X] [Fintype P] [Fintype Q] [Nonempty P] [Nonempty Q]
    (T : X → X) (U : SetRel X X) [U.IsSymm] (m r k : ℕ)
    (V : Set X) (p : P → X) (q : Q → X)
    (hp : ∀ x ∈ V, ∃ a : P, (x, p a) ∈ dynEntourage T U m)
    (hq : ∀ x, ∃ b : Q, (x, q b) ∈ dynEntourage T U m)
    (hsparse : ∀ x, (exceptionalBlocks T V m r x).card ≤ k) :
    ∃ s : Finset X, IsDynCoverOf T Set.univ (U ○ U) (m * r) s ∧
      s.card ≤ 2 ^ r * Fintype.card P ^ r * Fintype.card Q ^ k := by
  classical
  let bad (x : X) : Finset (Fin r) := exceptionalBlocks T V m r x
  have good_exists (x : X) (i : Fin r) :
      ∃ a : P, T^[m * i.val] x ∈ V →
        (T^[m * i.val] x, p a) ∈ dynEntourage T U m := by
    by_cases hi : T^[m * i.val] x ∈ V
    · obtain ⟨a, ha⟩ := hp _ hi
      exact ⟨a, fun _ => ha⟩
    · exact ⟨Classical.arbitrary P, fun h => (hi h).elim⟩
  choose good hgood using good_exists
  have other_exists (x : X) (i : Fin r) :
      ∃ b : Q, (T^[m * i.val] x, q b) ∈ dynEntourage T U m := hq _
  choose other hother using other_exists
  let code (x : X) : SparseCode r k P Q :=
    ⟨⟨bad x, hsparse x⟩, good x, fun i => other x i.val⟩
  apply exists_dynCover_of_sparse_code T U m r k p q code
  intro x i
  simp only [center, code]
  split_ifs with hi
  · exact hother x i
  · apply hgood x i
    simpa only [bad, exceptionalBlocks, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hi

theorem coverMincard_le_of_sparse_visits {X P Q : Type*}
    [Nonempty X] [Fintype P] [Fintype Q] [Nonempty P] [Nonempty Q]
    (T : X → X) (U : SetRel X X) [U.IsSymm] (m r k : ℕ)
    (V : Set X) (p : P → X) (q : Q → X)
    (hp : ∀ x ∈ V, ∃ a : P, (x, p a) ∈ dynEntourage T U m)
    (hq : ∀ x, ∃ b : Q, (x, q b) ∈ dynEntourage T U m)
    (hsparse : ∀ x, (exceptionalBlocks T V m r x).card ≤ k) :
    coverMincard T Set.univ (U ○ U) (m * r) ≤
      (2 ^ r * Fintype.card P ^ r * Fintype.card Q ^ k : ℕ) := by
  obtain ⟨s, hs, hcard⟩ := exists_dynCover_of_sparse_visits T U m r k V p q hp hq hsparse
  exact hs.coverMincard_le_card.trans (by exact_mod_cast hcard)

end Problem340.EntropyCoding

end OAI
