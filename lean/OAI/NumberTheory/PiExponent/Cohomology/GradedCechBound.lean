import OAI.NumberTheory.PiExponent.Cohomology.GradedCech
import OAI.NumberTheory.PiExponent.Cohomology.TupleCechBound

namespace OAI

namespace PiExponent.FiniteTupleCech
noncomputable section
open scoped BigOperators
open GradedCech (tupleSet tupleSet_comp_subset tupleSet_subset)
variable {J : Type*} [DecidableEq J] (D : Finset J → Type*)
  [∀ s, AddCommGroup (D s)]
  (r : ∀ {s t : Finset J}, s ⊆ t → D s →+ D t)
  (rid : ∀ s (z : D s), r (s := s) le_rfl z = z)
  (rcomp : ∀ {s t u : Finset J} (hst : s ⊆ t) (htu : t ⊆ u) (z : D s),
    r htu (r hst z) = r (hst.trans htu) z)

abbrev Cochain (q : ℕ) := ∀ t : Fin (q + 1) → J, D (tupleSet t)

def differential {q : ℕ} (c : Cochain D q) : Cochain D (q + 1) :=
  fun t => ∑ i : Fin (q + 2), (-1 : ℤ) ^ i.val •
    r (tupleSet_comp_subset t i.succAbove) (c (t ∘ i.succAbove))

lemma differential_zero {q : ℕ} : differential D r (0 : Cochain D q) = 0 := by
  funext t
  simp [differential]

lemma differential_add {q : ℕ} (a b : Cochain D q) :
    differential D r (a + b) = differential D r a + differential D r b := by
  funext t
  simp only [differential, Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]

lemma differential_sub {q : ℕ} (a b : Cochain D q) :
    differential D r (a - b) = differential D r a - differential D r b := by
  funext t
  simp only [differential, Pi.sub_apply, map_sub, smul_sub, Finset.sum_sub_distrib]

lemma mem_tupleSet {n : ℕ} (t : Fin n → J) (i : Fin n) : t i ∈ tupleSet t :=
  Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

def liftTo (s : Finset J) {n : ℕ} (t : Fin n → J) (ht : tupleSet t ⊆ s) :
    Fin n → s := fun i => ⟨t i, ht (mem_tupleSet t i)⟩

def evaluate (s : Finset J) {q : ℕ} (c : Cochain D q) :
    ProjectiveMonomialCechHigher.Cochain s (D s) q :=
  fun t => r (tupleSet_subset s Subtype.val (fun j => j.property) t) (c (Subtype.val ∘ t))

include rcomp in
lemma evaluate_differential (s : Finset J) {q : ℕ} (c : Cochain D q) :
    evaluate D r s (differential D r c) =
      ProjectiveMonomialCechHigher.differential (evaluate D r s c) := by
  funext t
  simp only [evaluate, differential, ProjectiveMonomialCechHigher.differential,
    map_sum, map_zsmul, rcomp]
  rfl

include rid rcomp in
lemma differential_squared {q : ℕ} (c : Cochain D q) :
    differential D r (differential D r c) = 0 := by
  funext t
  have h := congrFun (ProjectiveMonomialCechHigher.differential_squared
    (evaluate D r (tupleSet t) c)) (liftTo (tupleSet t) t le_rfl)
  rw [← evaluate_differential D r rcomp, ← evaluate_differential D r rcomp] at h
  change r le_rfl (differential D r (differential D r c) t) = 0 at h
  simpa only [rid, Pi.zero_apply] using h

lemma tuple_card_lt_of_missing {s : Finset J} {n : ℕ} (t : Fin n → J)
    (ht : tupleSet t ⊆ s) (j : J) (hj : j ∈ s) (hmiss : ∀ i, t i ≠ j) :
    (tupleSet t).card < s.card := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨ht, ?_⟩
  intro he
  have hmem : j ∈ tupleSet t := he.symm ▸ hj
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
  exact hmiss i hi

def assemble {q k : ℕ}
    (B : ∀ s : Finset J, s.card = k → ProjectiveMonomialCechHigher.Cochain s (D s) q) :
    Cochain D q := fun t =>
  if h : (tupleSet t).card = k then B (tupleSet t) h (liftTo (tupleSet t) t le_rfl) else 0

include rid in
lemma assemble_restrict {q k : ℕ}
    (B : ∀ s : Finset J, s.card = k → ProjectiveMonomialCechHigher.Cochain s (D s) q)
    (hB : ∀ s hs, TupleCechBound.FullSupport (B s hs))
    (s : Finset J) (hs : s.card = k) (t : Fin (q + 1) → J) (ht : tupleSet t ⊆ s) :
    r ht (assemble D B t) = B s hs (liftTo s t ht) := by
  classical
  by_cases he : tupleSet t = s
  · subst s
    simp only [assemble, dite_eq_left hs, rid]
  · have hlt : (tupleSet t).card < k := by
      rw [← hs]
      exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨ht, he⟩)
    rw [assemble, dite_eq_right (ne_of_lt hlt), map_zero]
    symm
    have hnot : ¬ s ⊆ tupleSet t := fun h => he (Finset.Subset.antisymm ht h)
    obtain ⟨j, hj, hjt⟩ := Finset.not_subset.mp hnot
    apply hB s hs _ ⟨j, hj⟩
    intro i hi
    have heq : t i = j := congrArg Subtype.val hi
    exact hjt (heq ▸ mem_tupleSet t i)

lemma differential_assemble_below {q k : ℕ}
    (B : ∀ s : Finset J, s.card = k → ProjectiveMonomialCechHigher.Cochain s (D s) q)
    (t : Fin (q + 2) → J) (ht : (tupleSet t).card < k) :
    differential D r (assemble D B) t = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have hle := Finset.card_le_card (tupleSet_comp_subset t i.succAbove)
  have hne : (tupleSet (t ∘ i.succAbove)).card ≠ k := by omega
  simp only [assemble, dite_eq_right hne, map_zero, smul_zero]

variable [Fintype J]

include rid rcomp in

theorem level_correction {q k : ℕ} (hq : Fintype.card J ≤ q + 1)
    (c : Cochain D (q + 1)) (hc : differential D r c = 0)
    (hv : ∀ t, (tupleSet t).card < k → c t = 0) :
    ∃ b : Cochain D q,
      (∀ t, (tupleSet t).card < k → differential D r b t = 0) ∧
      (∀ t, (tupleSet t).card = k → differential D r b t = c t) := by
  classical
  have hlocal (s : Finset J) (hs : s.card = k) :
      ∃ b : ProjectiveMonomialCechHigher.Cochain s (D s) q,
        ProjectiveMonomialCechHigher.differential b = evaluate D r s c ∧
        TupleCechBound.FullSupport b := by
    apply TupleCechBound.fullSupport_primitives
    · simpa only [Fintype.card_coe] using (Finset.card_le_univ s).trans hq
    · rw [← evaluate_differential D r rcomp, hc]
      funext t
      exact map_zero _
    · intro t j hj
      have hsub := tupleSet_subset s Subtype.val (fun j => j.property) t
      have hlt : (tupleSet (Subtype.val ∘ t)).card < k := by
        rw [← hs]
        apply tuple_card_lt_of_missing (Subtype.val ∘ t) hsub j.val j.property
        intro i he
        exact hj i (Subtype.ext he)
      change r hsub (c (Subtype.val ∘ t)) = 0
      rw [hv _ hlt, map_zero]
  choose B hB hfull using hlocal
  refine ⟨assemble D B, differential_assemble_below D r B, ?_⟩
  intro t ht
  let s := tupleSet t
  calc
    differential D r (assemble D B) t =
        ProjectiveMonomialCechHigher.differential (B s ht) (liftTo s t le_rfl) := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun z => (-1 : ℤ) ^ i.val • z)
        (assemble_restrict D r rid B hfull s ht (t ∘ i.succAbove)
          (tupleSet_comp_subset t i.succAbove))
    _ = evaluate D r s c (liftTo s t le_rfl) := congrFun (hB s ht) _
    _ = c t := rid s (c t)

include rid rcomp in

theorem primitives {q : ℕ} (hq : Fintype.card J ≤ q + 1)
    (c : Cochain D (q + 1)) (hc : differential D r c = 0) :
    ∃ b : Cochain D q, differential D r b = c := by
  classical
  have hlevels : ∀ k : ℕ, ∃ b : Cochain D q,
      ∀ t, (tupleSet t).card < k → differential D r b t = c t := by
    intro k
    induction k with
    | zero => exact ⟨0, fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
    | succ k ih =>
      obtain ⟨b, hb⟩ := ih
      let a := c - differential D r b
      have ha : differential D r a = 0 := by
        rw [differential_sub, hc, differential_squared D r rid rcomp, sub_self]
      have hav : ∀ t, (tupleSet t).card < k → a t = 0 := by
        intro t ht
        change c t - differential D r b t = 0
        rw [hb t ht, sub_self]
      obtain ⟨e, helo, heeq⟩ := level_correction D r rid rcomp hq a ha hav
      refine ⟨b + e, ?_⟩
      intro t ht
      rw [differential_add, Pi.add_apply]
      by_cases hlt : (tupleSet t).card < k
      · rw [hb t hlt, helo t hlt, add_zero]
      · have heq : (tupleSet t).card = k := by omega
        rw [heeq t heq]
        change differential D r b t + (c t - differential D r b t) = c t
        abel
  obtain ⟨b, hb⟩ := hlevels (Fintype.card J + 1)
  refine ⟨b, funext (fun t => hb t ?_)⟩
  exact Nat.lt_succ_of_le (Finset.card_le_univ (tupleSet t))

end
end PiExponent.FiniteTupleCech

namespace PiExponent.GradedCechBound
noncomputable section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  {σR σM : Type*} [SetLike σR R]
  [SetLike σM M] [AddSubgroupClass σM M]
  (𝒜 : ℤ → σR) (𝓜 : ℤ → σM)
  [SetLike.GradedMonoid 𝒜] [SetLike.GradedSMul 𝒜 𝓜]
  {J : Type*} [Fintype J] [DecidableEq J]
  (x : J → R) (hx : ∀ j, x j ∈ 𝒜 1) (d : ℤ)

theorem primitives {q : ℕ} (hq : Fintype.card J ≤ q + 1)
    (c : GradedCech.Cochain 𝒜 𝓜 x hx d (q + 1))
    (hc : GradedCech.differential 𝒜 𝓜 x hx d c = 0) :
    ∃ b : GradedCech.Cochain 𝒜 𝓜 x hx d q,
      GradedCech.differential 𝒜 𝓜 x hx d b = c := by
  exact FiniteTupleCech.primitives
    (fun s => GradedCech.IntersectionPiece 𝒜 𝓜 x hx s d)
    (fun {_ _} h => GradedCech.setRestriction 𝒜 𝓜 x hx h d)
    (fun s z => GradedCech.setRestriction_refl 𝒜 𝓜 x hx s d z)
    (fun {_ _ _} hst htu z => GradedCech.setRestriction_comp 𝒜 𝓜 x hx hst htu d z)
    hq c hc

end
end PiExponent.GradedCechBound

end OAI
