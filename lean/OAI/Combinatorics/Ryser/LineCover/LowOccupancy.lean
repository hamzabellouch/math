import OAI.Combinatorics.Ryser.LineCover.PairSampling
import OAI.Combinatorics.Ryser.LineCover.SamplingDefinitions
import OAI.Combinatorics.Ryser.LineCover.DisjointPairs
import OAI.Combinatorics.Ryser.Geometry.ProjectiveJoins
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def shapePairs (L : Finset (AffineLine F)) (S : Finset (Point F)) :
    Finset (↥L × ↥L) :=
  Finset.univ.filter fun p =>
    p.1 ≠ p.2 ∧ S ≠ linePoints p.1.val ∧ S ≠ linePoints p.2.val ∧
      ∃ x ∈ S, Incidence x p.1.val ∧ Incidence x p.2.val

@[simp] theorem mem_shapePairs (L : Finset (AffineLine F))
    (S : Finset (Point F)) (p : ↥L × ↥L) :
    p ∈ shapePairs L S ↔
      p.1 ≠ p.2 ∧ S ≠ linePoints p.1.val ∧ S ≠ linePoints p.2.val ∧
        ∃ x ∈ S, Incidence x p.1.val ∧ Incidence x p.2.val := by
  simp only [shapePairs, Finset.mem_filter, Finset.mem_univ, true_and]

theorem card_shapePairs_le
    (shapes : Finset (Finset (Point F))) (L : Finset (AffineLine F))
    {D R : ℕ} (hSparse : SparseShapes shapes D)
    (hR : ∀ p : ProjectivePoint F, (coverPencil L p).card ≤ R)
    {S : Finset (Point F)} (hS : S ∈ shapes) :
    (shapePairs L S).card ≤ L.card * D * R := by
  classical
  have hfiber (a : ↥L) :
      ((shapePairs L S).filter fun p => p.1 = a).card ≤ D * R := by
    by_cases ha : S = linePoints a.val
    · have hempty : (shapePairs L S).filter (fun p => p.1 = a) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro p hp hpa
        have hne := ((mem_shapePairs L S p).mp hp).2.1
        apply hne
        simpa only [hpa] using ha
      simp only [hempty, Finset.card_empty, Nat.zero_le]
    · let C := S ∩ linePoints a.val
      let pool := C.biUnion fun x => coverPencil L (Sum.inl x)
      calc
        ((shapePairs L S).filter fun p => p.1 = a).card ≤ pool.card := by
          apply Finset.card_le_card_of_injOn (fun p : ↥L × ↥L => p.2.val)
          · intro p hp
            have hpa := (Finset.mem_filter.mp hp).2
            obtain ⟨_, _, _, x, hx, hfirst, hsecond⟩ :=
              (mem_shapePairs L S p).mp (Finset.mem_filter.mp hp).1
            apply Finset.mem_biUnion.mpr
            refine ⟨x, Finset.mem_inter.mpr ⟨hx, ?_⟩, ?_⟩
            · apply (mem_linePoints x a.val).mpr
              simpa only [hpa] using hfirst
            · exact (mem_coverPencil L (Sum.inl x) p.2.val).mpr
                ⟨p.2.property, hsecond⟩
          · intro p hp q hq hpq
            apply Prod.ext
            · exact (Finset.mem_filter.mp hp).2.trans
                (Finset.mem_filter.mp hq).2.symm
            · exact Subtype.ext hpq
        _ ≤ ∑ x ∈ C, (coverPencil L (Sum.inl x)).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ _x ∈ C, R := Finset.sum_le_sum fun x _ => hR (Sum.inl x)
        _ = C.card * R := by simp only [Finset.sum_const, Nat.nsmul_eq_mul]
        _ ≤ D * R := Nat.mul_le_mul_right R (hSparse S hS a.val ha)
  calc
    (shapePairs L S).card =
        ∑ a : ↥L, ((shapePairs L S).filter fun p => p.1 = a).card :=
      Finset.card_eq_sum_card_fiberwise
        (s := shapePairs L S) (t := Finset.univ) (f := Prod.fst)
        (fun _ _ => Finset.mem_univ _)
    _ ≤ ∑ _a : ↥L, D * R := Finset.sum_le_sum fun a _ => hfiber a
    _ = L.card * D * R := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
        Nat.nsmul_eq_mul, Nat.mul_assoc]

theorem shape_ne_linePoints_of_not_mem_tupleShapes
    {t : ℕ} (a : LineTuple F t) {S : Finset (Point F)}
    (hS : S ∉ tupleShapes a) (slot : Fin t ⊕ Fin t) :
    S ≠ linePoints (a slot) := by
  intro heq
  exact hS ((mem_tupleShapes a S).mpr ⟨slot, heq.symm⟩)

theorem exists_disjoint_shapePairs_of_occupancy
    (shapes : Finset (Finset (Point F))) (L : Finset (AffineLine F))
    {D h t : ℕ} (hSparse : SparseShapes shapes D)
    {S : Finset (Point F)} (hS : S ∈ shapes) (u : CoverSample L t)
    (hnot : S ∉ tupleShapes (liftSample L u))
    (hlarge : 2 * D * h < (S ∩ crossPoints (liftSample L u)).card) :
    ∃ left right : Fin h ↪ Fin t, ∀ k,
      (u (Sum.inl (left k)), u (Sum.inr (right k))) ∈ shapePairs L S := by
  classical
  let a := liftSample L u
  let C := S ∩ crossPoints a
  have hrepr (x : ↥C) : ∃ i j : Fin t,
      Incidence x.val (a (Sum.inl i)) ∧ Incidence x.val (a (Sum.inr j)) :=
    (mem_crossPoints a x.val).mp (Finset.mem_inter.mp x.property).2
  let left : ↥C → Fin t := fun x => Classical.choose (hrepr x)
  let right : ↥C → Fin t :=
    fun x => Classical.choose (Classical.choose_spec (hrepr x))
  have hinc (x : ↥C) :
      Incidence x.val (a (Sum.inl (left x))) ∧
        Incidence x.val (a (Sum.inr (right x))) :=
    Classical.choose_spec (Classical.choose_spec (hrepr x))
  have hne (slot : Fin t ⊕ Fin t) : S ≠ linePoints (a slot) :=
    shape_ne_linePoints_of_not_mem_tupleShapes a hnot slot
  have hfiber (coord : ↥C → Fin t) (side : Fin t → Fin t ⊕ Fin t)
      (hcoord : ∀ x : ↥C, Incidence x.val (a (side (coord x)))) (i : Fin t) :
      ((Finset.univ : Finset ↥C).filter fun x => coord x = i).card ≤ D := by
    calc
      _ ≤ (S ∩ linePoints (a (side i))).card := by
        apply Finset.card_le_card_of_injOn (fun x : ↥C => x.val)
        · intro x hx
          refine Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp x.property).1, ?_⟩
          apply (mem_linePoints x.val (a (side i))).mpr
          simpa only [(Finset.mem_filter.mp hx).2] using hcoord x
        · intro x _ y _ hxy
          exact Subtype.ext hxy
      _ ≤ D := hSparse S hS (a (side i)) (hne (side i))
  have hlarge' : 2 * D * h < (Finset.univ : Finset ↥C).card := by
    simpa only [Finset.card_univ, Fintype.card_coe] using hlarge
  obtain ⟨e, hleft, hright⟩ := exists_disjoint_coordinate_sample
    (Finset.univ : Finset ↥C) left right D h
    (hfiber left Sum.inl (fun x => (hinc x).1))
    (hfiber right Sum.inr (fun x => (hinc x).2)) hlarge'
  let i : Fin h ↪ Fin t := ⟨fun k => left (e k).val, hleft⟩
  let j : Fin h ↪ Fin t := ⟨fun k => right (e k).val, hright⟩
  refine ⟨i, j, ?_⟩
  intro k
  let x : ↥C := (e k).val
  apply (mem_shapePairs L S _).mpr
  refine ⟨?_, hne (Sum.inl (i k)), hne (Sum.inr (j k)),
    x.val, (Finset.mem_inter.mp x.property).1, (hinc x).1, (hinc x).2⟩
  intro heq
  have hslots := u.injective heq
  cases hslots

theorem prob_shape_occupancy_le
    (shapes : Finset (Finset (Point F))) (L : Finset (AffineLine F))
    {D R h t : ℕ} [Nonempty (CoverSample L t)]
    (hSparse : SparseShapes shapes D)
    (hR : ∀ p : ProjectivePoint F, (coverPencil L p).card ≤ R)
    {S : Finset (Point F)} (hS : S ∈ shapes) :
    (FiniteLaw.uniform (CoverSample L t)).prob (fun u =>
      S ∉ tupleShapes (liftSample L u) ∧
        2 * D * h < (S ∩ crossPoints (liftSample L u)).card) ≤
      (t : ℝ) ^ (2 * h) * ((L.card * D * R : ℕ) : ℝ) ^ h /
        (L.card.descFactorial (2 * h) : ℝ) := by
  classical
  let μ := FiniteLaw.uniform (CoverSample L t)
  have hcard : ((shapePairs L S).card : ℝ) ≤ ((L.card * D * R : ℕ) : ℝ) :=
    Nat.cast_le.mpr (card_shapePairs_le shapes L hSparse hR hS)
  calc
    _ ≤ μ.prob (fun u => ∃ left right : Fin h ↪ Fin t, ∀ k,
        (u (Sum.inl (left k)), u (Sum.inr (right k))) ∈ shapePairs L S) := by
      apply μ.prob_mono
      intro u hu
      exact exists_disjoint_shapePairs_of_occupancy shapes L hSparse hS u hu.1 hu.2
    _ ≤ (t : ℝ) ^ (2 * h) * ((shapePairs L S).card : ℝ) ^ h /
        (L.card.descFactorial (2 * h) : ℝ) := by
      simpa only [Fintype.card_coe] using
        (InjectionSampling.prob_exists_disjoint_pairs_le
          (h := h) (t := t) (shapePairs L S))
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard h)
        (pow_nonneg (Nat.cast_nonneg _) (2 * h))

theorem prob_bad_occupancy_le
    (shapes : Finset (Finset (Point F))) (L : Finset (AffineLine F))
    {D R h t : ℕ} [Nonempty (CoverSample L t)]
    (hSparse : SparseShapes shapes D)
    (hR : ∀ p : ProjectivePoint F, (coverPencil L p).card ≤ R) :
    (FiniteLaw.uniform (CoverSample L t)).prob (fun u =>
      ∃ S ∈ shapes, S ∉ tupleShapes (liftSample L u) ∧
        2 * D * h < (S ∩ crossPoints (liftSample L u)).card) ≤
      (shapes.card : ℝ) * (t : ℝ) ^ (2 * h) * ((L.card * D * R : ℕ) : ℝ) ^ h /
        (L.card.descFactorial (2 * h) : ℝ) := by
  classical
  let μ := FiniteLaw.uniform (CoverSample L t)
  calc
    _ = μ.prob (fun u => ∃ S : ↥shapes,
        S.val ∉ tupleShapes (liftSample L u) ∧
          2 * D * h < (S.val ∩ crossPoints (liftSample L u)).card) := by
      congr 1
      funext u
      apply propext
      constructor
      · rintro ⟨S, hS, hbad⟩
        exact ⟨⟨S, hS⟩, hbad⟩
      · rintro ⟨S, hbad⟩
        exact ⟨S.val, S.property, hbad⟩
    _ ≤ ∑ S : ↥shapes, μ.prob (fun u =>
        S.val ∉ tupleShapes (liftSample L u) ∧
          2 * D * h < (S.val ∩ crossPoints (liftSample L u)).card) :=
      μ.prob_exists_le _
    _ ≤ ∑ _S : ↥shapes,
        (t : ℝ) ^ (2 * h) * ((L.card * D * R : ℕ) : ℝ) ^ h /
          (L.card.descFactorial (2 * h) : ℝ) := by
      apply Finset.sum_le_sum
      intro S _
      exact prob_shape_occupancy_le shapes L hSparse hR S.property
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      ring

end RyserCoveringCounterexample.LineCover

end

end OAI
