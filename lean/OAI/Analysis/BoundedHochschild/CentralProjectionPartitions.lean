import OAI.Analysis.BoundedHochschild.CentralProjectionSuprema
import OAI.Analysis.BoundedHochschild.PathStages

namespace OAI

/-!
# Maximal central partitions

Orthogonal central projections have a supremum obtained from their finite
sums. A maximal family of projections satisfying any prescribed property
therefore has an actual complementary central projection. This construction
does not use a trace or a countability hypothesis.
-/

noncomputable section

open Filter Topology
open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

universe u

variable {M X I : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The supremum of an arbitrary orthogonal central family preserves its common
annihilators. In particular, its complement completes the family to a partition. -/
theorem exists_orthogonal_central_supremum (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (p : I → M) (hp : ∀ i, IsStarProjection (p i))
    (hc : ∀ i a, p i * a = a * p i)
    (horth : ∀ i j, i ≠ j → p i * p j = 0) :
    ∃ q : M, IsStarProjection q ∧ (∀ a : M, q * a = a * q) ∧
      (∀ i, p i * q = p i) ∧
      (∀ a : M, (∀ i, p i * a = 0) → q * a = 0) := by
  classical
  let s (t : Finset I) : M := ∑ i ∈ t, p i
  let U : Ultrafilter (Finset I) := Ultrafilter.of atTop
  have hU : (U : Filter (Finset I)) ≤ atTop := Ultrafilter.of_le atTop
  have hn (t : Finset I) : ‖s t‖ ≤ 1 :=
    supported_sum_norm_le p p hp horth
      (fun i => (hp i).isIdempotentElem.eq)
      (fun i => (hp i).isIdempotentElem.eq) t 1 (by norm_num)
      (fun i _ => (hp i).norm_le)
  obtain ⟨q, _, ht⟩ := exists_predual_ultralimit e U s 1 hn
  have hfixed (i : I) : p i * q = p i := by
    have hm := HochschildSakai.predual_tendsto_mul_left e (p i) ht
    have heq : (fun t => p i * s t) =ᶠ[U] (fun _ => p i) := by
      apply hU
      filter_upwards [eventually_ge_atTop ({i} : Finset I)] with t hit
      have hi : i ∈ t := hit (Finset.mem_singleton_self i)
      simp only [s, Finset.mul_sum]
      rw [Finset.sum_eq_single i]
      · exact (hp i).isIdempotentElem.eq
      · intro j _ hji
        exact horth i j hji.symm
      · exact fun h => (h hi).elim
    apply predual_tendsto_unique e hm
    intro z
    exact tendsto_const_nhds.congr' (heq.mono fun _ h =>
      congrArg (fun a : M => e.symm a z) h.symm)
  have hqc (a : M) : q * a = a * q := by
    have hl := HochschildSakai.predual_tendsto_mul_left e a ht
    have hr := HochschildSakai.predual_tendsto_mul_right e a ht
    have heq : (fun t => a * s t) = (fun t => s t * a) := by
      funext t
      simp only [s, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun i _ => (hc i a).symm)
    rw [heq] at hl
    exact predual_tendsto_unique e hr hl
  have hq : IsStarProjection q := by
    constructor
    · have hm := HochschildSakai.predual_tendsto_mul_right e q ht
      have heq : (fun t => s t * q) = s := by
        funext t
        simp only [s, Finset.sum_mul, hfixed]
      rw [heq] at hm
      exact predual_tendsto_unique e hm ht
    · have hs := HochschildSakai.predual_tendsto_star e ht
      have heq : (fun t => star (s t)) = s := by
        funext t
        simp only [s, star_sum, fun i => (hp i).isSelfAdjoint.star_eq]
      rw [heq] at hs
      exact predual_tendsto_unique e hs ht
  refine ⟨q, hq, hqc, hfixed, ?_⟩
  intro a ha
  have hm := HochschildSakai.predual_tendsto_mul_right e a ht
  have heq : (fun t => s t * a) = (fun _ => (0 : M)) := by
    funext t
    simp only [s, Finset.sum_mul, ha, Finset.sum_const_zero]
  rw [heq] at hm
  exact predual_tendsto_unique e hm (predual_tendsto_const e 0 (U : Filter (Finset I)))

/-- A maximal family satisfying `P`, together with its actual central complement. -/
structure MaximalCentralPartition (M : Type u) [CStarAlgebra M]
    [PartialOrder M] [StarOrderedRing M] (P : M → Prop) where
  Index : Type u
  projection : Index → M
  isProjection : ∀ i, IsStarProjection (projection i)
  central : ∀ i a, projection i * a = a * projection i
  nonzero : ∀ i, projection i ≠ 0
  property : ∀ i, P (projection i)
  orthogonal : ∀ i j, i ≠ j → projection i * projection j = 0
  complement : M
  complement_isProjection : IsStarProjection complement
  complement_central : ∀ a, complement * a = a * complement
  complement_orthogonal : ∀ i, projection i * complement = 0
  total : ∀ a, complement * a = 0 → (∀ i, projection i * a = 0) → a = 0
  maximal : ∀ q : M, IsStarProjection q → (∀ a, q * a = a * q) →
    q ≤ complement → P q → q = 0

/-- Zorn's lemma and bounded weak-star limits provide a maximal central partition. -/
theorem exists_maximal_central_partition (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (P : M → Prop) : Nonempty (MaximalCentralPartition M P) := by
  classical
  let A : Set (Set M) := {S | (∀ p ∈ S, IsStarProjection p ∧
    (∀ a : M, p * a = a * p) ∧ p ≠ 0 ∧ P p) ∧
    ∀ p ∈ S, ∀ q ∈ S, p ≠ q → p * q = 0}
  obtain ⟨S, hS⟩ := zorn_subset A (fun c hc hchain => by
    refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
    · intro p hp
      obtain ⟨s, hs, hps⟩ := Set.mem_sUnion.mp hp
      exact (hc hs).1 p hps
    · intro p hp q hq hpq
      obtain ⟨s, hs, hps⟩ := Set.mem_sUnion.mp hp
      obtain ⟨t, ht, hqt⟩ := Set.mem_sUnion.mp hq
      rcases hchain.total hs ht with hst | hts
      · exact (hc ht).2 p (hst hps) q hqt hpq
      · exact (hc hs).2 p hps q (hts hqt) hpq)
  let p : S → M := Subtype.val
  have hp (i : S) : IsStarProjection (p i) := (hS.1.1 i i.property).1
  have hc (i : S) (a : M) : p i * a = a * p i := (hS.1.1 i i.property).2.1 a
  have hn (i : S) : p i ≠ 0 := (hS.1.1 i i.property).2.2.1
  have hP (i : S) : P (p i) := (hS.1.1 i i.property).2.2.2
  have ho (i j : S) (hij : i ≠ j) : p i * p j = 0 :=
    hS.1.2 i i.property j j.property (fun h => hij (Subtype.ext h))
  obtain ⟨q, hq, hqc, hfixed, hann⟩ := exists_orthogonal_central_supremum e p hp hc ho
  have hcomp (i : S) : p i * (1 - q) = 0 := by
    rw [mul_sub, mul_one, hfixed, sub_self]
  refine ⟨{
    Index := S
    projection := p
    isProjection := hp
    central := hc
    nonzero := hn
    property := hP
    orthogonal := ho
    complement := 1 - q
    complement_isProjection := hq.one_sub
    complement_central := fun a => by
      simp only [sub_mul, mul_sub, one_mul, mul_one, hqc]
    complement_orthogonal := hcomp
    total := ?_
    maximal := ?_ }⟩
  · intro a hca hpa
    have hqa := hann a hpa
    simpa only [sub_mul, one_mul, hqa, sub_zero] using hca
  · intro r hr hrc hrq hPr
    by_contra hr0
    have hrr : ∀ i : S, p i * r = 0 := by
      have hqr : (1 - q) * r = r := (hr.le_iff_mul_eq_right hq.one_sub).mp hrq
      intro i
      calc
        p i * r = p i * ((1 - q) * r) := by rw [hqr]
        _ = 0 := by rw [← mul_assoc, hcomp, zero_mul]
    have hnew : insert r S ∈ A := by
      constructor
      · intro a ha
        rcases Set.mem_insert_iff.mp ha with rfl | ha
        · exact ⟨hr, hrc, hr0, hPr⟩
        · exact hS.1.1 a ha
      · intro a ha b hb hab
        rcases Set.mem_insert_iff.mp ha with har | ha
        · subst a
          rcases Set.mem_insert_iff.mp hb with hbr | hb
          · exact (hab hbr.symm).elim
          · exact (hrc b).trans (hrr ⟨b, hb⟩)
        · rcases Set.mem_insert_iff.mp hb with hbr | hb
          · subst b
            exact hrr ⟨a, ha⟩
          · exact hS.1.2 a ha b hb hab
    have hsubset : insert r S ⊆ S := hS.2 hnew (Set.subset_insert r S)
    have hrS : r ∈ S := hsubset (Set.mem_insert r S)
    exact hr0 (by simpa only [p, hr.isIdempotentElem.eq] using hrr ⟨r, hrS⟩)

end KadisonRingrose
end BoundedHochschild

end

end OAI
