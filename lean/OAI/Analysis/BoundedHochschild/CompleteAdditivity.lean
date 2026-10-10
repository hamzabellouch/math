import OAI.Analysis.BoundedHochschild.ProjectionPositivity

namespace OAI

/-!
# Complete additivity on orthogonal projections

This is the complete-additivity condition of Ringrose, Section 4 (Takesaki's
normality criterion), expressed through the net of finite partial sums.
-/

noncomputable section

open Filter Topology

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildNormalPart

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Preservation of arbitrary orthogonal projection sums. The index universe
need only contain the set of projections of the algebra. -/
def CompletelyAdditive (F : StrongDual ℂ M) : Prop :=
  ∀ (I : Type u) (p : I → M), (∀ i, IsStarProjection (p i)) →
    (∀ i j, i ≠ j → p i * p j = 0) →
    ∀ P : M, IsStarProjection P → (∀ i, p i ≤ P) →
      (∀ r : M, IsStarProjection r → (∀ i, p i ≤ r) → P ≤ r) →
      Tendsto (fun s : Finset I => ∑ i ∈ s, F (p i)) atTop (𝓝 (F P))

lemma normal_completelyAdditive (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {F : StrongDual ℂ M} (hF : F ∈ normalDual e) : CompletelyAdditive F := by
  classical
  intro I p hp horth P hP hu hl
  obtain ⟨Q, hQ, hqu, hql, ht⟩ := exists_orthogonal_projection_sum e p hp horth
  have hQP : Q = P := le_antisymm (hql P hP hu) (hl Q hQ hqu)
  subst Q
  obtain ⟨z, hz⟩ := (mem_normalDual e F).mp hF
  have hconv : Tendsto (fun s : Finset I => F (∑ i ∈ s, p i)) atTop (𝓝 (F P)) := by
    simpa only [hz] using (ht z).star
  simpa only [map_sum] using hconv

omit [StarOrderedRing M] in
lemma CompletelyAdditive.add {F G : StrongDual ℂ M} (hF : CompletelyAdditive F)
    (hG : CompletelyAdditive G) : CompletelyAdditive (F + G) := by
  classical
  intro I p hp ho P hP hu hl
  simpa only [add_apply, Finset.sum_add_distrib] using
    (hF I p hp ho P hP hu hl).add (hG I p hp ho P hP hu hl)

omit [StarOrderedRing M] in
lemma CompletelyAdditive.sub {F G : StrongDual ℂ M} (hF : CompletelyAdditive F)
    (hG : CompletelyAdditive G) : CompletelyAdditive (F - G) := by
  classical
  intro I p hp ho P hP hu hl
  simpa only [sub_apply, Finset.sum_sub_distrib] using
    (hF I p hp ho P hP hu hl).sub (hG I p hp ho P hP hu hl)

/-- A completely additive hermitian functional has a maximal positive
projection corner inside any given projection (Ringrose, Lemma 4.1). Here
positivity is first recorded on subprojections. -/
theorem exists_nonnegative_projection_corner (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (F : StrongDual ℂ M) (hF : CompletelyAdditive F) {E : M} (hE : IsStarProjection E) :
    ∃ p : M, IsStarProjection p ∧ p ≤ E ∧ (F E).re ≤ (F p).re ∧
      ∀ q : M, IsStarProjection q → q ≤ p → 0 ≤ (F q).re := by
  classical
  let A : Set (Set M) := {S | (∀ p ∈ S, IsStarProjection p ∧ p ≤ E ∧ (F p).re < 0) ∧
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
  let f : S → M := Subtype.val
  have hp (i : S) : IsStarProjection (f i) := (hS.1.1 i i.property).1
  have ho (i j : S) (hij : i ≠ j) : f i * f j = 0 :=
    hS.1.2 i i.property j j.property (fun h => hij (Subtype.ext h))
  obtain ⟨P, hP, hPu, hPl, _⟩ := exists_orthogonal_projection_sum e f hp ho
  have hPE : P ≤ E := hPl E hE (fun i => (hS.1.1 i i.property).2.1)
  have hsum := hF S f hp ho P hP hPu hPl
  have hPneg : (F P).re ≤ 0 := by
    apply le_of_tendsto (Complex.continuous_re.tendsto _ |>.comp hsum)
    apply Eventually.of_forall
    intro s
    change (∑ i ∈ s, F (f i)).re ≤ 0
    change Complex.reCLM (∑ i ∈ s, F (f i)) ≤ 0
    rw [map_sum]
    exact Finset.sum_nonpos (fun i _ => (hS.1.1 i i.property).2.2.le)
  have hEP : IsStarProjection (E - P) := (hP.le_iff_sub hE).mp hPE
  refine ⟨E - P, hEP, ?_, ?_, ?_⟩
  · exact sub_le_self E hP.nonneg
  · rw [map_sub, Complex.sub_re]
    linarith
  · intro q hq hqEP
    by_contra hqneg
    have hqn : (F q).re < 0 := lt_of_not_ge hqneg
    have hqE : q ≤ E := hqEP.trans (sub_le_self E hP.nonneg)
    have hPq : P * q = 0 := HochschildCentralComparison.orthogonal_of_le_sub hE hP hq hPE hqEP
    have hfq (i : S) : f i * q = 0 := by
      calc
        f i * q = (f i * P) * q := by rw [((hp i).le_iff_mul_eq_left hP).mp (hPu i)]
        _ = 0 := by rw [mul_assoc, hPq, mul_zero]
    have hqf (i : S) : q * f i = 0 := by
      simpa only [star_mul, (hp i).isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq,
        star_zero] using congrArg star (hfq i)
    have hnew : insert q S ∈ A := by
      constructor
      · intro a ha
        rcases Set.mem_insert_iff.mp ha with rfl | ha
        · exact ⟨hq, hqE, hqn⟩
        · exact hS.1.1 a ha
      · intro a ha b hb hab
        rcases Set.mem_insert_iff.mp ha with har | ha
        · subst a
          rcases Set.mem_insert_iff.mp hb with hbr | hb
          · exact (hab hbr.symm).elim
          · exact hqf ⟨b, hb⟩
        · rcases Set.mem_insert_iff.mp hb with hbr | hb
          · subst b
            exact hfq ⟨a, ha⟩
          · exact hS.1.2 a ha b hb hab
    have hsubset : insert q S ⊆ S := hS.2 hnew (Set.subset_insert q S)
    have hqin : q ∈ S := hsubset (Set.mem_insert q S)
    have hq0 : q = 0 := by simpa only [f, hq.isIdempotentElem.eq] using hfq ⟨q, hqin⟩
    simp only [hq0, map_zero, Complex.zero_re, lt_self_iff_false] at hqn

end KadisonRingrose
end BoundedHochschild

end

end OAI
