import OAI.Analysis.BoundedHochschild.CentralProjectionSuprema
import OAI.Analysis.BoundedHochschild.Conditional

namespace OAI

/-! The maximal finite central cut, constructed without an assumed trace. -/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Finiteness of a corner, expressed in the ambient algebra. -/
def FiniteCorner (p : M) : Prop :=
  ∀ a : M, p * a = a → a * p = a → star a * a = p → a * star a = p

omit [PartialOrder M] [StarOrderedRing M] in
lemma finiteCorner_iff (p : M) (hp : IsStarProjection p) :
    FiniteCorner p ↔ FiniteAlgebra (HochschildCorners.Corner p hp) := by
  constructor
  · intro h a ha
    apply Subtype.ext
    exact h a a.property.1 a.property.2 (congrArg Subtype.val ha)
  · intro h a hL hR ha
    let b : HochschildCorners.Corner p hp := ⟨a, hL, hR⟩
    exact congrArg Subtype.val (h b (Subtype.ext ha))

omit [PartialOrder M] [StarOrderedRing M] in
lemma finiteCorner_zero : FiniteCorner (0 : M) := by
  intro a hL _ _
  have ha : a = 0 := by simpa using hL.symm
  simp [ha]

omit [PartialOrder M] [StarOrderedRing M] in
lemma finiteCorner_of_finiteAlgebra (hfinite : FiniteAlgebra M)
    (p : M) (hp : IsStarProjection p) : FiniteCorner p := by
  intro a hL hR haa
  have hsL : star a * p = star a := by
    simpa only [star_mul, hp.isSelfAdjoint.star_eq] using congrArg star hL
  have hsR : p * star a = star a := by
    simpa only [star_mul, hp.isSelfAdjoint.star_eq] using congrArg star hR
  have hca : (1 - p) * a = 0 := by rw [sub_mul, one_mul, hL, sub_self]
  have hac : a * (1 - p) = 0 := by rw [mul_sub, mul_one, hR, sub_self]
  have hcsa : (1 - p) * star a = 0 := by rw [sub_mul, one_mul, hsR, sub_self]
  have hsac : star a * (1 - p) = 0 := by rw [mul_sub, mul_one, hsL, sub_self]
  have hin : star (a + (1 - p)) * (a + (1 - p)) = 1 := by
    simp only [star_add, star_sub, star_one, hp.isSelfAdjoint.star_eq,
      add_mul, mul_add, hsac, hca, zero_add, add_zero, haa,
      hp.one_sub.isIdempotentElem.eq]
    abel
  have hout := hfinite (a + (1 - p)) hin
  simp only [star_add, star_sub, star_one, hp.isSelfAdjoint.star_eq,
    add_mul, mul_add, hac, hcsa, zero_add, add_zero,
    hp.one_sub.isIdempotentElem.eq] at hout
  have hp1 : p + (1 - p) = 1 := by abel
  exact add_right_cancel (hout.trans hp1.symm)

lemma finiteCorner_compressed_final {p q : M} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hc : ∀ b : M, q * b = b * q)
    (hqp : q ≤ p) (hfinite : FiniteCorner q)
    (a : M) (haa : star a * a = p) : q * (a * star a) = q := by
  have hL : q * (q * a) = q * a := by rw [← mul_assoc, hq.isIdempotentElem.eq]
  have hR : (q * a) * q = q * a := by rw [mul_assoc, ← hc a, hL]
  have hstar : star (q * a) = q * star a := by
    rw [star_mul, hq.isSelfAdjoint.star_eq, hc]
  have hin : star (q * a) * (q * a) = q := by
    rw [hstar, central_idempotent_mul q hq.isIdempotentElem.eq hc, haa]
    exact (hq.le_iff_mul_eq_left hp).mp hqp
  have hout := hfinite (q * a) hL hR hin
  rw [hstar, central_idempotent_mul q hq.isIdempotentElem.eq hc] at hout
  exact hout

lemma finiteCorner_orthogonal_sum {p q : M} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hcp : ∀ a : M, p * a = a * p)
    (hcq : ∀ a : M, q * a = a * q) (hpq : p * q = 0)
    (hfp : FiniteCorner p) (hfq : FiniteCorner q) : FiniteCorner (p + q) := by
  have hs := hp.add hq hpq
  intro a hL _ haa
  have hp' := finiteCorner_compressed_final hs hp hcp
    (le_add_of_nonneg_right hq.nonneg) hfp a haa
  have hq' := finiteCorner_compressed_final hs hq hcq
    (le_add_of_nonneg_left hp.nonneg) hfq a haa
  calc
    a * star a = (p + q) * (a * star a) := by rw [← mul_assoc, hL]
    _ = p + q := by rw [add_mul, hp', hq']

lemma finiteCorner_chain_sup (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (S : Set M) (hne : S.Nonempty) (hchain : IsChain (· ≤ ·) S)
    (hS : ∀ q ∈ S, IsStarProjection q ∧ (∀ a : M, q * a = a * q) ∧ FiniteCorner q) :
    ∃ p : M, IsStarProjection p ∧ (∀ a : M, p * a = a * p) ∧
      FiniteCorner p ∧ ∀ q ∈ S, q ≤ p := by
  obtain ⟨p, hp, hcp, hupper, _, hann⟩ := exists_central_projection_chain_supremum
    e S hne hchain (fun q hq => (hS q hq).1) (fun q hq => (hS q hq).2.1)
  refine ⟨p, hp, hcp, ?_, hupper⟩
  intro a hL _ haa
  have hzero : p * (p - a * star a) = 0 := by
    apply hann
    intro q hq
    rw [mul_sub, ( (hS q hq).1.le_iff_mul_eq_left hp).mp (hupper q hq),
      finiteCorner_compressed_final hp (hS q hq).1 (hS q hq).2.1
        (hupper q hq) (hS q hq).2.2 a haa, sub_self]
  rw [mul_sub, hp.isIdempotentElem.eq, ← mul_assoc, hL] at hzero
  exact (sub_eq_zero.mp hzero).symm

/-- Every W*-algebra has a finite central cut with no finite central subprojection
in its complement. This part of the classical type decomposition needs no trace. -/
theorem exists_maximal_finite_central_cut (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    ∃ p : M, IsStarProjection p ∧ (∀ a : M, p * a = a * p) ∧ FiniteCorner p ∧
      ∀ q : M, IsStarProjection q → (∀ a : M, q * a = a * q) →
        FiniteCorner q → q ≤ 1 - p → q = 0 := by
  classical
  let S : Set M := {p | IsStarProjection p ∧ (∀ a : M, p * a = a * p) ∧ FiniteCorner p}
  have hz : (0 : M) ∈ S := ⟨IsStarProjection.zero M, fun a => by simp, finiteCorner_zero⟩
  obtain ⟨p, _, hmax⟩ := zorn_le_nonempty₀ S (fun c hc hchain a ha => by
    obtain ⟨s, hs, hcs, hfs, hupper⟩ := finiteCorner_chain_sup e c ⟨a, ha⟩ hchain
      (fun q hq => hc hq)
    exact ⟨s, ⟨hs, hcs, hfs⟩, hupper⟩) 0 hz
  have hp := hmax.1.1
  have hcp := hmax.1.2.1
  have hfp := hmax.1.2.2
  refine ⟨p, hp, hcp, hfp, ?_⟩
  intro q hq hcq hfq hqp
  have hpq : p * q = 0 := by
    have h := (hq.le_iff_mul_eq_right hp.one_sub).mp hqp
    rw [sub_mul, one_mul] at h
    exact sub_eq_self.mp h
  have hs : p + q ∈ S := ⟨hp.add hq hpq,
    fun a => by rw [add_mul, mul_add, hcp, hcq],
    finiteCorner_orthogonal_sum hp hq hcp hcq hpq hfp hfq⟩
  have hle : p ≤ p + q := le_add_of_nonneg_right hq.nonneg
  have he : p + q = p := le_antisymm (hmax.2 hs hle) hle
  exact add_eq_left.mp he

omit [PartialOrder M] [StarOrderedRing M] in
lemma centralCorner_central {p : M} (hp : IsStarProjection p)
    (hc : ∀ a : M, p * a = a * p) (q : HochschildCorners.Corner p hp)
    (hqc : ∀ b : HochschildCorners.Corner p hp, q * b = b * q) :
    ∀ a : M, (q : M) * a = a * (q : M) := by
  intro a
  have h := congrArg Subtype.val (hqc (CentralCorner.compressMap p hp hc a))
  change (q : M) * (p * a) = (p * a) * (q : M) at h
  calc
    (q : M) * a = ((q : M) * p) * a := by rw [q.property.2]
    _ = (q : M) * (p * a) := mul_assoc _ _ _
    _ = (p * a) * (q : M) := h
    _ = a * (p * (q : M)) := by rw [hc a, mul_assoc]
    _ = a * (q : M) := by rw [q.property.1]

omit [PartialOrder M] [StarOrderedRing M] in
lemma finiteCorner_trans {p : M} (hp : IsStarProjection p)
    (q : HochschildCorners.Corner p hp) (hfinite : FiniteCorner q) :
    FiniteCorner (q : M) := by
  intro a hL hR haa
  have hpL : p * a = a := by
    calc
      p * a = p * ((q : M) * a) := by rw [hL]
      _ = a := by rw [← mul_assoc, q.property.1, hL]
  have hpR : a * p = a := by
    calc
      a * p = (a * (q : M)) * p := by rw [hR]
      _ = a := by rw [mul_assoc, q.property.2, hR]
  let b : HochschildCorners.Corner p hp := ⟨a, hpL, hpR⟩
  exact congrArg Subtype.val
    (hfinite b (Subtype.ext hL) (Subtype.ext hR) (Subtype.ext haa))

/-- Finiteness passes to every subprojection, without a centrality hypothesis. -/
lemma finiteCorner_mono {p q : M} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hpq : p ≤ q) (hfinite : FiniteCorner q) :
    FiniteCorner p := by
  let pC : HochschildCorners.Corner q hq :=
    ⟨p, (hp.le_iff_mul_eq_right hq).mp hpq, (hp.le_iff_mul_eq_left hq).mp hpq⟩
  have hpC : IsStarProjection pC :=
    ⟨Subtype.ext hp.isIdempotentElem.eq, Subtype.ext hp.isSelfAdjoint.star_eq⟩
  exact finiteCorner_trans hq pC
    (finiteCorner_of_finiteAlgebra ((finiteCorner_iff q hq).mp hfinite) pC hpC)

/-- The complementary corner of a maximal finite central cut has no II₁ summand. -/
theorem exists_finite_central_cut_noTypeII1 (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    ∃ (p : M) (hp : IsStarProjection p), (∀ a : M, p * a = a * p) ∧
      FiniteAlgebra (HochschildCorners.Corner p hp) ∧
      NoTypeII1Summand (HochschildCorners.Corner (1 - p) hp.one_sub) := by
  obtain ⟨p, hp, hc, hf, hmax⟩ := exists_maximal_finite_central_cut e
  refine ⟨p, hp, hc, (finiteCorner_iff p hp).mp hf, ?_⟩
  intro q hq hqc hqfinite _
  have hqM : IsStarProjection (q : M) :=
    ⟨congrArg Subtype.val hq.isIdempotentElem.eq,
      congrArg Subtype.val hq.isSelfAdjoint.star_eq⟩
  have hc' : ∀ a : M, (1 - p) * a = a * (1 - p) := by
    intro a
    simp only [sub_mul, mul_sub, one_mul, mul_one, hc]
  have hqcM := centralCorner_central hp.one_sub hc' q hqc
  have hqfiniteM : FiniteCorner (q : M) :=
    finiteCorner_trans hp.one_sub q ((finiteCorner_iff q hq).mpr hqfinite)
  have hqle : (q : M) ≤ 1 - p :=
    (hqM.le_iff_mul_eq_right hp.one_sub).mpr q.property.1
  exact Subtype.ext (hmax (q : M) hqM hqcM hqfiniteM hqle)

end KadisonRingrose
end BoundedHochschild

end

end OAI
