import OAI.Analysis.BoundedHochschild.TypeICentralSupport
import OAI.Analysis.BoundedHochschild.FiniteCentralDecomposition

namespace OAI

/-!
# The central type I cut

Central type I summands are closed under chain suprema and orthogonal sums.
A maximal one therefore has a complementary corner with no abelian
projections, and in particular no type I central part. All constructions
use the given predual and require no trace.
-/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open FinitePathMain HochschildCorners

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- A central projection meeting a type I summand contains an abelian projection. -/
lemma typeICentral_witness {p c : M} (hp : TypeICentralSummand p)
    (hc : CentralProjection c) (hzero : c * p ≠ 0) :
    ∃ a : M, AbelianProjection a ∧ a ≤ c ∧ a ≠ 0 := by
  have hcp : CentralProjection (c * p) :=
    ⟨hc.1.mul hp.1.1 (hc.2 p), fun a => (hc.2 a).mul_left (hp.1.2 a)⟩
  have hcpp : c * p ≤ p := (hcp.1.le_iff_mul_eq_left hp.1.1).mpr
    (by rw [mul_assoc, hp.1.1.isIdempotentElem.eq])
  have hcpc : c * p ≤ c := (hcp.1.le_iff_mul_eq_right hc.1).mpr
    (by rw [← mul_assoc, hc.1.isIdempotentElem.eq])
  obtain ⟨a, ha, hap, ha0⟩ := hp.2 (c * p) hcp hcpp hzero
  exact ⟨a, ha, hap.trans hcpc, ha0⟩

lemma typeICentral_chain_sup (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (S : Set M) (hne : S.Nonempty) (hchain : IsChain (· ≤ ·) S)
    (hS : ∀ q ∈ S, TypeICentralSummand q) :
    ∃ p : M, TypeICentralSummand p ∧ ∀ q ∈ S, q ≤ p := by
  obtain ⟨p, hp, hpc, hub, _, hann⟩ := exists_central_projection_chain_supremum
    e S hne hchain (fun q hq => (hS q hq).1.1)
      (fun q hq a => ((hS q hq).1.2 a).eq)
  refine ⟨p, ⟨⟨hp, fun a => hpc a⟩, ?_⟩, hub⟩
  intro c hc hcp hc0
  have hex : ∃ q ∈ S, c * q ≠ 0 := by
    by_contra hn
    push Not at hn
    have hpc0 := hann c (fun q hq => by rw [← (hc.2 q).eq]; exact hn q hq)
    exact hc0 (by rwa [(hc.1.le_iff_mul_eq_right hp).mp hcp] at hpc0)
  obtain ⟨q, hq, hcq⟩ := hex
  exact typeICentral_witness (hS q hq) hc hcq

lemma typeICentral_orthogonal_sum {p q : M}
    (hp : TypeICentralSummand p) (hq : TypeICentralSummand q) (hpq : p * q = 0) :
    TypeICentralSummand (p + q) := by
  have hsum : CentralProjection (p + q) :=
    ⟨hp.1.1.add hq.1.1 hpq, fun a => (hp.1.2 a).add_left (hq.1.2 a)⟩
  refine ⟨hsum, ?_⟩
  intro c hc hcle hc0
  by_cases hcp : c * p = 0
  · have hcq : c * q ≠ 0 := by
      intro hzero
      have h := (hc.1.le_iff_mul_eq_left hsum.1).mp hcle
      rw [mul_add, hcp, hzero, zero_add] at h
      exact hc0 h.symm
    exact typeICentral_witness hq hc hcq
  · exact typeICentral_witness hp hc hcp

/-- There is a maximal central type I summand. -/
theorem exists_maximal_typeI_central_cut (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    ∃ p : M, TypeICentralSummand p ∧
      ∀ q : M, TypeICentralSummand q → q ≤ 1 - p → q = 0 := by
  classical
  let S : Set M := {p | TypeICentralSummand p}
  have hz : (0 : M) ∈ S := by
    refine ⟨⟨IsStarProjection.zero M, fun _ => Commute.zero_left _⟩, ?_⟩
    intro c hc hc0 hcn
    exact (hcn (le_antisymm hc0 hc.1.nonneg)).elim
  obtain ⟨p, _, hmax⟩ := zorn_le_nonempty₀ S (fun c hc hchain a ha => by
    obtain ⟨s, hs, hupper⟩ := typeICentral_chain_sup e c ⟨a, ha⟩ hchain
      (fun q hq => hc hq)
    exact ⟨s, hs, hupper⟩) 0 hz
  refine ⟨p, hmax.1, ?_⟩
  intro q hq hqp
  have hpq := HochschildTypeII.projection_orthogonal_of_le_complement
    hmax.1.1.1 hq.1.1 hqp
  have hs : p + q ∈ S := typeICentral_orthogonal_sum hmax.1 hq hpq
  have hle : p ≤ p + q := le_add_of_nonneg_right hq.1.1.nonneg
  have he : p + q = p := le_antisymm (hmax.2 hs hle) hle
  exact add_eq_left.mp he

omit [PartialOrder M] [StarOrderedRing M] in
/-- The two corner formulations of an abelian projection agree in the direction needed here. -/
lemma finitePath_abelian_of_popa {p : M} (hp : IsStarProjection p)
    (h : PopaTypeII.AbelianProjection hp) : AbelianProjection p := by
  refine ⟨hp, fun a b => ?_⟩
  let A : PopaCorner.algebra hp := ⟨p * a * p, compress_mem_corner hp a⟩
  let B : PopaCorner.algebra hp := ⟨p * b * p, compress_mem_corner hp b⟩
  exact congrArg Subtype.val (h A B).eq

omit [PartialOrder M] [StarOrderedRing M] in
/-- An abelian projection in a central corner is abelian in the ambient algebra. -/
lemma centralCorner_abelian_to_ambient {p : M} (hp : IsStarProjection p)
    (hc : ∀ a : M, p * a = a * p) (q : Corner p hp)
    (hq : AbelianProjection q) : AbelianProjection (q : M) := by
  have hqp : IsStarProjection (q : M) :=
    ⟨congrArg Subtype.val hq.1.isIdempotentElem.eq,
      congrArg Subtype.val hq.1.isSelfAdjoint.star_eq⟩
  refine ⟨hqp, fun a b => ?_⟩
  have h := congrArg Subtype.val
    (hq.2 (CentralCorner.compressMap p hp hc a) (CentralCorner.compressMap p hp hc b)).eq
  change ((q : M) * (p * a) * (q : M)) * ((q : M) * (p * b) * (q : M)) =
    ((q : M) * (p * b) * (q : M)) * ((q : M) * (p * a) * (q : M)) at h
  have hcut (x : M) : (q : M) * (p * x) * (q : M) = (q : M) * x * (q : M) := by
    rw [← mul_assoc, q.property.2]
  change ((q : M) * a * (q : M)) * ((q : M) * b * (q : M)) =
    ((q : M) * b * (q : M)) * ((q : M) * a * (q : M))
  simpa only [hcut] using h

/-- A central type I summand of a central corner remains type I in the ambient algebra. -/
lemma centralCorner_typeI_to_ambient {p : M} (hp : IsStarProjection p)
    (hc : ∀ a : M, p * a = a * p) (q : Corner p hp)
    (hq : TypeICentralSummand q) : TypeICentralSummand (q : M) := by
  have hqp : IsStarProjection (q : M) :=
    ⟨congrArg Subtype.val hq.1.1.isIdempotentElem.eq,
      congrArg Subtype.val hq.1.1.isSelfAdjoint.star_eq⟩
  refine ⟨⟨hqp, fun a => centralCorner_central hp hc q
    (fun b => (hq.1.2 b).eq) a⟩, ?_⟩
  intro c hcp hcle hc0
  have hqp_le : (q : M) ≤ p := (hqp.le_iff_mul_eq_right hp).mpr q.property.1
  have hclep := hcle.trans hqp_le
  let cC : Corner p hp := ⟨c,
    (hcp.1.le_iff_mul_eq_right hp).mp hclep,
    (hcp.1.le_iff_mul_eq_left hp).mp hclep⟩
  have hcC : CentralProjection cC := by
    refine ⟨⟨Subtype.ext hcp.1.isIdempotentElem.eq,
      Subtype.ext hcp.1.isSelfAdjoint.star_eq⟩, ?_⟩
    intro a
    exact Subtype.ext (hcp.2 (a : M)).eq
  have hcC0 : cC ≠ 0 := fun h => hc0 (congrArg Subtype.val h)
  obtain ⟨a, ha, hac, ha0⟩ := hq.2 cC hcC hcle hcC0
  refine ⟨(a : M), centralCorner_abelian_to_ambient hp hc a ha, hac, ?_⟩
  intro h
  exact ha0 (Subtype.ext h)

/-- The complement of a maximal type I cut has no nonzero abelian corner. -/
theorem exists_typeI_central_cut (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    ∃ (p : M) (hp : IsStarProjection p), (∀ a : M, p * a = a * p) ∧
      TypeICentralSummand p ∧
      PopaTypeII.NoAbelianCorners (Corner (1 - p) hp.one_sub) ∧
      PopaTypeII.NoTypeICentralPart (Corner (1 - p) hp.one_sub) := by
  obtain ⟨p, hp, hmax⟩ := exists_maximal_typeI_central_cut e
  have hpc : ∀ a : M, p * a = a * p := fun a => (hp.1.2 a).eq
  have hcomp : ∀ a : M, (1 - p) * a = a * (1 - p) := by
    intro a
    simp only [sub_mul, mul_sub, one_mul, mul_one, hpc]
  let N := Corner (1 - p) hp.1.1.one_sub
  have hnoAb : PopaTypeII.NoAbelianCorners N := by
    intro r hr hr0
    by_contra hn
    push Not at hn
    have hab : PopaTypeII.AbelianProjection hr := fun a b => hn a b
    obtain ⟨z, hz, _, hz0⟩ := exists_typeI_support
      (cornerPredualEquiv (1 - p) hp.1.1.one_sub e) (finitePath_abelian_of_popa hr hab) hr0
    have hzM := centralCorner_typeI_to_ambient hp.1.1.one_sub hcomp z hz
    have hzle : (z : M) ≤ 1 - p := (hzM.1.1.le_iff_mul_eq_right hp.1.1.one_sub).mpr
      z.property.1
    exact hz0 (Subtype.ext (hmax (z : M) hzM hzle))
  refine ⟨p, hp.1.1, hpc, hp, hnoAb, ?_⟩
  intro z hz _hzc hz0 hI
  obtain ⟨q, hq, _, hq0, hqa⟩ := hI z hz le_rfl hz0
  obtain ⟨a, b, hab⟩ := hnoAb q hq hq0
  exact hab (hqa a b)

end KadisonRingrose
end BoundedHochschild

end

end OAI
