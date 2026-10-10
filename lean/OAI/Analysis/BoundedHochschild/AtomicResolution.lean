import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.BoundedHochschild.FactorPrimitive
import OAI.Analysis.BoundedHochschild.TypeIICorners
import OAI.Analysis.BoundedHochschild.CenterPowers
import OAI.Analysis.BoundedHochschild.CentralAtoms

namespace OAI

/-! Orthogonal atomic central resolution. -/

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace HochschildAtomic
open BoundedHochschild HochschildTypeII FinitePathMain
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def AtomicCenter (M : Type u) [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] : Prop :=
  ∀ p : M, IsStarProjection p → (∀ a : M, Commute p a) → p ≠ 0 →
    ∃ q : M, CentralAtom q ∧ q ≤ p

lemma central_atoms_orthogonal {p q : M} (hp : CentralAtom p) (hq : CentralAtom q) (hne : p ≠ q) :
    p*q=0 := by
  have hpq : IsStarProjection (p*q) := hp.1.mul hq.1 (hp.2.1 q)
  have hc : ∀ b : M, Commute (p*q) b := fun b => (hp.2.1 b).mul_left (hq.2.1 b)
  have hpqp : p*q ≤ p := (hpq.le_iff_mul_eq_right hp.1).mpr
    (by rw [← mul_assoc,hp.1.isIdempotentElem.eq])
  have hpqq : p*q ≤ q := (hpq.le_iff_mul_eq_left hq.1).mpr
    (by rw [mul_assoc,hq.1.isIdempotentElem.eq])
  rcases hp.2.2.2 (p*q) hpq hc hpqp with hz | hpp
  · exact hz
  rcases hq.2.2.2 (p*q) hpq hc hpqq with hz | hqq
  · exact hz
  exact (hne (hpp.symm.trans hqq)).elim

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

include e in

theorem central_atoms_total
    (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (hatomic : AtomicCenter M)
    (x : M) (hx : ∀ p : M, CentralAtom p → p*x=0) : x=0 := by
  classical
  let S : Set M := {p | CentralProjection p ∧ p*x=0}
  have hzero : (0:M) ∈ S := ⟨⟨IsStarProjection.zero M,fun _ => Commute.zero_left _⟩,zero_mul _⟩
  obtain ⟨q,_hq0,hmax⟩ := zorn_le_nonempty₀ S (fun c hc hchain y hy => by
    obtain ⟨q,hq,hqx,hupper⟩ := central_annihilator_chain e τ hτ htr hfaith
      x c hchain ⟨y,hy⟩ (fun p hp => hc hp)
    exact ⟨q,⟨hq,hqx⟩,hupper⟩) 0 hzero
  have hq : CentralProjection q := hmax.1.1
  have hqx : q*x=0 := hmax.1.2
  have hone : q=1 := by
    by_contra hne
    have hr : CentralProjection (1-q) :=
      ⟨hq.1.one_sub,fun a => (Commute.one_left a).sub_left (hq.2 a)⟩
    obtain ⟨p,hp,hpq⟩ := hatomic (1-q) hr.1 hr.2 (sub_ne_zero.mpr (Ne.symm hne))
    have hqp : q*p=0 := projection_orthogonal_of_le_complement hq.1 hp.1 hpq
    have hnew : q+p ∈ S := ⟨⟨hq.1.add hp.1 hqp,fun a => (hq.2 a).add_left (hp.2.1 a)⟩,
      by rw [add_mul,hqx,hx p hp,zero_add]⟩
    have he : q+p=q := le_antisymm (hmax.2 hnew (le_add_of_nonneg_right hp.1.nonneg))
      (le_add_of_nonneg_right hp.1.nonneg)
    exact hp.2.2.1 (add_eq_left.mp he)
  simpa only [hone,one_mul] using hqx

include e in

theorem typeII_no_minimal
    (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (hII : TypeII1 M) :
    HochschildDiffuse.NoMinimalProjections M := by
  intro p hp hp0
  by_contra hn
  have hmin (q : M) (hq : IsStarProjection q) (hqp : q ≤ p) : q=0 ∨ q=p := by
    by_cases hq0 : q=0
    · exact Or.inl hq0
    · right
      by_contra hne
      exact hn ⟨q,hq,hqp,hq0,hne⟩
  have hab : AbelianProjection p := by
    refine ⟨hp,fun a b => ?_⟩
    apply HochschildCorners.commute_corner_of_projections e hp
      (b:=p*b*p) _ (HochschildCorners.compress_mem_corner hp a)
    intro q hq hqp
    rcases hmin q hq hqp with hz | he
    · rw [hz]; exact Commute.zero_left _
    · rw [he]
      change p*(p*b*p)=(p*b*p)*p
      rw [(HochschildCorners.compress_mem_corner hp b).1,
        (HochschildCorners.compress_mem_corner hp b).2]
  exact hp0 (no_abelian_projection e τ hτ htr hfaith hII hab)

end HochschildAtomic

end

end OAI
