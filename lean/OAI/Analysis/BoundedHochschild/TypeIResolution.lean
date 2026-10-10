import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.BoundedHochschild.FactorPrimitive
import OAI.Analysis.BoundedHochschild.TypeIICorners
import OAI.Analysis.BoundedHochschild.CenterPowers
import OAI.Analysis.BoundedHochschild.CommutativePrimitives
import OAI.Analysis.BoundedHochschild.AtomicPrimitives
import OAI.Analysis.BoundedHochschild.TypeIBlocks

namespace OAI

/-!
# Orthogonal homogeneous resolutions of finite type-I algebras

A maximal orthogonal family of homogeneous central blocks separates points: a nonzero
central complement would contain another block by the type-I hypothesis.
-/

noncomputable section

open scoped ComplexOrder
namespace HochschildTypeILocal
open BoundedHochschild HochschildTypeII FinitePathMain
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

omit [PartialOrder M] [StarOrderedRing M] in
lemma exists_maximal_homogeneous_family :
    ∃ s : Set M, (∀ z∈s, HomogeneousBlock z) ∧ s.Pairwise (fun z w => z*w=0) ∧
      ∀ r : M, HomogeneousBlock r → (∀ z∈s, r*z=0) → False := by
  classical
  let S : Set (Set M) := {s | (∀ z∈s, HomogeneousBlock z) ∧ s.Pairwise (fun z w => z*w=0)}
  obtain ⟨s,hs⟩ := zorn_subset S (fun c hc hchain => by
    refine ⟨⋃₀ c,⟨?_,?_⟩,fun t ht => Set.subset_sUnion_of_mem ht⟩
    · rintro z ⟨t,ht,hzt⟩
      exact (hc ht).1 z hzt
    · rintro z ⟨t,ht,hzt⟩ w ⟨v,hv,hwv⟩ hne
      by_cases htv : t=v
      · subst v; exact (hc ht).2 hzt hwv hne
      rcases hchain ht hv htv with hsub | hsub
      · exact (hc hv).2 (hsub hzt) hwv hne
      · exact (hc ht).2 hzt (hsub hwv) hne)
  refine ⟨s,hs.1.1,hs.1.2,?_⟩
  intro r hr horth
  have hnew : insert r s ∈ S := by
    refine ⟨?_,?_⟩
    · intro z hz
      rcases hz with he | hz
      · simpa only [he] using hr
      · exact hs.1.1 z hz
    · intro z hz w hw hne
      rcases hz with he | hz
      · subst z
        rcases hw with hew | hw
        · exact (hne hew.symm).elim
        · exact horth w hw
      · rcases hw with hew | hw
        · subst w
          exact (hr.central.2 z).eq.symm.trans (horth z hz)
        · exact hs.1.2 hz hw hne
  have hrs : r∈s := hs.2 hnew (Set.subset_insert r s) (Set.mem_insert r s)
  exact hr.nonzero (hr.central.1.isIdempotentElem.eq.symm.trans (horth r hrs))

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
include e in

theorem exists_homogeneous_resolution
    (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (hI : TypeICentralSummand (1:M)) :
    ∃ s : Set M, (∀ z∈s, HomogeneousBlock z) ∧ s.Pairwise (fun z w => z*w=0) ∧
      ∀ x : M, (∀ z∈s, z*x=0) → x=0 := by
  classical
  obtain ⟨s,hs,horth,hmaxs⟩ := exists_maximal_homogeneous_family (M:=M)
  refine ⟨s,hs,horth,?_⟩
  intro x hx
  let S : Set M := {q | CentralProjection q ∧ q*x=0}
  have hz : (0:M) ∈ S := ⟨⟨IsStarProjection.zero M,fun _ => Commute.zero_left _⟩,zero_mul _⟩
  obtain ⟨q,_hq0,hmax⟩ := zorn_le_nonempty₀ S (fun c hc hchain y hy => by
    obtain ⟨q,hq,hqx,hupper⟩ := central_annihilator_chain e τ hτ htr hfaith
      x c hchain ⟨y,hy⟩ (fun p hp => hc hp)
    exact ⟨q,⟨hq,hqx⟩,hupper⟩) 0 hz
  have hq : CentralProjection q := hmax.1.1
  have hqx : q*x=0 := hmax.1.2
  have hle (z : M) (hzs : z∈s) : z≤q := by
    have hzc := (hs z hzs).central
    have hr : CentralProjection ((1-q)*z) :=
      ⟨hq.1.one_sub.mul hzc.1 ((Commute.one_left z).sub_left (hq.2 z)),
        fun a => ((Commute.one_left a).sub_left (hq.2 a)).mul_left (hzc.2 a)⟩
    have hqr : q*((1-q)*z)=0 := by
      rw [← mul_assoc,mul_sub,mul_one,hq.1.isIdempotentElem.eq,sub_self,zero_mul]
    have hnew : q+(1-q)*z ∈ S := ⟨⟨hq.1.add hr.1 hqr,
      fun a => (hq.2 a).add_left (hr.2 a)⟩,by rw [add_mul,hqx,mul_assoc,hx z hzs,mul_zero,zero_add]⟩
    have he : q+(1-q)*z=q := le_antisymm (hmax.2 hnew (le_add_of_nonneg_right hr.1.nonneg))
      (le_add_of_nonneg_right hr.1.nonneg)
    have hr0 : (1-q)*z=0 := add_eq_left.mp he
    rw [sub_mul,one_mul,sub_eq_zero] at hr0
    exact (hzc.1.le_iff_mul_eq_right hq.1).mpr hr0.symm
  have he : q=1 := by
    by_contra hne
    have hc : CentralProjection (1-q) :=
      ⟨hq.1.one_sub,fun a => (Commute.one_left a).sub_left (hq.2 a)⟩
    obtain ⟨p,hp,hpc,hp0⟩ := hI.2 (1-q) hc hc.1.le_one (sub_ne_zero.mpr (Ne.symm hne))
    obtain ⟨r,hr,hrc⟩ := exists_homogeneous_block_below e τ hτ htr hfaith hc hp hpc hp0
    apply hmaxs r hr
    intro z hzs
    have hqz := ((hs z hzs).central.1.le_iff_mul_eq_right hq.1).mp (hle z hzs)
    have hqr : q*r=0 := projection_orthogonal_of_le_complement hq.1 hr.central.1 hrc
    calc
      r*z = r*(q*z) := by rw [hqz]
      _ = (r*q)*z := (mul_assoc _ _ _).symm
      _ = 0 := by rw [← (hq.2 r).eq,hqr,zero_mul]
  simpa only [he,one_mul] using hqx

end HochschildTypeILocal

end

end OAI
