import OAI.Analysis.WeakInfiniteness.HalfFlipCriterion
import OAI.Analysis.WeakInfiniteness.TensorSubalgebras
import OAI.Analysis.WeakInfiniteness.CrossUniverseTensorLaws

namespace OAI

/-!
# Restricting multiplier conjugacies to a nonunital algebra

The range of the canonical map into the multiplier algebra is an ideal.
Consequently tensor conjugacies constructed in the multiplier algebra restrict
to the original, possibly nonunital, tensor product.  This is the local
nonunital step in the central-embedding absorption argument; no central
embedding or absorption statement is assumed here.
-/

noncomputable section

open scoped MultiplierAlgebra
open Filter Topology

namespace WeakPureInfiniteness

universe u v

section IdealRestriction

variable {A B : Type u} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- A formulation of right-ideal range useful for nonunital embeddings. -/
def RightIdealRange (ι : A →⋆ₙₐ[ℂ] B) : Prop :=
  ∀ a : A, ∀ b : B, ι a * b ∈ ι.range

lemma RightIdealRange.mul_left {ι : A →⋆ₙₐ[ℂ] B} (h : RightIdealRange ι)
    (a : A) (b : B) : b * ι a ∈ ι.range := by
  have hs := star_mem (h (star a) (star b))
  simpa only [star_mul, star_star, map_star] using hs

lemma RightIdealRange.inner_mem {ι : A →⋆ₙₐ[ℂ] B} (h : RightIdealRange ι)
    (u : unitary (Unitization ℂ B)) {b : B} (hb : b ∈ ι.range) :
    unitizationInnerFun u b ∈ ι.range := by
  obtain ⟨a, rfl⟩ := ι.mem_range.mp hb
  have hl : u.val.snd * ι a ∈ ι.range := h.mul_left a u.val.snd
  have hm : u.val.fst • ι a + u.val.snd * ι a ∈ ι.range :=
    ι.range.add_mem (ι.range.smul_mem _ (ι.mem_range_self a)) hl
  have hr : (u.val.fst • ι a + u.val.snd * ι a) * (star u.val).snd ∈ ι.range := by
    obtain ⟨c, hc⟩ := ι.mem_range.mp hm
    rw [← hc]
    exact h c _
  change (u.val * (ι a : Unitization ℂ B) * star u.val).snd ∈ ι.range
  simp only [Unitization.snd_mul, Unitization.fst_mul,
    Unitization.fst_inr, Unitization.snd_inr, mul_zero, zero_smul, add_zero, zero_add]
  exact ι.range.add_mem (ι.range.smul_mem (star u.val).fst hm) hr

/-- Restrict an inner automorphism of the containing algebra to its ideal. -/
def RightIdealRange.restrictInner {ι : A →⋆ₙₐ[ℂ] B} (h : RightIdealRange ι)
    (hι : Function.Injective ι) (u : unitary (Unitization ℂ B)) : A ≃⋆ₐ[ℂ] A := by
  let e := StarAlgEquiv.ofInjective' ι hι
  let f : ι.range →⋆ₙₐ[ℂ] ι.range :=
    NonUnitalStarAlgHom.codRestrict
      ((unitizationInnerHom u).comp (NonUnitalStarSubalgebraClass.subtype ι.range))
      ι.range (fun b => h.inner_mem u b.property)
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      exact (unitizationInnerEquiv u).injective (congrArg Subtype.val hxy)
    · intro b
      refine ⟨⟨unitizationInnerFun (star u) b, h.inner_mem (star u) b.property⟩, ?_⟩
      apply Subtype.ext
      change unitizationInnerFun u (unitizationInnerFun (star u) (b : B)) = (b : B)
      simpa only [star_star] using unitizationInnerFun_star_left (star u) b
  exact (e.trans (StarAlgEquiv.ofBijective f hf)).trans e.symm

lemma RightIdealRange.restrictInner_apply {ι : A →⋆ₙₐ[ℂ] B} (h : RightIdealRange ι)
    (hι : Function.Injective ι) (u : unitary (Unitization ℂ B)) (a : A) :
    ι (h.restrictInner hι u a) = unitizationInnerFun u (ι a) := by
  change ((StarAlgEquiv.ofInjective' ι hι)
    ((StarAlgEquiv.ofInjective' ι hι).symm _)).val = _
  rw [StarAlgEquiv.apply_symm_apply]
  rfl

end IdealRestriction

section Multiplier

variable (A : Type u) [NonUnitalCStarAlgebra A]

lemma multiplierInclusion_injective :
    Function.Injective (DoubleCentralizer.coeHom (𝕜 := ℂ) (A := A)) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  apply (CStarRing.mul_star_self_eq_zero_iff a).mp
  exact congrArg (fun m : 𝓜(ℂ, A) => m.fst (star a)) ha

lemma multiplierInclusion_rightIdeal :
    RightIdealRange (DoubleCentralizer.coeHom (𝕜 := ℂ) (A := A)) := by
  intro a m
  refine ⟨m.snd a, ?_⟩
  apply DoubleCentralizer.ext
  apply Prod.ext <;> apply ContinuousLinearMap.ext
  · intro b
    exact m.central a b
  · intro b
    change b * m.snd a = m.snd (b * a)
    -- Right module linearity follows from the defining centralizer identity.
    apply sub_eq_zero.mp
    apply (CStarRing.mul_star_self_eq_zero_iff
      (b * m.snd a - m.snd (b * a))).mp
    have hz (c : A) : (b * m.snd a - m.snd (b * a)) * c = 0 := by
      rw [sub_mul, mul_assoc, m.central, m.central, mul_assoc, sub_self]
    exact hz _

end Multiplier

section TensorIdeal

variable {A B : Type u} {D : Type v} [NonUnitalCStarAlgebra A]
  [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra D]

lemma minimalMapLeft_isometry_any (ι : A →⋆ₙₐ[ℂ] B) (hι : Function.Injective ι) :
    Isometry (minimalMapLeft (C := D) ι) := by
  have he : minimalMapLeft (C := D) ι =
      minimalMapAny ι (NonUnitalStarAlgHom.id ℂ D) := by
    apply minimalTensor_hom_ext
    intro a d
    simp only [minimalMapLeft_elementary, minimalMapAny_elementary,
      NonUnitalStarAlgHom.coe_id, id_eq]
  rw [he]
  exact minimalMapAny_isometry _ _ hι Function.injective_id

lemma RightIdealRange.tensor {ι : A →⋆ₙₐ[ℂ] B} (h : RightIdealRange ι) :
    RightIdealRange (minimalMapLeft (C := D) ι) := by
  let j := minimalMapLeft (C := D) ι
  have hclosed : IsClosed (j.range : Set (MinimalTensor B D)) :=
    nonUnitalStarHom_isClosed_range j
  intro x y
  change j x * y ∈ j.range
  apply minimalPolynomial_denseRange.induction_on (p := fun x => j x * y ∈ j.range) x
    (hclosed.preimage ((nonUnitalStarHom_continuous j).mul continuous_const))
  intro c
  apply minimalPolynomial_denseRange.induction_on
    (p := fun y => j (minimalPolynomial c) * y ∈ j.range) y
    (hclosed.preimage (continuous_const.mul continuous_id))
  intro d
  dsimp only [minimalPolynomial, Finsupp.sum]
  rw [map_sum, Finset.sum_mul]
  apply j.range.sum_mem
  intro p hp
  rw [map_smul, Finset.mul_sum]
  apply j.range.sum_mem
  intro q hq
  rw [smul_mul_assoc, mul_smul_comm]
  apply j.range.smul_mem
  apply j.range.smul_mem
  rw [minimalMapLeft_elementary, ← minimalElementary_mul]
  obtain ⟨a, ha⟩ := ι.mem_range.mp (h p.1 q.1)
  exact ⟨minimalElementary a (p.2 * q.2), by
    change minimalElementary (ι a) (p.2 * q.2) = _
    rw [ha]⟩

end TensorIdeal

end WeakPureInfiniteness

end

end OAI
