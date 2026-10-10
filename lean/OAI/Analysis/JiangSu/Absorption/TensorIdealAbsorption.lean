import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Absorption.AbsorptionCriterion
import OAI.Analysis.JiangSu.TensorProducts.TensorIdeal

namespace OAI

noncomputable section


namespace NonunitalTensor
open NonunitalRelative
open scoped CStarAlgebra TensorProduct

variable {A D E : Type*} [NonUnitalCStarAlgebra A] [CStarAlgebra D] [CStarAlgebra E]
variable (γ : Unitization ℂ A →⋆ₐ[ℂ] E) (κ : D →⋆ₐ[ℂ] E)
variable (hc : ∀ a d,Commute (γ a) (κ d))

lemma original_left_mul (a : Unitization ℂ A) (b : A) :
    γ a*originalHom γ b=originalHom γ (a.fst•b+a.snd*b) := by
  change γ a*γ (Unitization.inr b)=γ (Unitization.inr (a.fst•b+a.snd*b))
  rw [←map_mul]
  congr 1
  apply Unitization.ext <;> simp

include hc in
lemma span_left_elementary (a : Unitization ℂ A) (d : D) {b : E}
    (hb : b∈coefficientSpan (originalHom γ) κ) :
    (γ a*κ d)*b∈coefficientSpan (originalHom γ) κ := by
  induction hb using Submodule.span_induction with
  | mem b hb =>
    obtain ⟨c,e,rfl⟩ := hb
    have he : (γ a*κ d)*(originalHom γ c*κ e)=originalHom γ (a.fst•c+a.snd*c)*κ (d*e) := by
      calc
        _=γ a*(κ d*originalHom γ c)*κ e := by simp only [mul_assoc]
        _=γ a*(originalHom γ c*κ d)*κ e := by rw [(original_commute γ κ hc c d).symm.eq]
        _=(γ a*originalHom γ c)*(κ d*κ e) := by simp only [mul_assoc]
        _=_ := by rw [original_left_mul,←map_mul]
    rw [he]
    exact coefficientSpan_mem _ _ _ _
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [mul_add] using (coefficientSpan (originalHom γ) κ).add_mem ihx ihy
  | smul c x hx ih => simpa only [mul_smul_comm] using (coefficientSpan (originalHom γ) κ).smul_mem c ih

local notation "B" => tensorIdeal (originalHom γ) κ (original_commute γ κ hc)

lemma ideal_left_elementary (a : Unitization ℂ A) (d : D) (b : B) : (γ a*κ d)*(b:E)∈B := by
  have hcl : IsClosed {x : E | (γ a*κ d)*x∈B} := (tensorIdeal_closed _ _ _).preimage (by fun_prop)
  have hs : (coefficientSpan (originalHom γ) κ : Set E)⊆{x : E | (γ a*κ d)*x∈B} := by
    intro x hx
    exact NonUnitalStarSubalgebra.le_topologicalClosure
      (coefficientAlgebra (originalHom γ) κ (original_commute γ κ hc))
      (span_left_elementary γ κ hc a d hx)
  exact closure_minimal hs hcl b.property

variable (f : (Unitization ℂ A) ⊗[ℂ] D →⋆ₐ[ℂ] E) (hd : DenseRange f)
variable (he : ∀ a d,f (a ⊗ₜ[ℂ] d)=γ a*κ d)

include hd he in
lemma ideal_left_absorb (e : E) (b : B) : e*(b:E)∈B := by
  refine hd.induction_on e ?_ ?_
  · exact (tensorIdeal_closed _ _ _).preimage (by fun_prop)
  · intro z
    induction z using TensorProduct.inductionOn with
    | tmul a d => rw [he]; exact ideal_left_elementary γ κ hc a d b
    | add z w hz hw => rw [map_add,add_mul]; exact add_mem hz hw

include hd he in
lemma ideal_right_absorb (b : B) (e : E) : (b:E)*e∈B := by
  have h : star ((star e)*(star b:E))∈B :=
    star_mem (ideal_left_absorb γ κ hc f hd he (star e) (star b))
  simpa only [star_mul,StarMemClass.coe_star,star_star] using h

end NonunitalTensor


namespace NonunitalTensor
open NonunitalRelative Pureness NonunitalGamma CStarAbsorption Filter
open scoped CStarAlgebra TensorProduct

universe u
variable {A E T : Type*} {D : Type u}
variable [NonUnitalCStarAlgebra A] [CStarAlgebra D] [CStarAlgebra E] [CStarAlgebra T]
variable (γ : Unitization ℂ A →⋆ₐ[ℂ] E) (κ : D →⋆ₐ[ℂ] E)
variable (hc : ∀ a d,Commute (γ a) (κ d))
local notation "B" => tensorIdeal (originalHom γ) κ (original_commute γ κ hc)

instance tensorIdeal_separable [TopologicalSpace.SeparableSpace A]
    [TopologicalSpace.SeparableSpace D] : TopologicalSpace.SeparableSpace B := by
  have hs : TopologicalSpace.IsSeparable (elementarySet (originalHom γ) κ) := by
    have he : elementarySet (originalHom γ) κ = Set.range (fun z : A×D => originalHom γ z.1*κ z.2) := by
      ext x
      constructor
      · rintro ⟨a,d,rfl⟩; exact ⟨(a,d),rfl⟩
      · rintro ⟨⟨a,d⟩,rfl⟩; exact ⟨a,d,rfl⟩
    rw [he]
    exact TopologicalSpace.isSeparable_range (by fun_prop)
  exact (hs.span (R := ℂ)).closure.separableSpace

def originalInclusion : A →⋆ₙₐ[ℂ] B :=
  NonUnitalStarAlgHom.codRestrict (originalHom γ) B (fun a => by
    apply NonUnitalStarSubalgebra.le_topologicalClosure
    change originalHom γ a∈coefficientSpan (originalHom γ) κ
    simpa using coefficientSpan_mem (originalHom γ) κ a 1)

lemma originalInclusion_isometry (hγ : Function.Injective γ) : Isometry (originalInclusion γ κ hc) := by
  apply NonUnitalStarAlgHom.isometry
  intro a b hab
  exact Unitization.inr_injective (hγ (congrArg Subtype.val hab))

variable [Nontrivial A] [Nontrivial D]
variable [PartialOrder A] [StarOrderedRing A]
variable [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace D]
variable (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ)≤atTop)]
variable (φ : D →⋆ₐ[ℂ] CentralSequenceAlgebra (A := A) U)
variable (hD : IsNuclear.{u,u} D) (hs : Pureness.TopologicallySimple D)
variable (t : D ⊗[ℂ] D →⋆ₐ[ℂ] T) (ht : Function.Injective t) (htd : DenseRange t)
variable (hh : ConnectedApproximateInnerHalfFlip t)

include U φ hD hs ht htd hh in

theorem equiv_of_embedding (hγ : Function.Injective γ)
    (f : (Unitization ℂ A) ⊗[ℂ] D →⋆ₐ[ℂ] E) (hd : DenseRange f)
    (he : ∀ a d,f (a ⊗ₜ[ℂ] d)=γ a*κ d) : Nonempty (A ≃⋆ₐ[ℂ] B) := by
  let ι := originalInclusion γ κ hc
  let k := NonUnitalStarSubalgebraClass.subtype B
  have hj : ∃ a : A,k (ι a)≠0 := by
    obtain ⟨a,ha⟩ := exists_ne (0 : A)
    refine ⟨a,?_⟩
    have hinj : Function.Injective (originalHom γ) := hγ.comp Unitization.inr_injective
    intro hz
    exact ha ((map_eq_zero_iff (originalHom γ) hinj).mp hz)
  let : TopologicalSpace.SeparableSpace B := tensorIdeal_separable γ κ hc
  apply NonunitalRelative.equiv_of_central_embedding U ι k κ
    (original_commute γ κ hc) hj φ hD hs t ht htd hh
    (fun b ε hε => tensorIdeal_coefficient_dense _ _ _ b hε)
    (originalInclusion_isometry γ κ hc hγ) (isometry_subtype_coe)
  · intro e b
    exact ⟨⟨e*(b:E),ideal_left_absorb γ κ hc f hd he e b⟩,rfl⟩
  · intro b e
    exact ⟨⟨(b:E)*e,ideal_right_absorb γ κ hc f hd he b e⟩,rfl⟩

end NonunitalTensor

end

end OAI
