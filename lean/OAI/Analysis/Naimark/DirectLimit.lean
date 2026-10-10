import Mathlib

namespace OAI

noncomputable section

open UniformSpace Topology
namespace NaimarkZFC
section DirectLimit
universe u v
variable {I : Type u} [Preorder I] [IsDirectedOrder I] [Nonempty I]
  (A : I → Type v) [∀ i, CStarAlgebra (A i)]
  (f : ∀ i j, i ≤ j → A i →⋆ₐ[ℂ] A j)
  [DirectedSystem A (f · · ·)]

class IsometricStarSystem : Prop where
  isometry : ∀ i j h, Isometry (f i j h)

variable [IsometricStarSystem A f]

instance directLimitNorm : Norm (DirectLimit A f) where
  norm := Quotient.lift (fun x : Sigma A => ‖x.2‖) (by
    intro x y h
    obtain ⟨k,hx,hy,he⟩ := h
    have hf (i j) (h : i ≤ j) (a : A i) : ‖f i j h a‖ = ‖a‖ :=
      (IsometricStarSystem.isometry (A := A) (f := f) i j h).norm_map_of_map_zero
        (map_zero _) a
    rw [← hf x.1 k hx, ← hf y.1 k hy, he])

omit [Nonempty I] in
@[simp] theorem directLimit_norm_mk (i : I) (a : A i) :
    ‖(⟦⟨i,a⟩⟧ : DirectLimit A f)‖ = ‖a‖ := rfl

theorem directLimitNormCore : NormedSpace.Core ℂ (DirectLimit A f) where
  norm_nonneg := DirectLimit.induction f (fun i a => norm_nonneg a)
  norm_smul z := DirectLimit.induction f (fun i a => by
    rw [DirectLimit.smul_def,directLimit_norm_mk,directLimit_norm_mk,norm_smul])
  norm_triangle := DirectLimit.induction₂ f (fun i a b => by
    rw [DirectLimit.add_def,directLimit_norm_mk,directLimit_norm_mk,directLimit_norm_mk]
    exact norm_add_le a b)
  norm_eq_zero_iff := DirectLimit.induction f (fun i a => by
    rw [directLimit_norm_mk,norm_eq_zero]
    constructor
    · intro h
      rw [h,DirectLimit.zero_def i]
    · intro h
      have hh := Quotient.eq.mp h
      obtain ⟨k,ha,hb,he⟩ := hh
      have hz : f i k ha a = 0 := by simpa using he
      exact (IsometricStarSystem.isometry (A := A) (f := f) i k ha).injective
        (hz.trans (map_zero _).symm))

instance directLimitNormedAddCommGroup : NormedAddCommGroup (DirectLimit A f) :=
  NormedAddCommGroup.ofCore (directLimitNormCore A f)

instance directLimitNormedRing : NormedRing (DirectLimit A f) where
  __ : Ring (DirectLimit A f) := inferInstance
  __ : NormedAddCommGroup (DirectLimit A f) := directLimitNormedAddCommGroup A f
  norm_mul_le := DirectLimit.induction₂ f (fun i a b => by
    rw [DirectLimit.mul_def,directLimit_norm_mk,directLimit_norm_mk,directLimit_norm_mk]
    exact norm_mul_le a b)

instance directLimitNormedAlgebra : NormedAlgebra ℂ (DirectLimit A f) where
  norm_smul_le z := DirectLimit.induction f (fun i a => by
    rw [DirectLimit.smul_def,directLimit_norm_mk,directLimit_norm_mk]
    exact norm_smul_le z a)

instance directLimitNormedStarGroup : NormedStarGroup (DirectLimit A f) where
  norm_star_le := DirectLimit.induction f (fun i a => by
    rw [DirectLimit.star_def,directLimit_norm_mk,directLimit_norm_mk,norm_star])

instance directLimitCStarRing : CStarRing (DirectLimit A f) where
  norm_mul_self_le := DirectLimit.induction f (fun i a => by
    rw [DirectLimit.star_def,DirectLimit.mul_def,directLimit_norm_mk,directLimit_norm_mk]
    exact CStarRing.norm_mul_self_le a)

def directLimitInclude (i : I) : A i →⋆ₐ[ℂ] DirectLimit A f where
  toFun a := ⟦⟨i,a⟩⟧
  map_zero' := (DirectLimit.zero_def i).symm
  map_one' := (DirectLimit.one_def i).symm
  map_add' a b := (DirectLimit.add_def i a b).symm
  map_mul' a b := (DirectLimit.mul_def i a b).symm
  map_star' a := (DirectLimit.star_def i a).symm
  commutes' z := (DirectLimit.algebraMap_def i z).symm

theorem directLimitInclude_isometry (i : I) : Isometry (directLimitInclude A f i) := by
  apply AddMonoidHomClass.isometry_of_norm
  intro a
  exact directLimit_norm_mk A f i a

omit [IsometricStarSystem A f] in
@[simp] theorem directLimitInclude_compatible (i j : I) (h : i ≤ j) (a : A i) :
    directLimitInclude A f j (f i j h a) = directLimitInclude A f i a :=
  DirectLimit.mk_apply i j a h

end DirectLimit

namespace CStarCompletion
variable (A : Type*) [NormedRing A] [StarRing A] [NormedStarGroup A]

instance : Star (Completion A) where
  star := Completion.map (star : A → A)

@[simp] theorem star_coe (a : A) : star (a : Completion A) = (star a : A) :=
  Completion.map_coe star_isometry.uniformContinuous a

instance : ContinuousStar (Completion A) where
  continuous_star := Completion.continuous_map

instance : StarRing (Completion A) where
  star_involutive x := by
    induction x using Completion.induction_on
    · exact isClosed_eq (by fun_prop) continuous_id
    · rename_i a
      simp only [star_coe,star_star]
  star_mul x y := by
    induction x, y using Completion.induction_on₂
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · rename_i a b
      simp only [← Completion.coe_mul,star_coe,star_mul]
  star_add x y := by
    induction x, y using Completion.induction_on₂
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · rename_i a b
      simp only [← Completion.coe_add,star_coe,star_add]

instance : NormedStarGroup (Completion A) where
  norm_star_le x := by
    induction x using Completion.induction_on
    · exact isClosed_le (by fun_prop) (by fun_prop)
    · rename_i a
      simp only [star_coe,Completion.norm_coe,norm_star,le_refl]

instance [CStarRing A] : CStarRing (Completion A) where
  norm_mul_self_le x := by
    induction x using Completion.induction_on
    · exact isClosed_le (by fun_prop) (by fun_prop)
    · rename_i a
      rw [star_coe,← Completion.coe_mul,Completion.norm_coe,Completion.norm_coe]
      exact CStarRing.norm_mul_self_le a

instance [NormedAlgebra ℂ A] [StarModule ℂ A] : StarModule ℂ (Completion A) where
  star_smul z x := by
    induction x using Completion.induction_on
    · exact isClosed_eq (continuous_star.comp (continuous_const_smul z))
        ((continuous_const_smul (star z)).comp continuous_star)
    · rename_i a
      simp only [← Completion.coe_smul,star_coe,star_smul]

instance [NormedAlgebra ℂ A] : NormedAlgebra ℂ (Completion A) where
  norm_smul_le := norm_smul_le

instance [CStarRing A] [NormedAlgebra ℂ A] [StarModule ℂ A] :
    CStarAlgebra (Completion A) where
  __ : NormedAlgebra ℂ (Completion A) := inferInstance
  __ : StarModule ℂ (Completion A) := inferInstance

def toCompletion [NormedAlgebra ℂ A] [StarModule ℂ A] : A →⋆ₐ[ℂ] Completion A where
  toFun := (↑)
  map_zero' := Completion.coe_zero
  map_one' := Completion.coe_one A
  map_add' := Completion.coe_add
  map_mul' := Completion.coe_mul
  map_star' a := (star_coe A a).symm
  commutes' z := by simp only [Algebra.algebraMap_eq_smul_one,Completion.coe_smul,Completion.coe_one]

theorem include_isometry [NormedAlgebra ℂ A] [StarModule ℂ A] : Isometry (toCompletion A) :=
  Completion.coe_isometry

theorem include_dense [NormedAlgebra ℂ A] [StarModule ℂ A] : DenseRange (toCompletion A) :=
  Completion.denseRange_coe

end CStarCompletion

section Completion
universe u v w
variable {I : Type u} [Preorder I] [IsDirectedOrder I] [Nonempty I]
  (A : I → Type v) [∀ i, CStarAlgebra (A i)]
  (f : ∀ i j, i ≤ j → A i →⋆ₐ[ℂ] A j)
  [DirectedSystem A (f · · ·)] [IsometricStarSystem A f]

abbrev CStarDirectLimit := Completion (DirectLimit A f)

def cstarDirectLimitInclude (i : I) : A i →⋆ₐ[ℂ] CStarDirectLimit A f :=
  (CStarCompletion.toCompletion (DirectLimit A f)).comp (directLimitInclude A f i)

theorem cstarDirectLimitInclude_isometry (i : I) :
    Isometry (cstarDirectLimitInclude A f i) :=
  (CStarCompletion.include_isometry _).comp (directLimitInclude_isometry A f i)

@[simp] theorem cstarDirectLimitInclude_compatible (i j : I) (h : i ≤ j) (a : A i) :
    cstarDirectLimitInclude A f j (f i j h a) = cstarDirectLimitInclude A f i a := by
  change (directLimitInclude A f j (f i j h a) : Completion (DirectLimit A f)) = _
  rw [directLimitInclude_compatible]
  rfl

theorem cstarDirectLimitInclude_dense :
    Dense (⋃ i, Set.range (cstarDirectLimitInclude A f i)) := by
  apply (CStarCompletion.include_dense (DirectLimit A f)).mono
  rintro x ⟨a,rfl⟩
  induction a using DirectLimit.induction f with
  | ih i a => exact Set.mem_iUnion.mpr ⟨i,a,rfl⟩

theorem cstarDirectLimit_induction {P : CStarDirectLimit A f → Prop}
    (hP : IsClosed {x | P x})
    (hs : ∀ i a, P (cstarDirectLimitInclude A f i a)) (x) : P x := by
  have h := cstarDirectLimitInclude_dense A f x
  exact (closure_minimal (by
    intro y hy
    obtain ⟨i,a,rfl⟩ := Set.mem_iUnion.mp hy
    exact hs i a) hP) h

theorem cstarDirectLimit_nontrivial (i : I) [Nontrivial (A i)] :
    Nontrivial (CStarDirectLimit A f) :=
  (cstarDirectLimitInclude_isometry A f i).injective.nontrivial

variable {B : Type w} [CStarAlgebra B]
  (g : ∀ i, A i →⋆ₐ[ℂ] B)
  (hg : ∀ i j h a, g j (f i j h a) = g i a)

local instance directLimitLiftTopology : TopologicalSpace (DirectLimit A f) :=
  (inferInstance : UniformSpace (DirectLimit A f)).toTopologicalSpace

def directLimitLift : DirectLimit A f →⋆ₐ[ℂ] B where
  __ := DirectLimit.Algebra.lift A f B (fun i => (g i).toAlgHom) hg
  map_star' x := by
    induction x using DirectLimit.induction f with
    | ih i a => exact map_star (g i) a

omit [IsometricStarSystem A f] in
@[simp] theorem directLimitLift_stage (i : I) (a : A i) :
    directLimitLift A f g hg (directLimitInclude A f i a) = g i a := rfl

def directLimitLiftCLM : DirectLimit A f →L[ℂ] B :=
  (directLimitLift A f g hg).toAlgHom.toLinearMap.mkContinuous 1 (by
    intro x
    induction x using DirectLimit.induction f with
    | ih i a =>
      change ‖g i a‖ ≤ 1 * ‖a‖
      simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le (g i) a)

def cstarDirectLimitLift : CStarDirectLimit A f →⋆ₐ[ℂ] B where
  __ := (directLimitLiftCLM A f g hg).fromCompletion.toLinearMap
  toFun := (directLimitLiftCLM A f g hg).fromCompletion
  map_zero' := (directLimitLiftCLM A f g hg).fromCompletion.map_zero
  map_one' := by
    rw [← Completion.coe_one (DirectLimit A f),ContinuousLinearMap.fromCompletion_apply_coe]
    exact map_one (directLimitLift A f g hg)
  map_mul' x y := by
    induction x, y using Completion.induction_on₂
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · rename_i x y
      rw [← Completion.coe_mul]
      simp only [ContinuousLinearMap.fromCompletion_apply_coe]
      exact map_mul (directLimitLift A f g hg) x y
  map_star' x := by
    induction x using Completion.induction_on
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · rename_i x
      rw [CStarCompletion.star_coe]
      simp only [ContinuousLinearMap.fromCompletion_apply_coe]
      exact map_star (directLimitLift A f g hg) x
  commutes' z := by
    rw [Algebra.algebraMap_eq_smul_one,map_smul]
    have h1 : (directLimitLiftCLM A f g hg).fromCompletion 1 = 1 := by
      rw [← Completion.coe_one (DirectLimit A f),ContinuousLinearMap.fromCompletion_apply_coe]
      exact map_one (directLimitLift A f g hg)
    rw [h1,Algebra.algebraMap_eq_smul_one]

@[simp] theorem cstarDirectLimitLift_stage (i : I) (a : A i) :
    cstarDirectLimitLift A f g hg (cstarDirectLimitInclude A f i a) = g i a :=
  (ContinuousLinearMap.fromCompletion_apply_coe _ _).trans rfl

theorem cstarDirectLimitLift_isometry (hi : ∀ i, Isometry (g i)) :
    Isometry (cstarDirectLimitLift A f g hg) := by
  apply AddMonoidHomClass.isometry_of_norm
  intro x
  apply cstarDirectLimit_induction A f (P := fun x =>
    ‖cstarDirectLimitLift A f g hg x‖ = ‖x‖)
  · exact isClosed_eq (continuous_norm.comp
      (directLimitLiftCLM A f g hg).fromCompletion.continuous) continuous_norm
  · intro i a
    rw [cstarDirectLimitLift_stage]
    rw [(hi i).norm_map_of_map_zero (map_zero _) a,
      (cstarDirectLimitInclude_isometry A f i).norm_map_of_map_zero (map_zero _) a]

def cstarDirectLimitEquiv (hi : ∀ i, Isometry (g i))
    (hd : Dense (⋃ i, Set.range (g i))) : CStarDirectLimit A f ≃⋆ₐ[ℂ] B :=
  StarAlgEquiv.ofBijective (cstarDirectLimitLift A f g hg) ⟨
    (cstarDirectLimitLift_isometry A f g hg hi).injective, by
      intro b
      have hc : IsClosed (Set.range (cstarDirectLimitLift A f g hg)) :=
        (cstarDirectLimitLift_isometry A f g hg hi).isClosedEmbedding.isClosed_range
      apply closure_minimal (t := Set.range (cstarDirectLimitLift A f g hg)) ?_ hc (hd b)
      intro x hx
      obtain ⟨i,a,rfl⟩ := Set.mem_iUnion.mp hx
      exact ⟨cstarDirectLimitInclude A f i a,cstarDirectLimitLift_stage A f g hg i a⟩⟩

end Completion
end NaimarkZFC

end

end OAI
