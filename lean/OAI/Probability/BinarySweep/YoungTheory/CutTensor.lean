import Mathlib
import OAI.Probability.BinarySweep.YoungTheory.CutColumns

namespace OAI

noncomputable section

section

open scoped BigOperators Classical TensorProduct

namespace BinaryCoordinateSweeps.Young
lemma tensor_map_injective_complex {V W X Y : Type*}
    [AddCommMonoid V] [Module ℂ V] [AddCommMonoid W] [Module ℂ W]
    [AddCommMonoid X] [Module ℂ X] [AddCommMonoid Y] [Module ℂ Y]
    (f : V →ₗ[ℂ] X) (g : W →ₗ[ℂ] Y)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (TensorProduct.map f g) := by
  let : AddCommGroup X := Module.addCommMonoidToAddCommGroup ℂ
  let : AddCommGroup W := Module.addCommMonoidToAddCommGroup ℂ
  exact TensorProduct.map_injective_of_flat_flat f g hf hg

variable (μ : YoungDiagram) (p : ℕ)

abbrev CutTensor := SpechtSpace (hookPart μ p) ⊗[ℂ] SpechtSpace (southeast μ p)
abbrev CutTabloids := Tabloid (hookPart μ p) × Tabloid (southeast μ p)

def cutTensorInclude : CutTensor μ p →ₗ[ℂ] (CutTabloids μ p → ℂ) :=
  TensorProduct.lift {
    toFun := fun v => {
      toFun := fun w t => spechtInclude (hookPart μ p) v t.1 * spechtInclude (southeast μ p) w t.2
      map_add' := by intro a b; ext t; simp only [map_add,Pi.add_apply,mul_add]
      map_smul' := by intro c a; ext t; simp only [map_smul,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]; ring }
    map_add' := by intro a b; ext w t; simp only [map_add,Pi.add_apply,add_mul,LinearMap.add_apply,LinearMap.coe_mk,AddHom.coe_mk]
    map_smul' := by intro c a; ext w t; simp only [map_smul,Pi.smul_apply,smul_eq_mul,LinearMap.smul_apply,LinearMap.coe_mk,AddHom.coe_mk,RingHom.id_apply]; ring }

@[simp] lemma cutTensorInclude_tmul (v : SpechtSpace (hookPart μ p))
    (w : SpechtSpace (southeast μ p)) (t : CutTabloids μ p) :
    cutTensorInclude μ p (v ⊗ₜ[ℂ] w) t =
      spechtInclude (hookPart μ p) v t.1 * spechtInclude (southeast μ p) w t.2 := rfl

lemma cutTensorInclude_injective : Function.Injective (cutTensorInclude μ p) := by
  let T := TensorProduct.map (spechtInclude (hookPart μ p)) (spechtInclude (southeast μ p))
  have hT : Function.Injective T := tensor_map_injective_complex
    (spechtInclude (hookPart μ p)) (spechtInclude (southeast μ p))
    (spechtInclude_injective (hookPart μ p)) (spechtInclude_injective (southeast μ p))
  let E := TensorProduct.piScalarRight ℂ ℂ (Tabloid (hookPart μ p) → ℂ) (Tabloid (southeast μ p))
  have hE (u : CutTensor μ p) (t : CutTabloids μ p) :
      E (T u) t.2 t.1 = cutTensorInclude μ p u t := by
    induction u using TensorProduct.inductionOn with
    | tmul v w =>
      change E (spechtInclude _ v ⊗ₜ[ℂ] spechtInclude _ w) t.2 t.1 = _
      simp only [cutTensorInclude_tmul,E,TensorProduct.piScalarRight_apply,
        TensorProduct.piScalarRightHom_tmul,Pi.smul_apply,smul_eq_mul]
      exact mul_comm _ _
    | add u v hu hv => simp only [map_add,Pi.add_apply,hu,hv]
  intro u v h
  apply hT
  apply E.injective
  ext s t
  exact (hE u (t,s)).trans ((congrFun h (t,s)).trans (hE v (t,s)).symm)

def cutRestriction : SpechtSpace μ →ₗ[ℂ] (CutTabloids μ p → ℂ) where
  toFun v t := spechtInclude μ v (glueTabloid μ p t)
  map_add' a b := by ext t; simp
  map_smul' c a := by ext t; simp

lemma cutRestriction_poly :
    cutRestriction μ p (spechtPoly μ) =
      cutTensorInclude μ p (spechtPoly (hookPart μ p) ⊗ₜ[ℂ] spechtPoly (southeast μ p)) := by
  ext t
  change spechtInclude μ (spechtPoly μ) (glueTabloid μ p t) = _
  simp only [spechtInclude_poly,polytabloid_glue,cutTensorInclude_tmul]

lemma cutRestriction_translate (g : G (hookPart μ p) × G (southeast μ p)) :
    cutRestriction μ p (spechtRep μ (cutPerm μ p g) (spechtPoly μ)) =
      cutTensorInclude μ p
        (spechtRep (hookPart μ p) g.1 (spechtPoly (hookPart μ p)) ⊗ₜ[ℂ]
         spechtRep (southeast μ p) g.2 (spechtPoly (southeast μ p))) := by
  ext t
  change spechtInclude μ (spechtRep μ (cutPerm μ p g) (spechtPoly μ))
    (glueTabloid μ p t) = _
  rw [spechtInclude_rep,tabloidRepresentation_apply,← map_inv,← glueTabloid_smul,
    spechtInclude_poly,polytabloid_glue,cutTensorInclude_tmul,
    spechtInclude_rep,spechtInclude_rep]
  rfl

lemma cut_tensor_orbit_mem_range (g : G (hookPart μ p)) (d : G (southeast μ p)) :
    cutTensorInclude μ p (spechtRep (hookPart μ p) g (spechtPoly (hookPart μ p)) ⊗ₜ[ℂ]
      spechtRep (southeast μ p) d (spechtPoly (southeast μ p))) ∈
      LinearMap.range (cutRestriction μ p) :=
  ⟨spechtRep μ (cutPerm μ p (g,d)) (spechtPoly μ),cutRestriction_translate μ p (g,d)⟩

private lemma spechtPoly_span_top (ν : YoungDiagram) :
    Submodule.span ℂ (Set.range (fun g : G ν => spechtRep ν g (spechtPoly ν))) = ⊤ :=
  Irrep.span_orbit_eq_top (spechtRep ν) (spechtPoly ν) (spechtPoly_ne_zero ν)

lemma cut_tensor_tmul_mem_range (v : SpechtSpace (hookPart μ p))
    (w : SpechtSpace (southeast μ p)) :
    cutTensorInclude μ p (v ⊗ₜ[ℂ] w) ∈ LinearMap.range (cutRestriction μ p) := by
  have hv : v ∈ Submodule.span ℂ (Set.range (fun g : G (hookPart μ p) =>
      spechtRep (hookPart μ p) g (spechtPoly (hookPart μ p)))) := by
    rw [spechtPoly_span_top]
    trivial
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g,rfl⟩ := hx
    have hw : w ∈ Submodule.span ℂ (Set.range (fun d : G (southeast μ p) =>
        spechtRep (southeast μ p) d (spechtPoly (southeast μ p)))) := by
      rw [spechtPoly_span_top]
      trivial
    induction hw using Submodule.span_induction with
    | mem y hy => obtain ⟨d,rfl⟩ := hy; exact cut_tensor_orbit_mem_range μ p g d
    | zero => simp
    | add x y hx hy hx' hy' => simpa only [TensorProduct.tmul_add,map_add] using Submodule.add_mem _ hx' hy'
    | smul c x hx hx' => simpa only [TensorProduct.tmul_smul,map_smul] using Submodule.smul_mem _ c hx'
  | zero => simp
  | add x y hx hy hx' hy' => simpa only [TensorProduct.add_tmul,map_add] using Submodule.add_mem _ hx' hy'
  | smul c x hx hx' => simpa only [← TensorProduct.smul_tmul',map_smul] using Submodule.smul_mem _ c hx'

theorem cutTensor_range_le : LinearMap.range (cutTensorInclude μ p) ≤
    LinearMap.range (cutRestriction μ p) := by
  rintro _ ⟨u,rfl⟩
  induction u using TensorProduct.inductionOn with
  | tmul v w => exact cut_tensor_tmul_mem_range μ p v w
  | add u v hu hv => simpa only [map_add] using Submodule.add_mem _ hu hv

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep
open Representation

variable {G V W P : Type*} [Group G] [Fintype G]
  [AddCommMonoid V] [Module ℂ V] [AddCommMonoid W] [Module ℂ W]
  [AddCommMonoid P] [Module ℂ P]
  (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (τ : Representation ℂ G P)

def averageLinear (l : P →ₗ[ℂ] V) : P →ₗ[ℂ] V :=
  (Fintype.card G : ℂ)⁻¹ • ∑ g : G, (ρ g⁻¹).comp (l.comp (τ g))

lemma averageLinear_apply (l : P →ₗ[ℂ] V) (v : P) :
    averageLinear ρ τ l v = (Fintype.card G : ℂ)⁻¹ • ∑ g : G, ρ g⁻¹ (l (τ g v)) := by
  simp only [averageLinear,LinearMap.smul_apply,LinearMap.sum_apply,LinearMap.comp_apply]

lemma averageLinear_intertwines (l : P →ₗ[ℂ] V) (a : G) (v : P) :
    averageLinear ρ τ l (τ a v) = ρ a (averageLinear ρ τ l v) := by
  simp only [averageLinear_apply,map_smul,map_sum,← Module.End.mul_apply,← map_mul]
  congr 1
  have hh := Equiv.sum_comp (Equiv.mulRight a) (fun g : G =>
    ρ (a*g⁻¹) (l (τ g v)))
  rw [← hh]
  apply Finset.sum_congr rfl
  intro g _
  simp only [Equiv.coe_mulRight,mul_inv_rev,mul_inv_cancel_left]

def averagedIntertwiner (l : P →ₗ[ℂ] V) : IntertwiningMap τ ρ where
  toLinearMap := averageLinear ρ τ l
  isIntertwining' a := LinearMap.ext (averageLinear_intertwines ρ τ l a)

lemma averageLinear_lift (l : P →ₗ[ℂ] V) (f : IntertwiningMap ρ σ)
    (g : IntertwiningMap τ σ) (hl : ∀ v, f (l v) = g v) (v : P) :
    f (averageLinear ρ τ l v) = g v := by
  rw [averageLinear_apply,map_smul,map_sum]
  simp only [hl,IntertwiningMap.isIntertwining,
    ← Module.End.mul_apply,← map_mul,inv_mul_cancel,map_one,Module.End.one_apply]
  rw [Finset.sum_const,Finset.card_univ,← Nat.cast_smul_eq_nsmul ℂ,smul_smul,
    inv_mul_cancel₀ (show (Fintype.card G : ℂ) ≠ 0 from Nat.cast_ne_zero.mpr Fintype.card_ne_zero),one_smul]

theorem lift_intertwiner (f : IntertwiningMap ρ σ) (g : IntertwiningMap τ σ)
    (h : LinearMap.range g.toLinearMap ≤ LinearMap.range f.toLinearMap) :
    ∃ l : IntertwiningMap τ ρ, ∀ v, f (l v) = g v := by
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup ℂ
  let : AddCommGroup W := Module.addCommMonoidToAddCommGroup ℂ
  let : AddCommGroup P := Module.addCommMonoidToAddCommGroup ℂ
  let f0 := f.toLinearMap.rangeRestrict
  obtain ⟨r,hr⟩ := f0.exists_rightInverse_of_surjective f.toLinearMap.range_rangeRestrict
  let g0 : P →ₗ[ℂ] LinearMap.range f.toLinearMap :=
    g.toLinearMap.codRestrict _ (fun v => h ⟨v,rfl⟩)
  let l := r.comp g0
  have hl (v : P) : f (l v) = g v := by
    have hh := DFunLike.congr_fun hr (g0 v)
    exact congrArg Subtype.val hh
  exact ⟨averagedIntertwiner ρ τ l,averageLinear_lift ρ σ τ l f g hl⟩

end BinaryCoordinateSweeps.Irrep

end

end OAI
