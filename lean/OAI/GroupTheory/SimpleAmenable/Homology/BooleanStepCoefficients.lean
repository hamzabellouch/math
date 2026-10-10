import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.TorusStepFunctions
import OAI.GroupTheory.SimpleAmenable.Configurations.BooleanStages
import OAI.GroupTheory.SimpleAmenable.Configurations.StageOrder

namespace OAI

section

section
open CategoryTheory Classical Set
namespace SimpleAmenable.PolygonObject

namespace BooleanPartition
variable {a:ℕ}
lemma arrangement_color (P:BooleanPartition a) : HasSquareArrangement P.color := by
  choose S hS using fun b => polygon_hasSquareArrangement (P.polygon b)
  refine ⟨Finset.univ.biUnion S,fun p q hpq => ?_⟩
  have h := hS (P.color p) p q (fun l hl => hpq l (Finset.mem_biUnion.mpr ⟨_,Finset.mem_univ _,hl⟩))
  exact ((decide_eq_decide.mp h).mp rfl).symm
lemma arrangement_values (P:BooleanPartition a) {K:Type*} (v:Fin P.size→K) :
    HasSquareArrangement (fun p => v (P.color p)) := by
  obtain ⟨S,hS⟩ := P.arrangement_color
  exact ⟨S,fun p q h => congrArg v (hS p q h)⟩

lemma exists_arrangement_partition {ι K:Type} [Fintype ι] (f:ι→GenericSquare a→K)
    (hf:∀i,HasSquareArrangement (f i)) :
    ∃P:BooleanPartition a,∀i p q,P.color p=P.color q → f i p=f i q := by
  choose S hS using hf
  let T := Finset.univ.biUnion S
  let C : T → polygonAlgebra a := fun l => ⟨_,halfPlane_mem a l.val.1 l.val.2⟩
  refine ⟨generated C,fun i p q hpq => hS i p q (fun l hl => ?_)⟩
  have h := generated_constant C hpq (⟨l,Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hl⟩⟩:T)
  exact decide_eq_decide.mpr h
end BooleanPartition
variable (a:ℕ) (K:Type) [AddCommGroup K] [Module ℤ K]
noncomputable def booleanStepSubmodule : Submodule ℤ (GenericSquare a→K) where
  carrier := {f | HasSquareArrangement f}
  zero_mem' := ⟨∅,fun _ _ _ => rfl⟩
  add_mem' := by
    rintro f g ⟨S,hS⟩ ⟨T,hT⟩
    exact ⟨S∪T,fun p q h => congrArg₂ (·+·)
      (hS p q (fun l hl => h l (Finset.mem_union_left T hl)))
      (hT p q (fun l hl => h l (Finset.mem_union_right S hl)))⟩
  smul_mem' := by
    rintro r f ⟨S,hS⟩
    exact ⟨S,fun p q h => congrArg (r • ·) (hS p q h)⟩
noncomputable abbrev BooleanStep := ↥(booleanStepSubmodule a K)
namespace BooleanStep
variable {a K}
noncomputable def inflate (P:BooleanPartition a) : (Fin P.size→K) →ₗ[ℤ] BooleanStep a K where
  toFun v := ⟨fun p => v (P.color p),P.arrangement_values v⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
noncomputable def evaluate (P:BooleanPartition a) : BooleanStep a K →ₗ[ℤ] (Fin P.size→K) where
  toFun f b := f.val (P.point b)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
omit [Module ℤ K] in
@[simp] lemma inflate_apply (P:BooleanPartition a) (v:Fin P.size→K) (p:GenericSquare a) :
    (inflate (K:=K) P v).val p=v (P.color p) := rfl
omit [Module ℤ K] in
@[simp] lemma evaluate_apply (P:BooleanPartition a) (v:BooleanStep a K) (b:Fin P.size) :
    evaluate (K:=K) P v b=v.val (P.point b) := rfl
omit [Module ℤ K] in
lemma evaluate_inflate (P:BooleanPartition a) : (evaluate (K:=K) P).comp (inflate (K:=K) P)=LinearMap.id := by
  apply LinearMap.ext; intro v; funext i
  simp only [LinearMap.comp_apply,evaluate_apply,inflate_apply,BooleanPartition.color_point,LinearMap.id_apply]
omit [Module ℤ K] in
lemma inflate_injective (P:BooleanPartition a) : Function.Injective (inflate (K:=K) P) := by
  intro x y h
  have hh := congrArg (evaluate (K:=K) P) h
  change ((evaluate (K:=K) P).comp (inflate (K:=K) P)) x=((evaluate (K:=K) P).comp (inflate (K:=K) P)) y at hh
  simpa only [evaluate_inflate,LinearMap.id_apply] using hh
noncomputable def refinement {P Q:BooleanPartition a} (_h:P.Refines Q) :
    (Fin P.size→K) →ₗ[ℤ] (Fin Q.size→K) := (evaluate (K:=K) Q).comp (inflate (K:=K) P)
omit [Module ℤ K] in
lemma inflate_refinement {P Q:BooleanPartition a} (h:P.Refines Q) :
    (inflate (K:=K) Q).comp (refinement h)=inflate (K:=K) P := by
  apply LinearMap.ext; intro v; apply Subtype.ext; funext p
  change v (P.color (Q.point (Q.color p)))=v (P.color p)
  exact congrArg v (h _ _ (Q.color_point (Q.color p)))
omit [Module ℤ K] in
lemma exists_common {ι:Type} [Fintype ι] (f:ι→BooleanStep a K) :
    ∃P:BooleanPartition a,∀i,inflate (K:=K) P (evaluate (K:=K) P (f i))=f i := by
  obtain ⟨P,hP⟩ := BooleanPartition.exists_arrangement_partition (fun i => (f i).val) (fun i => (f i).property)
  refine ⟨P,fun i => ?_⟩
  apply Subtype.ext; funext p
  exact hP i _ _ (P.color_point (P.color p))
end BooleanStep
end SimpleAmenable.PolygonObject

end

section
open CategoryTheory Classical Set TensorProduct
namespace SimpleAmenable.PolygonObject.BooleanStep

variable {a:ℕ} {K:Type} [AddCommGroup K]
noncomputable def multiply : BooleanStep a ℤ →ₗ[ℤ] K →ₗ[ℤ] BooleanStep a K where
  toFun f := {
    toFun k := ⟨fun p => f.val p • k,by
      obtain ⟨S,hS⟩ := f.property
      exact ⟨S,fun p q h => congrArg (· • k) (hS p q h)⟩⟩
    map_add' x y := by apply Subtype.ext; funext p; change f.val p • (x+y)=f.val p • x+f.val p • y; exact smul_add _ _ _
    map_smul' r k := by apply Subtype.ext; funext p; change f.val p • (r • k)=r • (f.val p • k); exact smul_comm _ _ _ }
  map_add' f g := by ext k p; exact add_smul _ _ _
  map_smul' r f := by
    apply LinearMap.ext; intro k; apply Subtype.ext; funext p
    change (r • f.val p) • k = r • (f.val p • k)
    exact smul_assoc r (f.val p) k
noncomputable def tensorMap : BooleanStep a ℤ ⊗[ℤ] K →ₗ[ℤ] BooleanStep a K :=
  TensorProduct.lift multiply
@[simp] lemma tensorMap_tmul (f:BooleanStep a ℤ) (k:K) (p:GenericSquare a) :
    (tensorMap (a:=a) (K:=K) (f ⊗ₜ[ℤ] k)).val p=f.val p • k := rfl
noncomputable def finiteTensorEquiv (P:BooleanPartition a) :
    (Fin P.size→ℤ) ⊗[ℤ] K ≃ₗ[ℤ] (Fin P.size→K) :=
  TensorProduct.comm ℤ _ _ ≪≫ₗ TensorProduct.piScalarRight ℤ ℤ K (Fin P.size)
@[simp] lemma finiteTensorEquiv_tmul (P:BooleanPartition a) (v:Fin P.size→ℤ) (k:K) :
    finiteTensorEquiv (K:=K) P (v ⊗ₜ[ℤ] k)=fun i => v i • k := by
  change TensorProduct.piScalarRightHom ℤ ℤ K (Fin P.size) (k ⊗ₜ[ℤ] v)=_
  exact TensorProduct.piScalarRightHom_tmul ℤ ℤ K (Fin P.size) k v
noncomputable def tensorInflate (P:BooleanPartition a) :
    (Fin P.size→ℤ) ⊗[ℤ] K →ₗ[ℤ] BooleanStep a ℤ ⊗[ℤ] K :=
  TensorProduct.map (inflate (K:=ℤ) P) LinearMap.id
lemma tensorMap_inflate (P:BooleanPartition a) :
    (tensorMap (a:=a) (K:=K)).comp (tensorInflate P) =
      (inflate (K:=K) P).comp (finiteTensorEquiv (K:=K) P).toLinearMap := by
  apply TensorProduct.ext'; intro v k; apply Subtype.ext; funext p
  change v (P.color p) • k=finiteTensorEquiv (K:=K) P (v ⊗ₜ[ℤ] k) (P.color p)
  rw [finiteTensorEquiv_tmul]
lemma tensorInflate_refinement {P Q:BooleanPartition a} (h:P.Refines Q) :
    (tensorInflate (K:=K) Q).comp (TensorProduct.map (refinement (K:=ℤ) h) LinearMap.id)=
      tensorInflate P := by
  apply TensorProduct.ext'; intro v k
  exact congrArg (fun f => f ⊗ₜ[ℤ] k) (LinearMap.congr_fun (inflate_refinement (K:=ℤ) h) v)
lemma exists_tensor_stage (x:BooleanStep a ℤ ⊗[ℤ] K) :
    ∃P:BooleanPartition a,∃v:(Fin P.size→ℤ) ⊗[ℤ] K,tensorInflate P v=x := by
  induction x using TensorProduct.inductionOn with
  | tmul f k =>
    obtain ⟨P,hP⟩ := exists_common (fun _:Fin 1 => f)
    refine ⟨P,evaluate (K:=ℤ) P f ⊗ₜ[ℤ] k,?_⟩
    change inflate (K:=ℤ) P (evaluate (K:=ℤ) P f) ⊗ₜ[ℤ] k = f ⊗ₜ[ℤ] k
    rw [hP 0]
  | add x y hx hy =>
    obtain ⟨P,v,rfl⟩ := hx
    obtain ⟨Q,w,rfl⟩ := hy
    let T := P.join Q
    let hP : P.Refines T := P.le_join_left Q
    let hQ : Q.Refines T := P.le_join_right Q
    refine ⟨T,TensorProduct.map (refinement hP) LinearMap.id v+
      TensorProduct.map (refinement hQ) LinearMap.id w,?_⟩
    rw [map_add]
    exact congrArg₂ (·+·) (LinearMap.congr_fun (tensorInflate_refinement (K:=K) hP) v)
      (LinearMap.congr_fun (tensorInflate_refinement (K:=K) hQ) w)
lemma tensorMap_injective : Function.Injective (tensorMap (a:=a) (K:=K)) := by
  apply (tensorMap (a:=a) (K:=K)).ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨P,v,rfl⟩ := exists_tensor_stage x
  have hv : inflate (K:=K) P (finiteTensorEquiv (K:=K) P v)=0 := by
    change ((inflate (K:=K) P).comp (finiteTensorEquiv (K:=K) P).toLinearMap) v=0
    rw [←tensorMap_inflate]
    exact hx
  have hv0 : finiteTensorEquiv (K:=K) P v=0 := inflate_injective P (hv.trans (map_zero _).symm)
  have h := (finiteTensorEquiv (K:=K) P).injective (hv0.trans (map_zero _).symm)
  rw [h,map_zero]
lemma tensorMap_surjective : Function.Surjective (tensorMap (a:=a) (K:=K)) := by
  intro f
  obtain ⟨P,hP⟩ := exists_common (fun _:Fin 1 => f)
  refine ⟨tensorInflate P ((finiteTensorEquiv (K:=K) P).symm (evaluate (K:=K) P f)),?_⟩
  change ((tensorMap (a:=a) (K:=K)).comp (tensorInflate P)) _ = _
  rw [tensorMap_inflate,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]
  exact hP 0

noncomputable def tensorEquiv : SquareStep a ⊗[ℤ] K ≃ₗ[ℤ] BooleanStep a K :=
  LinearEquiv.ofBijective tensorMap ⟨tensorMap_injective,tensorMap_surjective⟩
end SimpleAmenable.PolygonObject.BooleanStep

end

end

end OAI
