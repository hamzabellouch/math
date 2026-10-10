import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.StageRealization
import OAI.GroupTheory.SimpleAmenable.Configurations.StageOrder
import OAI.GroupTheory.SimpleAmenable.Homology.BooleanStepCoefficients

namespace OAI

section

section
open CategoryTheory Classical Set
namespace SimpleAmenable.PolygonObject.LabelledStage

variable {a n:ℕ} {K:Type} [AddCommGroup K]
noncomputable abbrev Coefficients (a n:ℕ) (K:Type) [AddCommGroup K] :=
  ReducedLabel n →₀ BooleanStep a K
namespace Stage
variable (S:Stage a n)
noncomputable def label (j:Fin S.support.card) : ReducedLabel n := ⟨S.L j,S.L_reduced j⟩
lemma label_injective : Function.Injective S.label := fun _ _ equality => S.L_injective (congrArg Subtype.val equality)
lemma label_mem_support (j:Fin S.support.card) : S.label j∈S.support :=
  (S.label_mem _ _).mp ⟨j,rfl⟩
lemma label_range (l:ReducedLabel n) : (∃j,S.label j=l) ↔ l∈S.support := by
  simpa only [label,Subtype.ext_iff] using S.label_mem l.val l.property
noncomputable def realize : (Fin S.partition.size × Fin S.support.card → K) →ₗ[ℤ] Coefficients a n K :=
  ∑j:Fin S.support.card,
    (Finsupp.lsingle (S.label j)).comp
      ((BooleanStep.inflate (K:=K) S.partition).comp (LinearMap.funLeft ℤ K (fun i => (i,j))))
lemma realize_at_label (v:Fin S.partition.size × Fin S.support.card → K) (j:Fin S.support.card) :
    (S.realize (K:=K) v) (S.label j) = BooleanStep.inflate (K:=K) S.partition (fun i => v (i,j)) := by
  simp only [realize,LinearMap.sum_apply,LinearMap.comp_apply,Finsupp.lsingle_apply,Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single j]
  · rw [Finsupp.single_eq_same]; rfl
  · intro k hk hkj
    exact Finsupp.single_eq_of_ne (fun e => hkj (S.label_injective e.symm))
  · intro h; exact False.elim (h (Finset.mem_univ _))
lemma realize_outside (v:Fin S.partition.size × Fin S.support.card → K) (l:ReducedLabel n)
    (hl:l∉S.support) : (S.realize (K:=K) v) l=0 := by
  simp only [realize,LinearMap.sum_apply,LinearMap.comp_apply,Finsupp.lsingle_apply,Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero; intro j hj
  exact Finsupp.single_eq_of_ne (fun e => hl (e.symm ▸ S.label_mem_support j))
noncomputable def coefficientEvaluate : Coefficients a n K →ₗ[ℤ] (Fin S.partition.size × Fin S.support.card → K) where
  toFun f c := (f (S.label c.2)).val (S.partition.point c.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
lemma coefficientEvaluate_realize :
    (S.coefficientEvaluate (K:=K)).comp S.realize=LinearMap.id := by
  apply LinearMap.ext; intro v; funext c
  change (S.realize (K:=K) v (S.label c.2)).val (S.partition.point c.1)=v c
  rw [realize_at_label,BooleanStep.inflate_apply,S.partition.color_point]
lemma realize_injective : Function.Injective (S.realize (K:=K)) := by
  intro v w h
  have hh := congrArg (S.coefficientEvaluate (K:=K)) h
  change ((S.coefficientEvaluate (K:=K)).comp S.realize) v=((S.coefficientEvaluate (K:=K)).comp S.realize) w at hh
  simpa only [coefficientEvaluate_realize,LinearMap.id_apply] using hh

def Admissible (f:Coefficients a n K) : Prop :=
  f.support ⊆ S.support ∧ ∀l p q,S.partition.color p=S.partition.color q → (f l).val p=(f l).val q
lemma realize_admissible (v:Fin S.partition.size × Fin S.support.card → K) : S.Admissible (S.realize (K:=K) v) := by
  constructor
  · intro l hl
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hl) (S.realize_outside v l hn)
  · intro l p q hpq
    by_cases hl:l∈S.support
    · obtain ⟨j,rfl⟩ := (S.label_range l).mpr hl
      rw [S.realize_at_label,BooleanStep.inflate_apply,BooleanStep.inflate_apply,hpq]
    · rw [S.realize_outside v l hl]; rfl
lemma realize_coefficientEvaluate (f:Coefficients a n K) (hf:S.Admissible f) :
    S.realize (K:=K) (S.coefficientEvaluate (K:=K) f)=f := by
  apply Finsupp.ext; intro l
  by_cases hl:l∈S.support
  · obtain ⟨j,rfl⟩ := (S.label_range l).mpr hl
    rw [realize_at_label]
    apply Subtype.ext; funext p
    exact hf.2 _ _ _ (S.partition.color_point (S.partition.color p))
  · rw [realize_outside _ _ _ hl]
    exact (Finsupp.notMem_support_iff.mp (fun h => hl (hf.1 h))).symm
lemma admissible_mono {T:Stage a n} (h:S≤T) {f:Coefficients a n K} (hf:S.Admissible f) :
    T.Admissible f := ⟨hf.1.trans h.2,fun l p q hpq => hf.2 l p q (h.1 p q hpq)⟩
variable {S}
noncomputable def coefficientRefinement {T:Stage a n} (_h:S≤T) :
    (Fin S.partition.size × Fin S.support.card →K) →ₗ[ℤ] (Fin T.partition.size × Fin T.support.card →K) :=
  (T.coefficientEvaluate (K:=K)).comp S.realize
lemma realize_refinement {T:Stage a n} (h:S≤T) :
    (T.realize (K:=K)).comp (coefficientRefinement h)=S.realize (K:=K) := by
  apply LinearMap.ext; intro v
  exact T.realize_coefficientEvaluate _ (S.admissible_mono h (S.realize_admissible v))
lemma exists_coefficient_stage (f:Coefficients a n K) : ∃S:Stage a n,S.Admissible f := by
  obtain ⟨P,hP⟩ := BooleanStep.exists_common (fun l:f.support => f l.val)
  refine ⟨⟨P,f.support⟩,Subset.rfl,?_⟩
  intro l p q hpq
  by_cases hl:l∈f.support
  · have h := congrArg Subtype.val (hP ⟨l,hl⟩)
    exact (congrFun h p).symm.trans ((congrArg (fun i => (BooleanStep.evaluate (K:=K) P (f l)) i) hpq).trans (congrFun h q))
  · rw [Finsupp.notMem_support_iff.mp hl]; rfl
end Stage
end SimpleAmenable.PolygonObject.LabelledStage

end

section
open CategoryTheory Limits Classical Set
namespace SimpleAmenable.PolygonObject.LabelledStage.Stage

variable {a n:ℕ} (K:Type) [AddCommGroup K]
noncomputable def coefficientDiagram : Stage a n ⥤ ModuleCat ℤ where
  obj S := ModuleCat.of ℤ (Fin S.partition.size × Fin S.support.card→K)
  map h := ModuleCat.ofHom (coefficientRefinement (K:=K) (leOfHom h))
  map_id S := by
    apply ModuleCat.hom_ext
    exact coefficientEvaluate_realize S
  map_comp {S T U} h k := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext; intro v
    change U.coefficientEvaluate (K:=K) (S.realize (K:=K) v) =
      U.coefficientEvaluate (K:=K) (T.realize (K:=K) (coefficientRefinement (K:=K) (leOfHom h) v))
    exact congrArg (U.coefficientEvaluate (K:=K)) (LinearMap.congr_fun (realize_refinement (K:=K) (leOfHom h)) v).symm
noncomputable def coefficientCocone : Cocone (coefficientDiagram (a:=a) (n:=n) K) where
  pt := ModuleCat.of ℤ (Coefficients a n K)
  ι := {
    app S := ModuleCat.ofHom (S.realize (K:=K))
    naturality _ _ h := ModuleCat.hom_ext (realize_refinement (K:=K) (leOfHom h)) }

noncomputable def coefficientIsColimit : IsColimit (coefficientCocone (a:=a) (n:=n) K) := by
  apply isColimitOfReflects (CategoryTheory.forget (ModuleCat ℤ))
  apply Types.FilteredColimit.isColimitOf'
  · intro f
    obtain ⟨S,hS⟩ := exists_coefficient_stage f
    exact ⟨S,S.coefficientEvaluate (K:=K) f,(S.realize_coefficientEvaluate f hS).symm⟩
  · intro S v w h
    have hvw := S.realize_injective h
    exact ⟨S,𝟙 S,congrArg _ hvw⟩
end SimpleAmenable.PolygonObject.LabelledStage.Stage

end

end

end OAI
