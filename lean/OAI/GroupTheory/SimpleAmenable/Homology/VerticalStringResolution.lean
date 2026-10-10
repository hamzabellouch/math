import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.PolygonGroupoid

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section VerticalStringResolution
open CategoryTheory
universe sv su

namespace VerticalString
variable {C : Type su} [Groupoid.{sv} C]

def allowed (P : Subgroupoid C) (n : ℕ) (F : Fin (n+1) ⥤ C) : Prop :=
  ∀i j (f : i ⟶ j), F.map f∈P.arrows (F.obj i) (F.obj j)

abbrev Object (P : Subgroupoid C) (n : ℕ) := ObjectProperty.FullSubcategory (allowed P n)

noncomputable def evaluation (P : Subgroupoid C) (n : ℕ) : Object P n ⥤ C where
  obj F := F.obj.obj 0
  map f := f.hom.app 0
  map_id _ := rfl
  map_comp _ _ := rfl

noncomputable def constant (P : Subgroupoid C)
    (hP : ∀c, (𝟙 c)∈P.arrows c c) (n : ℕ) : C ⥤ Object P n where
  obj c := ⟨(Functor.const (Fin (n+1))).obj c,fun _ _ _ => hP c⟩
  map f := ⟨(Functor.const (Fin (n+1))).map f⟩
  map_id _ := rfl
  map_comp _ _ := rfl

noncomputable def comparison (P : Subgroupoid C)
    (hP : ∀c, (𝟙 c)∈P.arrows c c) (n : ℕ) :
    evaluation P n ⋙ constant P hP n ≅ 𝟭 (Object P n) := by
  refine NatIso.ofComponents (fun F => ?_) ?_
  ·
    refine ⟨⟨{ app := fun i => F.obj.map (homOfLE (Fin.zero_le i))
               naturality := ?_ }⟩,
      ⟨{ app := fun i => Groupoid.inv (F.obj.map (homOfLE (Fin.zero_le i)))
         naturality := ?_ }⟩,?_,?_⟩
    · intro i j f
      change (𝟙 (F.obj.obj 0)) ≫ F.obj.map (homOfLE (Fin.zero_le j)) =
        F.obj.map (homOfLE (Fin.zero_le i)) ≫ F.obj.map f
      rw [Category.id_comp,←F.obj.map_comp]
      congr 1
    · intro i j f
      change F.obj.map f ≫ Groupoid.inv (F.obj.map (homOfLE (Fin.zero_le j))) =
        Groupoid.inv (F.obj.map (homOfLE (Fin.zero_le i))) ≫ 𝟙 (F.obj.obj 0)
      rw [Category.comp_id]
      apply (cancel_mono (F.obj.map (homOfLE (Fin.zero_le j)))).mp
      simp only [Category.assoc,Groupoid.inv_comp,Category.comp_id]
      have he : F.obj.map (homOfLE (Fin.zero_le j))=
          F.obj.map (homOfLE (Fin.zero_le i)) ≫ F.obj.map f := by
        rw [←F.obj.map_comp]; congr 1
      rw [he,←Category.assoc,Groupoid.inv_comp,Category.id_comp]
    · apply (ObjectProperty.hom_ext _)
      ext i
      exact Groupoid.comp_inv _
    · apply (ObjectProperty.hom_ext _)
      ext i
      exact Groupoid.inv_comp _
  · intro F G f
    apply (ObjectProperty.hom_ext _)
    ext i
    change f.hom.app 0 ≫ G.obj.map (homOfLE (Fin.zero_le i)) =
      F.obj.map (homOfLE (Fin.zero_le i)) ≫ f.hom.app i
    exact (f.hom.naturality _).symm

noncomputable def evaluationEquivalence (P : Subgroupoid C)
    (hP : ∀c, (𝟙 c)∈P.arrows c c) (n : ℕ) : Object P n ≌ C where
  functor := evaluation P n
  inverse := constant P hP n
  unitIso := (comparison P hP n).symm
  counitIso := Iso.refl _
  functor_unitIso_comp F := by
    change Groupoid.inv (F.obj.map (homOfLE (Fin.zero_le 0))) ≫ 𝟙 _ = 𝟙 _
    have he : (homOfLE (Fin.zero_le (0 : Fin (n+1))))=𝟙 0 := Subsingleton.elim _ _
    rw [he,F.obj.map_id]
    simp

noncomputable def polygonEvaluationEquivalence (a n : ℕ) :
    Object (PolygonObject.positionalSubgroupoid a) n ≌ PolygonObject a :=
  evaluationEquivalence _ (PolygonObject.identity_positional) n

end VerticalString
end VerticalStringResolution

section IntegralTransgression
open Classical

namespace IntegralTransgression
variable {H E : Type*} [Group H] [Group E]

def Kernel (q : H →* E) (_hc : q.ker ≤ Subgroup.center H) : Type _ := q.ker

instance kernelCommGroup (q : H →* E) (hc : q.ker ≤ Subgroup.center H) :
    CommGroup (Kernel q hc) := by
  change CommGroup q.ker
  exact { (inferInstance : Group q.ker) with
    mul_comm := fun x y => Subtype.ext (Subgroup.mem_center_iff.mp (hc x.property) y.val).symm }

noncomputable def inclusion (q : H →* E) (hc : q.ker ≤ Subgroup.center H) : Kernel q hc →* H :=
  q.ker.subtype

variable (q : H →* E) (hq : Function.Surjective q) (hc : q.ker ≤ Subgroup.center H)

noncomputable def sectionMap (x : E) : H := if x=1 then 1 else Classical.choose (hq x)

@[simp] theorem section_one : sectionMap q hq 1 = 1 := by simp [sectionMap]
@[simp] theorem section_projection (x : E) : q (sectionMap q hq x)=x := by
  by_cases hx : x=1
  · simp [sectionMap,hx]
  · simpa [sectionMap,hx] using Classical.choose_spec (hq x)

noncomputable def factor (x y : E) : Kernel q hc :=
  ⟨sectionMap q hq x * sectionMap q hq y * (sectionMap q hq (x*y))⁻¹,by
    change q (sectionMap q hq x * sectionMap q hq y * (sectionMap q hq (x*y))⁻¹) = 1
    simp⟩

noncomputable def remainder (h : H) : Kernel q hc :=
  ⟨h * (sectionMap q hq (q h))⁻¹,by
    change q (h * (sectionMap q hq (q h))⁻¹) = 1
    simp⟩

@[simp] theorem factor_one_left (x : E) : factor q hq hc 1 x=1 := by
  apply Subtype.ext; simp only [factor,section_one,one_mul,mul_inv_cancel]; rfl
@[simp] theorem factor_one_right (x : E) : factor q hq hc x 1=1 := by
  apply Subtype.ext; simp only [factor,section_one,mul_one,mul_inv_cancel]; rfl
@[simp] theorem remainder_one : remainder q hq hc 1=1 := by
  apply Subtype.ext; simp only [remainder,map_one,section_one,inv_one,mul_one]; rfl
@[simp] theorem remainder_inclusion (k : Kernel q hc) :
    remainder q hq hc (inclusion q hc k)=k := by
  apply Subtype.ext
  change k.val * (sectionMap q hq (q k.val))⁻¹=k.val
  have hk : q k.val=1 := k.property
  simp [hk]

theorem factor_cocycle (x y z : E) :
    factor q hq hc x y * factor q hq hc (x*y) z =
    factor q hq hc y z * factor q hq hc x (y*z) := by
  apply Subtype.ext
  change (sectionMap q hq x * sectionMap q hq y * (sectionMap q hq (x*y))⁻¹) *
      (sectionMap q hq (x*y) * sectionMap q hq z * (sectionMap q hq (x*y*z))⁻¹) =
    (factor q hq hc y z).val *
      (sectionMap q hq x * sectionMap q hq (y*z) * (sectionMap q hq (x*(y*z)))⁻¹)
  have hcomm := Subgroup.mem_center_iff.mp (hc (factor q hq hc y z).property)
    (sectionMap q hq x)
  simp only [mul_assoc x y z]
  calc
    _ = sectionMap q hq x * sectionMap q hq y * sectionMap q hq z *
        (sectionMap q hq (x*(y*z)))⁻¹ := by group
    _ = sectionMap q hq x * (factor q hq hc y z).val *
        sectionMap q hq (y*z) * (sectionMap q hq (x*(y*z)))⁻¹ := by
      dsimp [factor]; group
    _ = _ := by rw [hcomm]; group

theorem remainder_mul (h k : H) :
    remainder q hq hc (h*k)=remainder q hq hc h * remainder q hq hc k *
      factor q hq hc (q h) (q k) := by
  apply Subtype.ext
  change h*k*(sectionMap q hq (q (h*k)))⁻¹ =
    (h*(sectionMap q hq (q h))⁻¹) * (remainder q hq hc k).val *
      (sectionMap q hq (q h)*sectionMap q hq (q k)*
        (sectionMap q hq (q h*q k))⁻¹)
  have hcomm := Subgroup.mem_center_iff.mp (hc (remainder q hq hc k).property)
    (sectionMap q hq (q h))⁻¹
  symm
  calc
    _ = h * ((sectionMap q hq (q h))⁻¹ * (remainder q hq hc k).val) *
      (sectionMap q hq (q h)*sectionMap q hq (q k)*
        (sectionMap q hq (q h*q k))⁻¹) := by group
    _ = h * ((remainder q hq hc k).val * (sectionMap q hq (q h))⁻¹) *
      (sectionMap q hq (q h)*sectionMap q hq (q k)*
        (sectionMap q hq (q h*q k))⁻¹) := by rw [hcomm]
    _ = _ := by dsimp [remainder]; rw [map_mul]; group

end IntegralTransgression
end IntegralTransgression

end SimpleAmenable
end
end

end OAI
