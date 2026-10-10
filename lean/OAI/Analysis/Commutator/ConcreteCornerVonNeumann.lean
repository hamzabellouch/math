import Mathlib
import OAI.Analysis.Commutator.CornerAlgebra
import OAI.Analysis.Commutator.CornerCyclic

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

namespace Kadison.ConcreteCorner

open MatrixCornerHilbert ReducingRepresentation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H)

instance closedCarrier : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (M : Set (H →L[ℂ] H))
  rw [←M.centralizer_centralizer]
  exact Set.isClosed_centralizer _

abbrev Algebra := M.toStarSubalgebra

def inclusion : Algebra M →⋆ₐ[ℂ] (H →L[ℂ] H) := M.toStarSubalgebra.subtype

@[simp] lemma inclusion_apply (a : Algebra M) : inclusion M a=(a:H →L[ℂ] H) := rfl

lemma inclusion_injective : Function.Injective (inclusion M) := Subtype.val_injective

lemma inclusion_range : Set.range (inclusion M)=(M : Set (H →L[ℂ] H)) := by
  ext a
  exact ⟨fun ⟨b,h⟩ => h ▸ b.property, fun h => ⟨⟨a,h⟩,rfl⟩⟩

variable {M} {p : Algebra M} (hp : IsStarProjection p)

abbrev Space (_hp : IsStarProjection p) := fixedSpace (inclusion M p)

abbrev representation := corner (inclusion M) hp

abbrev project : H →L[ℂ] Space hp := cornerProjection (inclusion M) hp

@[simp] lemma project_apply (x : H) : (project hp x:H)=(p:H →L[ℂ] H) x := rfl

lemma representation_project (a : Corner hp) (x : H) :
    (representation hp a (project hp x):H)=((a:Algebra M):H →L[ℂ] H) x := by
  change ((a:Algebra M):H →L[ℂ] H) ((p:H →L[ℂ] H) x)=((a:Algebra M):H →L[ℂ] H) x
  exact congrArg (fun b : Algebra M => (b:H →L[ℂ] H) x) a.property.2

lemma representation_injective : Function.Injective (representation hp) := by
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  ext x
  have he := congrArg (fun T : Space hp →L[ℂ] Space hp => (T (project hp x):H)) h
  simpa only [representation_project] using he

def lift (T : Space hp →L[ℂ] Space hp) : H →L[ℂ] H :=
  (fixedSpace (inclusion M p)).subtypeL.comp (T.comp (project hp))

@[simp] lemma lift_apply (T : Space hp →L[ℂ] Space hp) (x : H) :
    lift hp T x=(T (project hp x):H) := rfl

@[simp] lemma project_fixed (x : Space hp) : project hp (x:H)=x :=
  cornerProjection_fixed (inclusion M) hp x

lemma lift_left (T : Space hp →L[ℂ] Space hp) : (p:H →L[ℂ] H)*lift hp T=lift hp T := by
  ext x
  exact fixed_apply _ _

lemma lift_right (T : Space hp →L[ℂ] Space hp) : lift hp T*(p:H →L[ℂ] H)=lift hp T := by
  ext x
  change (T (project hp (project hp x:H)):H)=(T (project hp x):H)
  rw [project_fixed]

variable (R : H →L[ℂ] H) (hR : R∈M.commutant)

include hR in
lemma commutant_preserves (x : H) (hx : x∈Space hp) : R x∈Space hp := by
  rw [mem_fixedSpace] at hx ⊢
  have he := VonNeumannAlgebra.mem_commutant_iff.mp hR (p:H →L[ℂ] H) p.property
  calc
    inclusion M p (R x) = R (inclusion M p x) := congrArg (fun T : H →L[ℂ] H => T x) he
    _ = R x := by rw [hx]

def restrictCommutant : Space hp →L[ℂ] Space hp := R.restrict (commutant_preserves hp R hR)

@[simp] lemma restrictCommutant_apply (x : Space hp) : (restrictCommutant hp R hR x:H)=R x := rfl

lemma project_commutant (x : H) : project hp (R x)=restrictCommutant hp R hR (project hp x) := by
  apply Subtype.ext
  exact congrArg (fun T : H →L[ℂ] H => T x)
    (VonNeumannAlgebra.mem_commutant_iff.mp hR (p:H →L[ℂ] H) p.property)

lemma restrictCommutant_centralizer : restrictCommutant hp R hR ∈
    Set.centralizer (Set.range (representation hp)) := by
  rintro _ ⟨a,rfl⟩
  ext x
  exact congrArg (fun T : H →L[ℂ] H => T (x:H))
    (VonNeumannAlgebra.mem_commutant_iff.mp hR
      ((a:Algebra M):H →L[ℂ] H) (a:Algebra M).property)

include hR in
lemma lift_commutes {T : Space hp →L[ℂ] Space hp}
    (hT : T∈Set.centralizer (Set.centralizer (Set.range (representation hp)))) :
    R*lift hp T=lift hp T*R := by
  have he := hT _ (restrictCommutant_centralizer hp R hR)
  ext x
  change R (T (project hp x):H)=(T (project hp (R x)):H)
  rw [project_commutant hp R hR]
  exact congrArg (fun F : Space hp →L[ℂ] Space hp => (F (project hp x):H)) he

lemma lift_mem {T : Space hp →L[ℂ] Space hp}
    (hT : T∈Set.centralizer (Set.centralizer (Set.range (representation hp)))) :
    lift hp T∈M := by
  rw [← SetLike.mem_coe,←M.centralizer_centralizer]
  intro R hR
  exact lift_commutes hp R (VonNeumannAlgebra.mem_commutant_iff.mpr hR) hT

lemma corner_bicommutant :
    Set.centralizer (Set.centralizer (Set.range (representation hp)))=
      Set.range (representation hp) := by
  apply Set.Subset.antisymm
  · intro T hT
    let a : Algebra M := ⟨lift hp T,lift_mem hp hT⟩
    let b : Corner hp := ⟨a,Subtype.ext (lift_left hp T),Subtype.ext (lift_right hp T)⟩
    refine ⟨b,?_⟩
    ext x
    change (T (project hp (x:H)):H)=(T x:H)
    rw [project_fixed]
  · intro T hT R hR
    exact (hR T hT).symm

def vonNeumann : VonNeumannAlgebra (Space hp) where
  toStarSubalgebra := (representation hp).range
  centralizer_centralizer' := by
    change Set.centralizer (Set.centralizer (Set.range (representation hp))) =
      Set.range (representation hp)
    exact corner_bicommutant hp

lemma vonNeumann_range : Set.range (representation hp)=
    (vonNeumann hp : Set (Space hp →L[ℂ] Space hp)) := rfl

end Kadison.ConcreteCorner

end

end
end

end OAI
