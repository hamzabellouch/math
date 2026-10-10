import Mathlib
import OAI.Analysis.Commutator.DerivationKaplansky
import OAI.Analysis.Commutator.MainMatrix
import OAI.Analysis.Commutator.MinimalCorner
import OAI.Analysis.Commutator.ConcreteCornerVonNeumann
import OAI.Analysis.Commutator.ReducingMatrix

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder

namespace Kadison.CentralCorner

open ConcreteCorner MatrixCornerHilbert ReducingRepresentation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def center (M : VonNeumannAlgebra H) : VonNeumannAlgebra H :=
  vonNeumannIntersection M M.commutant

lemma mem_center (M : VonNeumannAlgebra H) (a : H →L[ℂ] H) :
    a∈center M ↔ a∈M ∧ a∈Set.centralizer (M : Set (H →L[ℂ] H)) := by
  change a∈M ∧ a∈M.commutant ↔ _
  rw [VonNeumannAlgebra.mem_commutant_iff]
  rfl

variable (M : VonNeumannAlgebra H) {p : M} (hp : IsStarProjection p)
    (hz : (p:H →L[ℂ] H)∈Set.centralizer (M : Set (H →L[ℂ] H)))

include hz

lemma invariant (a : M) (x : H) (hx : x∈Space hp) : (a:H →L[ℂ] H) x∈Space hp := by
  rw [mem_fixedSpace] at hx ⊢
  change (p:H →L[ℂ] H) x=x at hx
  change (p:H →L[ℂ] H) ((a:H →L[ℂ] H) x)=(a:H →L[ℂ] H) x
  rw [←mul_apply_eq_comp,←hz a a.property,mul_apply_eq_comp,hx]

def restriction : M →⋆ₐ[ℂ] (Space hp →L[ℂ] Space hp) :=
  restrict M.toStarSubalgebra.subtype (Space hp) (invariant M hp hz)

lemma restriction_apply (a : M) (x : Space hp) : (restriction M hp hz a x:H)=(a:H →L[ℂ] H) (x:H) := rfl

def cut (a : M) : Corner hp := ⟨p*a,by rw [←mul_assoc,hp.isIdempotentElem.eq],by
  have hc : a*p=p*a := Subtype.ext (hz a a.property)
  rw [mul_assoc,hc,←mul_assoc,hp.isIdempotentElem.eq]⟩

lemma restriction_eq_corner (a : M) : restriction M hp hz a=representation hp (cut M hp hz a) := by
  ext x
  change (a:H →L[ℂ] H) (x:H)=(p:H →L[ℂ] H) ((a:H →L[ℂ] H) (x:H))
  exact ((mem_fixedSpace _ _).mp (invariant M hp hz a x x.property)).symm

lemma corner_restriction (a : Corner hp) : restriction M hp hz (a:M)=representation hp a := by
  ext x
  rfl

lemma restriction_range : (restriction M hp hz).range=(vonNeumann hp).toStarSubalgebra := by
  apply SetLike.coe_injective
  change Set.range (restriction M hp hz)=Set.range (representation hp)
  apply Set.Subset.antisymm
  · rintro _ ⟨a,rfl⟩
    exact ⟨cut M hp hz a,(restriction_eq_corner M hp hz a).symm⟩
  · rintro _ ⟨a,rfl⟩
    exact ⟨(a:M),corner_restriction M hp hz a⟩

lemma lift_restriction (T : Space hp →L[ℂ] Space hp) (a : M) :
    (a:H →L[ℂ] H)*lift hp T=lift hp (restriction M hp hz a*T) := by
  ext x
  rfl

lemma project_mul (a : M) (x : H) :
    project hp ((a:H →L[ℂ] H) x)=restriction M hp hz a (project hp x) := by
  apply Subtype.ext
  exact congrArg (fun T : H →L[ℂ] H => T x) (hz a a.property).symm

lemma lift_mul_restriction (T : Space hp →L[ℂ] Space hp) (a : M) :
    lift hp T*(a:H →L[ℂ] H)=lift hp (T*restriction M hp hz a) := by
  ext x
  change (T (project hp ((a:H →L[ℂ] H) x)):H)=(T (restriction M hp hz a (project hp x)):H)
  rw [project_mul M hp hz]

lemma lift_central {T : Space hp →L[ℂ] Space hp}
    (hT : T∈vonNeumann hp)
    (hTc : T∈Set.centralizer (vonNeumann hp : Set (Space hp →L[ℂ] Space hp))) :
    lift hp T∈center M := by
  apply (mem_center M _).mpr
  refine ⟨lift_mem hp (by rw [corner_bicommutant]; exact hT),?_⟩
  intro a ha
  rcases (show ∃ b : M,(b:H →L[ℂ] H)=a from ⟨⟨a,ha⟩,rfl⟩) with ⟨b,rfl⟩
  rw [lift_restriction M hp hz,lift_mul_restriction M hp hz]
  congr 1
  apply hTc
  change restriction M hp hz b∈(vonNeumann hp).toStarSubalgebra
  rw [←restriction_range M hp hz]
  exact Set.mem_range_self b

theorem factor_of_minimal_center
    (hmin : AtomicFactor.IsMinimalProjection (center M) (p:H →L[ℂ] H)) :
    FactorCorner.IsFactor (vonNeumann hp) := by
  intro T hT hTc
  obtain ⟨c,hc⟩ := AtomicFactor.corner_scalar (center M) hmin
    (lift_central M hp hz hT hTc) (lift_left hp T) (lift_right hp T)
  refine ⟨c,?_⟩
  ext x
  have he := congrArg (fun S : H →L[ℂ] H => S (x:H)) hc
  change (T x:H)=c • (x:H)
  change (T (project hp (x:H)):H)=c • (p:H →L[ℂ] H) (x:H) at he
  rw [project_fixed,show (p:H →L[ℂ] H) (x:H)=(x:H) from MatrixCornerHilbert.fixed_apply (inclusion M p) x] at he
  exact he

lemma bicommutant_restriction : NormalGNS.bicommutant (restriction M hp hz).range=vonNeumann hp := by
  rw [restriction_range M hp hz]
  apply SetLike.coe_injective
  apply Set.ext
  intro T
  rw [SetLike.mem_coe,SetLike.mem_coe,NormalGNS.mem_bicommutant]
  change T∈Set.centralizer (Set.centralizer (vonNeumann hp : Set (Space hp →L[ℂ] Space hp))) ↔ T∈vonNeumann hp
  rw [(vonNeumann hp).centralizer_centralizer]
  rfl

theorem seminorm_le (Y : H →L[ℂ] H)
    (hY : ∀ x∈Space hp,Y x∈Space hp) :
    commutatorSeminorm (vonNeumann hp) (Y.restrict hY)≤commutatorSeminorm M Y := by
  rw [←bicommutant_restriction M hp hz]
  apply DerivationColumns.seminorm_bicommutant_le _ _ (commutatorSeminorm_nonneg M Y)
  intro a
  rw [←compression_eq_restrict (Space hp) Y hY]
  exact (norm_commutator_compression_le M.toStarSubalgebra.subtype (Space hp)
    (invariant M hp hz) Y a).trans (commutator_bound M Y a.property)

end Kadison.CentralCorner

end

end
end

end OAI
