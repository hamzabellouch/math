import Mathlib
import OAI.Combinatorics.SharpRamsey.Geometry.Projection
import OAI.Combinatorics.SharpRamsey.Learning.ValidationCover

namespace OAI

section
namespace SharpLogRamsey.ProjectiveDuality
open Incidence Finset
open scoped Classical BigOperators
noncomputable section
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

lemma incident_mapEquiv (e : V ≃ₗ[K] W) (a : Projectivization K V)
    (b : Projectivization K (Module.Dual K V)) :
    SharpLogRamsey.Incidence.Incident (mapEquiv e a) (mapEquiv e.symm.dualMap b) ↔ SharpLogRamsey.Incidence.Incident a b := by
  induction a using Projectivization.ind with
  | h v hv =>
    induction b using Projectivization.ind with
    | h f hf =>
      dsimp only [mapEquiv,Equiv.coe_fn_mk]
      rw [Projectivization.map_mk,Projectivization.map_mk,
        Projection.incident_mk_iff,Projection.incident_mk_iff]
      simp only [LinearEquiv.coe_coe,LinearEquiv.dualMap_apply,e.symm_apply_apply]

lemma incidenceCount_mapEquiv (e : V ≃ₗ[K] W)
    (S : Finset (Projectivization K V)) (T : Finset (Projectivization K (Module.Dual K V))) :
    incidenceCount (S.image (mapEquiv e)) (T.image (mapEquiv e.symm.dualMap))=
      incidenceCount S T := by
  unfold incidenceCount
  rw [sum_image (mapEquiv e.symm.dualMap).injective.injOn]
  apply sum_congr rfl
  intro t ht
  rw [filter_image]
  simp only [incident_mapEquiv]
  exact card_image_of_injective _ (mapEquiv e).injective

variable [FiniteDimensional K V]
lemma incidenceCount_bidual (S : Finset (Projectivization K V))
    (T : Finset (Projectivization K (Module.Dual K V))) :
    incidenceCount T (S.image bidual)=incidenceCount S T := by
  unfold incidenceCount
  rw [sum_image bidual.injective.injOn]
  simp only [incident_bidual]
  simp only [card_filter]
  rw [sum_comm]

lemma pullback_cover {α β : Type*} (e : α ≃ β) (U S : Finset α)
    (E : Finset β) (hE : E ⊆ U.image e) :
    E.image e.symm ⊆ U ∧ (E.image e.symm).card=E.card ∧
      (S∩E.image e.symm).card=((S.image e)∩E).card := by
  refine ⟨?_,card_image_of_injective _ e.symm.injective,?_⟩
  · intro a ha
    obtain ⟨b,hb,he⟩ := mem_image.mp ha
    obtain ⟨a₀,ha₀,he₀⟩ := mem_image.mp (hE hb)
    have hba : e.symm b=a₀ := by rw [←he₀,e.symm_apply_apply]
    rw [←he,hba]
    exact ha₀
  · have he : (S∩E.image e.symm).image e=(S.image e)∩E := by
      rw [image_inter _ _ e.injective]
      congr 1
      ext b
      simp
    rw [←he,card_image_of_injective _ e.injective]

end
end SharpLogRamsey.ProjectiveDuality

end

end OAI
