import Mathlib
import OAI.Combinatorics.SharpRamsey.Geometry.ProjectionCenterBounds
import OAI.Combinatorics.SharpRamsey.Geometry.ProjectionCapture

namespace OAI

section
namespace SharpLogRamsey.Projection
open Finset Incidence
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def quotientCut (T : Finset (Projectivization K (Module.Dual K V)))
    (z : Projectivization K V) : Finset (Projectivization K (Module.Dual K (V ⧸ z.submodule))) :=
  (T.subtype (SharpLogRamsey.Incidence.Incident z)).image (projectDual z)

lemma quotientCut_card (T : Finset (Projectivization K (Module.Dual K V)))
    (z : Projectivization K V) : (quotientCut T z).card=(cut T z).card := by
  rw [quotientCut,card_image_of_injective _ (projectDual_injective z)]
  simp only [card_subtype,cut]

lemma quotientCut_mono {T U : Finset (Projectivization K (Module.Dual K V))}
    (h : T⊆U) (z : Projectivization K V) : quotientCut T z⊆quotientCut U z := by
  apply image_subset_image
  intro t ht
  exact mem_subtype.mpr (h (mem_subtype.mp ht))

lemma projected_mono {S U : Finset (Projectivization K V)} (h : S⊆U)
    (z : Projectivization K V) : projected S z⊆projected U z := by
  apply image_subset_image
  intro p hp
  exact mem_subtype.mpr (h (mem_subtype.mp hp))

lemma quotient_incidence_le (S : Finset (Projectivization K V))
    (T : Finset (Projectivization K (Module.Dual K V))) (z : Projectivization K V) :
    incidenceCount (projected S z) (quotientCut T z)≤ incidenceCount S (cut T z) := by
  unfold incidenceCount quotientCut
  rw [sum_image (fun a ha b hb he => projectDual_injective z he)]
  have hrow (t : {t : Projectivization K (Module.Dual K V) // SharpLogRamsey.Incidence.Incident z t}) :
      ((projected S z).filter (fun p => SharpLogRamsey.Incidence.Incident p (projectDual z t))).card≤
        (S.filter (fun p => SharpLogRamsey.Incidence.Incident p t.val)).card := by
    unfold projected
    rw [filter_image]
    simp only [project_incident_iff]
    apply card_image_le.trans
    apply card_le_card_of_injOn (fun p : {p : Projectivization K V // p≠z} => p.val)
    · intro p hp
      exact mem_filter.mpr ⟨mem_subtype.mp (mem_filter.mp hp).1,(mem_filter.mp hp).2⟩
    · intro p hp r hr he
      exact Subtype.ext he
  apply (sum_le_sum (fun t ht => hrow t)).trans_eq
  have he : (T.subtype (SharpLogRamsey.Incidence.Incident z)).image Subtype.val=cut T z := by
    ext t
    simp [cut]
  rw [←he,sum_image (fun a ha b hb h => Subtype.ext h)]

end
end SharpLogRamsey.Projection

end

end OAI
