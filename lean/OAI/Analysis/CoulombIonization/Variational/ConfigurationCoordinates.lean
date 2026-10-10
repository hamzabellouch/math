import Mathlib
import OAI.Analysis.CoulombIonization.Localization.ArraySymmetry
import OAI.Analysis.CoulombIonization.ThomasFermi.FlatFermionAverage

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff

namespace CoulombAtom
variable {N : ℕ}

def configurationCoordinates (N : ℕ) : Configuration N ≃L[ℝ] ((Fin N × Fin 3) → ℝ) :=
  ({ toFun := flattenConfiguration N
     invFun := fun x i => WithLp.toLp 2 (fun a => x (i,a))
     left_inv := by intro x; rfl
     right_inv := by intro x; rfl
     map_add' := (flattenConfiguration N).map_add
     map_smul' := (flattenConfiguration N).map_smul }: Configuration N ≃ₗ[ℝ] ((Fin N × Fin 3) → ℝ)).toContinuousLinearEquiv

@[simp] lemma configurationCoordinates_apply (x : Configuration N) (q : Fin N × Fin 3) :
    configurationCoordinates N x q = x q.1 q.2 := rfl

@[simp] lemma configurationCoordinates_symm_apply (x : (Fin N × Fin 3) → ℝ) (i : Fin N) (a : Fin 3) :
    (configurationCoordinates N).symm x i a = x (i,a) := rfl

lemma configurationCoordinates_eq_flatten :
    (configurationCoordinates N : Configuration N → ((Fin N × Fin 3) → ℝ)) = flattenConfiguration N := rfl

lemma configurationCoordinates_preserving (N : ℕ) : MeasurePreserving (configurationCoordinates N) := by
  refine ⟨(configurationCoordinates N).continuous.measurable, ?_⟩
  apply Eq.symm
  change Measure.pi (fun _ : Fin N × Fin 3 => (volume : Measure ℝ)) = _
  apply Measure.pi_eq
  intro A hA
  rw [Measure.map_apply (configurationCoordinates N).continuous.measurable (MeasurableSet.univ_pi hA)]
  have he : configurationCoordinates N ⁻¹' pi univ A =
      pi univ (fun i : Fin N => (WithLp.ofLp : Space → (Fin 3 → ℝ)) ⁻¹'
        pi univ (fun a => A (i,a))) := by
    ext x
    simp only [mem_preimage,mem_univ_pi,configurationCoordinates_apply,Prod.forall]
  rw [he,volume_pi,Measure.pi_pi]
  calc
    _ = ∏ i : Fin N, ∏ a : Fin 3, volume (A (i,a)) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [(PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage
        (MeasurableSet.univ_pi (fun a => hA (i,a))).nullMeasurableSet,volume_pi,Measure.pi_pi]
    _ = _ := (Fintype.prod_prod_type (fun q : Fin N × Fin 3 => (volume : Measure ℝ) (A q))).symm

lemma configurationCoordinates_symm_preserving (N : ℕ) :
    MeasurePreserving (configurationCoordinates N).symm :=
  MeasurePreserving.symm (configurationCoordinates N).toHomeomorph.toMeasurableEquiv
    (configurationCoordinates_preserving N)

lemma configurationCoordinates_single (q : Fin N × Fin 3) :
    (configurationCoordinates N).symm (Pi.single q 1) = direction q.1 q.2 := by
  apply (configurationCoordinates N).injective
  rw [(configurationCoordinates N).apply_symm_apply]
  exact (flattenConfiguration_direction q.1 q.2).symm

lemma configurationCoordinates_permute (π : Equiv.Perm (Fin N)) (x : (Fin N × Fin 3) → ℝ) :
    (configurationCoordinates N).symm (CoulombNeumann.flatPermutation π x) =
      (configurationCoordinates N).symm x ∘ π := by
  funext i
  apply WithLp.ofLp_injective
  funext a
  change CoulombNeumann.flatPermutation π x (i,a) = x (π i,a)
  simp [CoulombNeumann.flatPermutation_apply,CoulombNeumann.particlePermute]

lemma integral_configurationCoordinates {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ((Fin N × Fin 3) → ℝ) → E) :
    (∫ x : Configuration N, f (configurationCoordinates N x)) = ∫ x, f x :=
  (configurationCoordinates_preserving N).integral_comp
    (configurationCoordinates N).toHomeomorph.measurableEmbedding f

lemma integral_configurationCoordinates_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Configuration N → E) :
    (∫ x : (Fin N × Fin 3) → ℝ, f ((configurationCoordinates N).symm x)) = ∫ x, f x :=
  (configurationCoordinates_symm_preserving N).integral_comp
    (configurationCoordinates N).symm.toHomeomorph.measurableEmbedding f

end CoulombAtom

end

end OAI
