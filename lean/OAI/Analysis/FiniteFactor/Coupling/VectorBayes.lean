import OAI.Analysis.FiniteFactor.Coupling.Infinite
import OAI.Analysis.FiniteFactor.Coupling.FiniteLaw
import OAI.Analysis.FiniteFactor.ProductKernel

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal
noncomputable section
namespace CouplingParameters

/-- The orientation records the conditioning endpoint first. -/
def orientPair (right : Bool) (z : ℝ × ℝ) : ℝ × ℝ :=
  (endpoint right z, endpoint (!right) z)

theorem orientPair_measurable (right : Bool) : Measurable (orientPair right) :=
  (endpoint_measurable right).prodMk (endpoint_measurable (!right))

theorem posterior_compProd (p : CouplingParameters) (right : Bool) :
    (p.selectedLaw true right) ⊗ₘ (p.posteriorKernel right) =
      p.coupling.map (orientPair right) := by
  apply Measure.ext_prod
  intro A B hA hB
  rw [Measure.compProd_apply_prod hA hB, selectedLaw_endpoint,
    Measure.map_apply (orientPair_measurable right) (hA.prod hB)]
  cases right
  · exact p.conditional_given_x hA hB
  · have he : orientPair true ⁻¹' (A ×ˢ B) = B ×ˢ A := by
      ext z
      simp [orientPair, endpoint, and_comm]
    rw [he]
    exact p.conditional_given_y hA hB

def vectorCoupling {ι : Type*} (p : ι → CouplingParameters) :
    Measure (ι → Fin 6 × (ℝ × ℝ)) := Measure.infinitePi (fun i => (p i).labelledCoupling)

instance vectorCoupling_probability {ι : Type*} (p : ι → CouplingParameters) :
    IsProbabilityMeasure (vectorCoupling p) := by unfold vectorCoupling; infer_instance

def vectorEndpoint {ι : Type*} (right : ι → Bool) (ω : ι → Fin 6 × (ℝ × ℝ)) (i : ι) : ℝ :=
  endpoint (right i) (ω i).2

theorem vectorEndpoint_measurable {ι : Type*} (right : ι → Bool) : Measurable (vectorEndpoint right) := by
  exact Measurable.of_eval (fun i => (endpoint_measurable (right i)).comp
    (measurable_snd.comp (measurable_pi_apply i)))

theorem vectorEndpoint_law {ι : Type*} (p : ι → CouplingParameters) (right : ι → Bool) :
    (vectorCoupling p).map (vectorEndpoint right) =
      Measure.infinitePi (fun i => (p i).selectedLaw true (right i)) := by
  unfold vectorCoupling vectorEndpoint
  rw [Measure.infinitePi_map_pi _
    (f := fun i (z : Fin 6 × (ℝ × ℝ)) => endpoint (right i) z.2)
    (fun i => (endpoint_measurable (right i)).comp measurable_snd)]
  simp_rw [labelled_endpoint_density]
  rfl

def vectorPosterior {ι : Type*} (p : ι → CouplingParameters) (right : ι → Bool) :
    Kernel (ι → ℝ) (ι → ℝ) := independentKernel (fun i => (p i).posteriorKernel (right i))

instance vectorPosterior_markov {ι : Type*} (p : ι → CouplingParameters) (right : ι → Bool) :
    IsMarkovKernel (vectorPosterior p right) := by unfold vectorPosterior; infer_instance

/-- The product posterior is the conditional law given the entire selected
endpoint vector. This identity holds for the actual augmented product law. -/
theorem vectorPosterior_disintegration {ι : Type*} (p : ι → CouplingParameters) (right : ι → Bool) :
    ((vectorCoupling p).map (vectorEndpoint right)) ⊗ₘ (vectorPosterior p right) =
      (vectorCoupling p).map (fun ω => (vectorEndpoint right ω, vectorEndpoint (fun i => !right i) ω)) := by
  rw [vectorEndpoint_law]
  have hh := independentKernel_compProd (fun i => (p i).selectedLaw true (right i))
    (fun i => (p i).posteriorKernel (right i))
  simp_rw [posterior_compProd] at hh
  let zip : (ι → ℝ) × (ι → ℝ) → (ι → ℝ × ℝ) := fun z i => (z.1 i, z.2 i)
  let unzip : (ι → ℝ × ℝ) → (ι → ℝ) × (ι → ℝ) := fun z => (fun i => (z i).1, fun i => (z i).2)
  have hz : Measurable zip := by fun_prop
  have hu : Measurable unzip := by fun_prop
  have hleft := congrArg (fun ν : Measure (ι → ℝ × ℝ) => ν.map unzip) hh
  rw [Measure.map_map hu hz] at hleft
  have hid : unzip ∘ zip = id := rfl
  rw [hid, Measure.map_id] at hleft
  change _ = (Measure.infinitePi (fun i => (p i).coupling.map (orientPair (right i)))).map unzip at hleft
  unfold vectorPosterior
  rw [hleft]
  have hp : (vectorCoupling p).map (fun ω i => orientPair (right i) (ω i).2) =
      Measure.infinitePi (fun i => (p i).coupling.map (orientPair (right i))) := by
    unfold vectorCoupling
    rw [Measure.infinitePi_map_pi _
      (f := fun i (z : Fin 6 × (ℝ × ℝ)) => orientPair (right i) z.2)
      (fun i => (orientPair_measurable (right i)).comp measurable_snd)]
    congr 1
    funext i
    unfold coupling
    rw [Measure.map_map (orientPair_measurable (right i)) measurable_snd]
    rfl
  have hv : Measurable (fun (ω : ι → Fin 6 × (ℝ × ℝ)) i => orientPair (right i) (ω i).2) :=
    Measurable.of_eval (fun i => (orientPair_measurable (right i)).comp
      (measurable_snd.comp (measurable_pi_apply i)))
  rw [← hp, Measure.map_map hu hv]
  rfl

/-- Full-vector conditional independence, including both endpoint orientations.
Together with vectorPosterior_disintegration this is independence under the
actual conditional law, not a statement about a separately chosen product. -/
theorem vectorPosterior_independence {ι : Type*} (p : ι → CouplingParameters) (right : ι → Bool)
    (x : ι → ℝ) (I : Finset ι) (S : ι → Set ℝ) (hS : ∀ i ∈ I, MeasurableSet (S i)) :
    vectorPosterior p right x (Set.pi (I : Set ι) S) =
      ∏ i ∈ I, (p i).posteriorKernel (right i) (x i) (S i) :=
  independentKernel_pi _ x I S hS

/-- Defining conditional identity for every measurable pair of full-vector events. -/
theorem vectorPosterior_rectangle {ι : Type*} (p : ι → CouplingParameters) (right : ι → Bool)
    {A B : Set (ι → ℝ)} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (∫⁻ x in A, vectorPosterior p right x B ∂((vectorCoupling p).map (vectorEndpoint right))) =
      vectorCoupling p {ω | vectorEndpoint right ω ∈ A ∧ vectorEndpoint (fun i => !right i) ω ∈ B} := by
  rw [← Measure.compProd_apply_prod hA hB, vectorPosterior_disintegration,
    Measure.map_apply ((vectorEndpoint_measurable right).prodMk
      (vectorEndpoint_measurable (fun i => !right i))) (hA.prod hB)]
  rfl

end CouplingParameters
end
end FiniteFactor

end OAI
