import OAI.Analysis.FiniteFactor.Coupling.FinitePosteriorAC

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
namespace CouplingParameters

/-- The mixed posterior keeps every unselected coordinate fixed. -/
def mixedPosteriorKernel {ι : Type*} (p : ι → CouplingParameters) (r : ι → Bool) :
    Kernel (ι → ℝ) (ι → ℝ) := by
  letI : ∀ i, IsMarkovKernel (if r i then (p i).posteriorKernel false else Kernel.id) :=
    fun i => by split_ifs <;> infer_instance
  exact independentKernel (fun i => if r i then (p i).posteriorKernel false else Kernel.id)

instance mixedPosteriorKernel_markov {ι : Type*} (p : ι → CouplingParameters) (r : ι → Bool) :
    IsMarkovKernel (mixedPosteriorKernel p r) := by
  unfold mixedPosteriorKernel
  let : ∀ i, IsMarkovKernel (if r i then (p i).posteriorKernel false else Kernel.id) :=
    fun i => by split_ifs <;> infer_instance
  infer_instance

theorem mixedCoordinate_compProd (p : CouplingParameters) (r : Bool) :
    p.selectedLaw true false ⊗ₘ (if r then p.posteriorKernel false else Kernel.id) =
      p.labelledCoupling.map (fun ω => (endpoint false ω.2,endpoint r ω.2)) := by
  cases r
  · simp only [Bool.false_eq_true,ite_false]
    rw [Measure.compProd_id,selectedLaw_endpoint]
    unfold coupling
    rw [Measure.map_map (endpoint_measurable false) measurable_snd,
      Measure.map_map (by fun_prop) ((endpoint_measurable false).comp measurable_snd)]
    rfl
  · simp only [ite_true]
    rw [posterior_compProd]
    unfold coupling
    rw [Measure.map_map (orientPair_measurable false) measurable_snd]
    rfl

/-- Disintegration of every mixed endpoint pair under the actual augmented
product law, conditioned on the entire original x vector. -/
theorem mixedPosterior_disintegration {ι : Type*} (p : ι → CouplingParameters) (r : ι → Bool) :
    ((vectorCoupling p).map (vectorEndpoint (fun _ => false))) ⊗ₘ (mixedPosteriorKernel p r) =
      (vectorCoupling p).map (fun ω => (vectorEndpoint (fun _ => false) ω,vectorEndpoint r ω)) := by
  rw [vectorEndpoint_law]
  let κ := fun i => if r i then (p i).posteriorKernel false else Kernel.id
  let : ∀ i, IsMarkovKernel (κ i) := fun i => by dsimp [κ]; split_ifs <;> infer_instance
  have hh := independentKernel_compProd (fun i => (p i).selectedLaw true false) κ
  dsimp [κ] at hh
  simp_rw [mixedCoordinate_compProd] at hh
  let zip : (ι → ℝ) × (ι → ℝ) → (ι → ℝ × ℝ) := fun z i => (z.1 i,z.2 i)
  let unzip : (ι → ℝ × ℝ) → (ι → ℝ) × (ι → ℝ) := fun z => (fun i => (z i).1,fun i => (z i).2)
  have hz : Measurable zip := by fun_prop
  have hu : Measurable unzip := by fun_prop
  have hleft := congrArg (fun ν : Measure (ι → ℝ × ℝ) => ν.map unzip) hh
  rw [Measure.map_map hu hz] at hleft
  have hid : unzip ∘ zip = id := rfl
  rw [hid,Measure.map_id] at hleft
  unfold mixedPosteriorKernel
  rw [hleft]
  have hp : (vectorCoupling p).map (fun ω i => (endpoint false (ω i).2,endpoint (r i) (ω i).2)) =
      Measure.infinitePi (fun i => (p i).labelledCoupling.map
        (fun ω => (endpoint false ω.2,endpoint (r i) ω.2))) := by
    unfold vectorCoupling
    exact Measure.infinitePi_map_pi _ (f := fun i (ω : Fin 6 × (ℝ × ℝ)) =>
      (endpoint false ω.2,endpoint (r i) ω.2)) (fun i =>
        ((endpoint_measurable false).comp measurable_snd).prodMk
          ((endpoint_measurable (r i)).comp measurable_snd))
  have hv : Measurable (fun (ω : ι → Fin 6 × (ℝ × ℝ)) i =>
      (endpoint false (ω i).2,endpoint (r i) (ω i).2)) := by
    apply Measurable.of_eval
    intro i
    exact ((endpoint_measurable false).comp (measurable_snd.comp (measurable_pi_apply i))).prodMk
      ((endpoint_measurable (r i)).comp (measurable_snd.comp (measurable_pi_apply i)))
  rw [← hp,Measure.map_map hu hv]
  rfl

end CouplingParameters
end
end FiniteFactor

end OAI
