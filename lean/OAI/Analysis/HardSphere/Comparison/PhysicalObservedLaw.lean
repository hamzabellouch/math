import Mathlib
import OAI.Analysis.HardSphere.Geometry.UniformBath
import OAI.Analysis.HardSphere.Conditioning.PhysicalObservation

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {E : Type*} [MeasurableSpace E]
attribute [local instance] permBathSpace permBathSingleton

def primaryBathKernel (b : Bool) (i : Fin (n+1)) :
    Kernel (Option (Fin (n+1))→E) (E×E×(Fin n→E)) :=
  (Kernel.id ×ₖ Kernel.const _ (uniformBathOrder n)).map (orderedPrimaryObservation b i)
instance primaryBathKernel_markov (b : Bool) (i : Fin (n+1)) :
    IsMarkovKernel (primaryBathKernel (E:=E) b i) :=
  Kernel.IsMarkovKernel.map _ (orderedPrimaryObservation_measurable b i)

lemma primaryBathKernel_apply (b : Bool) (i : Fin (n+1)) (F : Option (Fin (n+1))→E) :
    primaryBathKernel b i F=(uniformBathOrder n).map (fun τ ↦ orderedPrimaryObservation b i (F,τ)) := by
  rw [primaryBathKernel,Kernel.map_apply _ (orderedPrimaryObservation_measurable b i),
    Kernel.prod_apply,Kernel.id_apply,Kernel.const_apply,Measure.dirac_prod,
    Measure.map_map (orderedPrimaryObservation_measurable b i) measurable_prodMk_left]
  rfl
end HardSphere.Comparison

namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable
variable {J : Type*} [Fintype J] [DecidableEq J]

def physicalBathKernel {N K M G : ℕ} {L : Length} (particle : J↪Fin (N+1))
    (b : Bool) (i : J) :
    Kernel (PhysicalDatum (N+1) K M G L×(Option J→C(Time,Point)))
      (Torus L×Torus L×(Fin N→Torus L)) :=
  (primaryBathKernel b (particle i)).comap (physicalFullMidpoint particle)
    (physicalFullMidpoint_measurable particle)
instance physicalBathKernel_markov {N K M G : ℕ} {L : Length} (particle : J↪Fin (N+1))
    (b : Bool) (i : J) : IsMarkovKernel (physicalBathKernel (K:=K) (M:=M) (G:=G) (L:=L) particle b i) := by
  unfold physicalBathKernel; infer_instance

theorem physicalPairedRoute_same_observed {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (u : Time)
    (particle : J↪Fin (N+1)) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7)
    (hc : ∀k,projectPoint L (routeCellPeriod (v k.succ) (v k.castSucc) (steps k))=0)
    (d : PhysicalDatum (N+1) K M G L)
    (hhome : ∀k,datumHome hL d (particle (labels k))=v k.castSucc)
    (haccess : ∀k,datumAccessible hL g m t r R C S u (particle (labels k)) d) :
    ((physicalBathKernel particle true (labels 0)).comap (mγ:=inferInstance) (fun z : (Option J→C(Time,Point))×(Option J→C(Time,Point)) ↦ (d,z.1))
      (measurable_const.prodMk measurable_fst)) ∘ₘ physicalPairedRoute hL g m t r R C S u particle labels v steps d =
    ((physicalBathKernel particle false (labels (Fin.last n))).comap (mγ:=inferInstance) (fun z : (Option J→C(Time,Point))×(Option J→C(Time,Point)) ↦ (d,z.2))
      (measurable_const.prodMk measurable_snd)) ∘ₘ physicalPairedRoute hL g m t r R C S u particle labels v steps d := by
  apply Measure.comp_congr
  filter_upwards [physicalPairedRoute_midpoint hL g m t r R C S ht u particle labels v steps hc d hhome haccess] with z hz
  change primaryBathKernel true (particle (labels 0)) (physicalFullMidpoint particle (d,z.1))=
    primaryBathKernel false (particle (labels (Fin.last n))) (physicalFullMidpoint particle (d,z.2))
  rw [primaryBathKernel_apply,primaryBathKernel_apply]
  exact uniformBath_same_observation (routePermutation (labels.trans particle))
    (particle (labels 0)) (particle (labels (Fin.last n)))
    (routePermutation_star n (labels.trans particle))
    (routePermutation_lastLabel n (labels.trans particle)) _ _ hz

end HardSphere.Groups
end
end

end OAI
