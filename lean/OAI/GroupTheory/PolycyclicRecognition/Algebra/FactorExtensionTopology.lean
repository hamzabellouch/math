import OAI.GroupTheory.PolycyclicRecognition.Algebra.FactorExtensionMap
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Homeomorph.Lemmas

namespace OAI

/-! # Completing the kernel while retaining the discrete quotient -/

noncomputable section
namespace PolycyclicRecognition
open Filter Topology

theorem continuous_discrete_parameter {Q X Y : Type*}
    [TopologicalSpace Q] [DiscreteTopology Q] [TopologicalSpace X] [TopologicalSpace Y]
    (f : Q → X → Y) (hf : ∀ q, Continuous (f q)) :
    Continuous (fun p : Q × X => f p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hq : ∀ᶠ q : Q in 𝓝 p.1, q = p.1 := by
    simp only [nhds_discrete, Filter.eventually_pure]
  have he : ∀ᶠ z : Q × X in 𝓝 p, z.1 = p.1 :=
    (continuous_fst.tendsto p).eventually hq
  apply ((hf p.1).continuousAt.comp continuous_snd.continuousAt).congr_of_eventuallyEq
  filter_upwards [he] with z hz
  rw [hz]
  rfl

variable {N Q : Type*} [Group N] [Group Q] [TopologicalSpace N] [TopologicalSpace Q]
  (S : NonabelianFactorSystem N Q)

@[instance_reducible] def factorExtensionTopology : TopologicalSpace (FactorExtension S) :=
  TopologicalSpace.induced (FactorExtension.equivProd S) inferInstance

attribute [local instance] factorExtensionTopology

def factorExtensionHomeomorph : FactorExtension S ≃ₜ N × Q where
  toEquiv := FactorExtension.equivProd S
  continuous_toFun := continuous_induced_dom
  continuous_invFun := continuous_induced_rng.2 continuous_id

theorem continuous_factor_left : Continuous (fun a : FactorExtension S => a.left) :=
  (factorExtensionHomeomorph S).continuous.fst

theorem continuous_factor_right : Continuous (fun a : FactorExtension S => a.right) :=
  (factorExtensionHomeomorph S).continuous.snd

theorem continuous_factor_inl : Continuous (FactorExtension.inl S) :=
  (factorExtensionHomeomorph S).symm.continuous.comp (continuous_id.prodMk continuous_const)

instance [T2Space N] [T2Space Q] : T2Space (FactorExtension S) :=
  (factorExtensionHomeomorph S).isEmbedding.t2Space

instance [LocallyCompactSpace N] [LocallyCompactSpace Q] :
    LocallyCompactSpace (FactorExtension S) :=
  (factorExtensionHomeomorph S).locallyCompactSpace_iff.mpr inferInstance

variable [IsTopologicalGroup N] [DiscreteTopology Q]

/-- Individual continuous kernel automorphisms suffice over a discrete quotient. -/
theorem factorExtensionTopologicalGroup (ha : ∀ q, Continuous (S.action q)) :
    IsTopologicalGroup (FactorExtension S) := by
  have hA : Continuous (fun p : Q × N => S.action p.1 p.2) :=
    continuous_discrete_parameter (fun q x => S.action q x) ha
  have hc : Continuous (fun p : Q × Q => S.factor p.1 p.2) := continuous_of_discreteTopology
  refine { continuous_mul := ?_, continuous_inv := ?_ }
  · apply continuous_induced_rng.2
    exact (((continuous_factor_left S).comp continuous_fst).mul
      (hA.comp (((continuous_factor_right S).comp continuous_fst).prodMk
        ((continuous_factor_left S).comp continuous_snd)))).mul
      (hc.comp (((continuous_factor_right S).comp continuous_fst).prodMk
        ((continuous_factor_right S).comp continuous_snd))) |>.prodMk
      (((continuous_factor_right S).comp continuous_fst).mul
        ((continuous_factor_right S).comp continuous_snd))
  · apply continuous_induced_rng.2
    exact ((hc.comp ((continuous_factor_right S).inv.prodMk
      (continuous_factor_right S))).inv.mul
      (hA.comp ((continuous_factor_right S).inv.prodMk
        (continuous_factor_left S).inv))).prodMk (continuous_factor_right S).inv

end PolycyclicRecognition

end

end OAI
