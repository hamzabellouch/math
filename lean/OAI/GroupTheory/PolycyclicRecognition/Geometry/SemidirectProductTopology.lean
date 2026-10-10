import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Connected.Basic

namespace OAI

/-! # The product topology on the Cartan semidirect cover -/

noncomputable section
namespace PolycyclicRecognition

variable {N D : Type*} [Group N] [Group D] [TopologicalSpace N] [TopologicalSpace D]
  (φ : D →* MulAut N)

@[instance_reducible]
def semidirectProductTopology : TopologicalSpace (N ⋊[φ] D) :=
  TopologicalSpace.induced SemidirectProduct.equivProd inferInstance

attribute [local instance] semidirectProductTopology

def semidirectProductHomeomorph : (N ⋊[φ] D) ≃ₜ N × D where
  toEquiv := SemidirectProduct.equivProd
  continuous_toFun := continuous_induced_dom
  continuous_invFun := continuous_induced_rng.2 continuous_id

theorem continuous_semidirect_left : Continuous (fun p : N ⋊[φ] D => p.left) :=
  (semidirectProductHomeomorph φ).continuous.fst

theorem continuous_semidirect_right : Continuous (fun p : N ⋊[φ] D => p.right) :=
  (semidirectProductHomeomorph φ).continuous.snd

theorem continuous_semidirect_inl :
    Continuous (SemidirectProduct.inl : N → N ⋊[φ] D) :=
  (semidirectProductHomeomorph φ).symm.continuous.comp
    (continuous_id.prodMk continuous_const)

theorem continuous_semidirect_inr :
    Continuous (SemidirectProduct.inr : D → N ⋊[φ] D) :=
  (semidirectProductHomeomorph φ).symm.continuous.comp
    (continuous_const.prodMk continuous_id)

instance [T2Space N] [T2Space D] : T2Space (N ⋊[φ] D) :=
  (semidirectProductHomeomorph φ).isEmbedding.t2Space

instance [LocallyCompactSpace N] [LocallyCompactSpace D] :
    LocallyCompactSpace (N ⋊[φ] D) :=
  (semidirectProductHomeomorph φ).locallyCompactSpace_iff.mpr inferInstance

instance [SecondCountableTopology N] [SecondCountableTopology D] :
    SecondCountableTopology (N ⋊[φ] D) :=
  (semidirectProductHomeomorph φ).secondCountableTopology

instance [ConnectedSpace N] [ConnectedSpace D] : ConnectedSpace (N ⋊[φ] D) :=
  (semidirectProductHomeomorph φ).symm.surjective.connectedSpace
    (semidirectProductHomeomorph φ).symm.continuous

variable [IsTopologicalGroup N] [IsTopologicalGroup D]

theorem semidirectProductTopologicalGroup
    (hφ : Continuous (fun p : D × N => φ p.1 p.2)) : IsTopologicalGroup (N ⋊[φ] D) where
  continuous_mul := by
    apply continuous_induced_rng.2
    exact ((continuous_semidirect_left φ).comp continuous_fst |>.mul
      (hφ.comp (((continuous_semidirect_right φ).comp continuous_fst).prodMk
        ((continuous_semidirect_left φ).comp continuous_snd)))).prodMk
      (((continuous_semidirect_right φ).comp continuous_fst).mul
        ((continuous_semidirect_right φ).comp continuous_snd))
  continuous_inv := by
    apply continuous_induced_rng.2
    exact (hφ.comp ((continuous_semidirect_right φ).inv.prodMk
      (continuous_semidirect_left φ).inv)).prodMk (continuous_semidirect_right φ).inv

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def semidirectProductLift (ι : N →* G) (κ : D →* G)
    (hc : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹) : (N ⋊[φ] D) →* G :=
  SemidirectProduct.lift ι κ (by intro d; ext n; exact hc d n)

omit [IsTopologicalGroup N] [IsTopologicalGroup D] in
theorem continuous_semidirect_lift (ι : N →* G) (κ : D →* G)
    (hι : Continuous ι) (hκ : Continuous κ)
    (hc : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹) :
    Continuous (semidirectProductLift φ ι κ hc) :=
  (hι.comp (continuous_semidirect_left φ)).mul (hκ.comp (continuous_semidirect_right φ))

end PolycyclicRecognition

end

end OAI
