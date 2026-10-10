import OAI.Probability.SpanningForest.FiniteUSTRelabel
import OAI.Probability.SpanningForest.FUSFLawUnique

namespace OAI

noncomputable section
open MeasureTheory

namespace Problem336

def configurationRelabel (σ : Equiv ℕ ℕ) : EdgeConfiguration ≃ᵐ EdgeConfiguration :=
  MeasurableEquiv.arrowCongr' (edgeEquiv σ) (MeasurableEquiv.refl Bool)

@[simp] theorem configurationRelabel_apply (σ : Equiv ℕ ℕ)
    (x : EdgeConfiguration) (e : EdgeCode) :
    configurationRelabel σ x e = x (mapEdge σ.symm e) := rfl

@[simp] theorem configurationRelabel_symm_apply (σ : Equiv ℕ ℕ)
    (x : EdgeConfiguration) :
    configurationRelabel σ.symm (configurationRelabel σ x) = x := by
  funext e
  simp

theorem configurationRelabel_preimage_cylinder (σ : Equiv ℕ ℕ)
    (A B : Finset EdgeCode) :
    configurationRelabel σ ⁻¹' configurationCylinder A B =
      configurationCylinder (A.image (mapEdge σ.symm)) (B.image (mapEdge σ.symm)) := by
  ext x
  simp only [configurationCylinder, Set.mem_preimage, Set.mem_ofPred_eq,
    configurationRelabel_apply, Finset.forall_mem_image]

theorem HasFUSFLaw.map_configurationRelabel
    {G : GraphCode} {μ ν : Measure EdgeConfiguration} [IsFiniteMeasure μ]
    (hμ : HasFUSFLaw G μ id) (σ : Equiv ℕ ℕ)
    (hν : HasFUSFLaw (relabelGraph σ G) ν id)
    {H : ℕ → FiniteSubgraphCode} (hH : IsConnectedExhaustion G H) :
    μ.map (configurationRelabel σ) = ν := by
  have h := (hμ.relabel σ).map_eq hν (hH.relabel σ)
  have hf : (fun x : EdgeConfiguration => fun e => x (mapEdge σ.symm e)) =
      (configurationRelabel σ : EdgeConfiguration → EdgeConfiguration) := by
    funext x e
    rfl
  simpa only [id_eq, hf, Measure.map_id] using h

theorem fusfMeasureFamily_relabel
    (μ : GraphCode → Measure EdgeConfiguration)
    (hfinite : ∀ G, IsFiniteMeasure (μ G))
    (hlaw : ∀ G, HasFUSFLaw G (μ G) id)
    {G : GraphCode} {H : ℕ → FiniteSubgraphCode}
    (hH : IsConnectedExhaustion G H) (σ : Equiv ℕ ℕ) :
    (μ G).map (configurationRelabel σ) = μ (relabelGraph σ G) := by
  let := hfinite G
  exact (hlaw G).map_configurationRelabel σ (hlaw (relabelGraph σ G)) hH

end Problem336

end

end OAI
