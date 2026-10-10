import Mathlib
import OAI.Analysis.Commutator.CentralCorner
import OAI.Analysis.Commutator.CyclicGelfandModel
import OAI.Analysis.Commutator.FaithfulNormalStateProducer
import OAI.Analysis.Commutator.NormalGNSSeparable

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open MeasureTheory

open scoped Topology ComplexOrder

namespace Kadison.CentralSpectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H)

instance centerCommCStar : CommCStarAlgebra (CentralCorner.center M) where
  mul_comm a b := Subtype.ext (((CentralCorner.mem_center M a).mp a.property).2 b
    (((CentralCorner.mem_center M b).mp b.property).1)).symm

abbrev Spectrum := WeakDual.characterSpace ℂ (CentralCorner.center M)

instance spectrumMeasurable : MeasurableSpace (Spectrum M) := borel (Spectrum M)

instance spectrumBorel : BorelSpace (Spectrum M) := ⟨rfl⟩

theorem exists_center_gns_model [TopologicalSpace.SeparableSpace H] :
    ∃ τ : (CentralCorner.center M) →ₚ[ℂ] ℂ,
      NormalGNS.BoundedWOTContinuous (CentralCorner.center M) τ ∧
      (∀ a,τ (star a*a)=0 → a=0) ∧
      ∃ μ : Measure (Spectrum M), IsFiniteMeasure μ ∧
        ∃ U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] τ.GNS,
          (∀ (a : CentralCorner.center M) (v : Lp ℂ 2 μ),
            U (CyclicSpectral.scalarMultiplier μ (gelfandStarTransform _ a) v)=
              τ.gnsStarAlgHom a (U v)) ∧
          TopologicalSpace.SeparableSpace (Lp ℂ 2 μ) := by
  classical
  let hτ := exists_faithful_normal_positive (H := H) (CentralCorner.center M)
  let τ := hτ.choose
  have hn := hτ.choose_spec.1
  have hf := hτ.choose_spec.2
  let hmodel := CyclicSpectral.exists_gelfand_model
    (A := CentralCorner.center M) (H := τ.GNS)
    (by exact τ.gnsStarAlgHom) (by exact TracialGNS.vacuum τ)
    (by exact TracialGNS.dense_cyclic_orbit τ)
  let μ := hmodel.choose
  have hμ := hmodel.choose_spec.1
  let U := hmodel.choose_spec.2.choose
  have hU := hmodel.choose_spec.2.choose_spec
  let : TopologicalSpace.SeparableSpace τ.GNS := NormalGNS.separable_gns _ τ hn
  exact ⟨τ,hn,hf,μ,hμ,U,hU,U.isometry.isEmbedding.separableSpace⟩

end Kadison.CentralSpectral

end

end OAI
