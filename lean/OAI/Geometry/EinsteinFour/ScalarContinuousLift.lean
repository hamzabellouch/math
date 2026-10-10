import OAI.Geometry.EinsteinFour.ScalarBoundedPairing

namespace OAI

/-! A local H3-valued bounded operator has a bounded continuous-function lift.
The norm bound follows from the closed graph theorem and actual test pairings. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (A : E →L[ℝ] Lp ℂ 2 (volume : Measure V))
  (hA : ∀ f, MemSobolev 3 2 (A f : 𝓢'(V, ℂ)))

def scalarH3Representative (f : E) : V →ᵇ ℂ :=
  (scalar_L2_H3_boundedContinuous_representative (A f) (hA f)).choose

theorem scalarH3Representative_ae (f : E) :
    (A f : V → ℂ) =ᵐ[volume] scalarH3Representative A hA f :=
  (scalar_L2_H3_boundedContinuous_representative (A f) (hA f)).choose_spec

theorem scalarH3Representative_eq (f : E) (g : V →ᵇ ℂ)
    (hg : (A f : V → ℂ) =ᵐ[volume] g) : scalarH3Representative A hA f = g := by
  apply DFunLike.coe_injective
  exact MeasureTheory.Measure.eq_of_ae_eq ((scalarH3Representative_ae A hA f).symm.trans hg)
    (scalarH3Representative A hA f).continuous g.continuous

def scalarH3RepresentativeLinear : E →ₗ[ℝ] (V →ᵇ ℂ) where
  toFun := scalarH3Representative A hA
  map_add' f g := by
    apply scalarH3Representative_eq
    rw [map_add]
    filter_upwards [Lp.coeFn_add (A f) (A g), scalarH3Representative_ae A hA f,
      scalarH3Representative_ae A hA g] with x hadd hf hg
    simp only [hadd, hf, hg, BoundedContinuousFunction.coe_add, Pi.add_apply]
  map_smul' c f := by
    apply scalarH3Representative_eq
    rw [map_smul]
    filter_upwards [Lp.coeFn_smul c (A f), scalarH3Representative_ae A hA f] with x hsm hf
    simp only [hsm, hf, BoundedContinuousFunction.coe_smul, Pi.smul_apply, RingHom.id_apply]

theorem scalarH3Representative_pairing (f : E) (φ : 𝓢(V, ℂ)) :
    (A f : 𝓢'(V, ℂ)) φ = scalarBoundedTestPairing φ (scalarH3Representative A hA f) := by
  rw [Lp.toTemperedDistribution_apply, scalarBoundedTestPairing_apply]
  apply integral_congr_ae
  filter_upwards [scalarH3Representative_ae A hA f] with x hx
  rw [hx, smul_eq_mul]

theorem scalarH3Representative_graph_closed :
    IsClosed ((scalarH3RepresentativeLinear A hA).graph : Set (E × (V →ᵇ ℂ))) := by
  have heq : ((scalarH3RepresentativeLinear A hA).graph : Set (E × (V →ᵇ ℂ))) =
      ⋂ φ : 𝓢(V, ℂ), {p | (A p.1 : 𝓢'(V, ℂ)) φ = scalarBoundedTestPairing φ p.2} := by
    ext p
    rcases p with ⟨f, g⟩
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    change g = scalarH3Representative A hA f ↔
      ∀ φ : 𝓢(V, ℂ), (A f : 𝓢'(V, ℂ)) φ = scalarBoundedTestPairing φ g
    constructor
    · intro hg φ
      rw [hg]
      exact scalarH3Representative_pairing A hA f φ
    · intro h
      exact (scalarH3Representative_eq A hA f g (scalar_L2_eq_bounded_of_tests (A f) g h)).symm
  rw [heq]
  apply isClosed_iInter
  intro φ
  apply isClosed_eq _ ((scalarBoundedTestPairing φ).continuous.comp continuous_snd)
  exact ((PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ φ).continuous.comp
    ((Lp.toTemperedDistributionCLM ℂ volume 2).continuous.comp A.continuous)).comp continuous_fst

variable [CompleteSpace E]

def scalarH3ContinuousLift : E →L[ℝ] (V →ᵇ ℂ) :=
  ContinuousLinearMap.ofIsClosedGraph (scalarH3Representative_graph_closed A hA)

theorem scalarH3ContinuousLift_ae (f : E) :
    (A f : V → ℂ) =ᵐ[volume] scalarH3ContinuousLift A hA f :=
  scalarH3Representative_ae A hA f

end
end PositiveEinsteinFour.Geometry

end OAI
