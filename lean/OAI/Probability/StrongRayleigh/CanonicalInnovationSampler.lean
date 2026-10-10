import OAI.Probability.StrongRayleigh.InnovationSampler
import OAI.Probability.StrongRayleigh.ReferenceObservation

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal Topology

namespace Problem336AdditiveD139.PathRealization

local instance : MeasurableSpace Path := borel Path
local instance : BorelSpace Path := ⟨rfl⟩

def referencePaths {I : Type u_1} (ω : ReferenceObservation.Space I Path) : I → Path :=
  fun i => observationPath (boolReal (ω.1 i)) (ω.2 i)

theorem measurable_referencePaths {I : Type u_2} : Measurable (@referencePaths I) := by
  refine Measurable.of_eval (fun i => measurable_path_iff.mpr (fun t => ?_))
  exact ReferenceObservation.measurable_observation (fun (s : ℝ≥0) (w : Path) => w s)
    (fun s => (continuous_eval_const s).measurable) i t

@[simp] theorem referencePaths_apply {I : Type u_3}
    (ω : ReferenceObservation.Space I Path) (i : I) (t : ℝ≥0) :
    referencePaths ω i t = ReferenceObservation.observation (fun (s : ℝ≥0) (w : Path) => w s) i t ω := rfl

theorem factor_of_canonical_innovation_law
    {Γ : Type u_4} [Group Γ] [Countable Γ] [MeasurableSpace Γ]
    (μ : ProbabilityMeasure (Γ → Bool)) (ν : ProbabilityMeasure Path)
    (hν : IsPreBrownianReal (fun (t : ℝ≥0) (w : Path) => w t) (ν : Measure Path))
    {b : (ℝ≥0 × (Γ → ℝ)) → Γ → ℝ} (hb : Measurable b)
    (C : ℝ) (hbound : ∀ p i, |b p i| ≤ C)
    (hunit : ∀ p i, 0 ≤ b p i ∧ b p i ≤ 1)
    (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ t x y D, 0 ≤ D → (∀ i, |x i - y i| ≤ D) →
      ∀ i, |b (t, x) i - b (t, y) i| ≤ L * D)
    (hequiv : ∀ (g : Γ) t x i,
      b (t, leftTranslate g x) i = b (t, x) (g⁻¹ * i))
    (hinnovation : (ReferenceObservation.law μ ν).map
      (fun ω => innovation b hb C hbound (referencePaths ω)) =
        Measure.infinitePi (fun _ : Γ => (ν : Measure Path))) :
    HasEquivariantIIDFactor μ := by
  apply factor_of_brownian_reference_innovation (ReferenceObservation.law μ ν)
    (ν : Measure Path) μ hb C hbound hunit L hL hlip hequiv
    referencePaths measurable_referencePaths hinnovation
    Prod.fst (ReferenceObservation.signal_hasLaw μ ν).map_eq
    (fun ω i t => ω.2 i t)
  · intro ω i t
    rfl
  · exact ReferenceObservation.noise_isPreBrownian μ ν
      (fun (t : ℝ≥0) (w : Path) => w t) hν

end Problem336AdditiveD139.PathRealization

end

end OAI
