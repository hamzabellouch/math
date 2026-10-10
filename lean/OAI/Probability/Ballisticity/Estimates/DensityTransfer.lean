import Mathlib
import OAI.Probability.Ballisticity.Walk.KernelSections
import OAI.Probability.Ballisticity.Estimates.TailProfile

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace TailDecorrelation

lemma controlled_ae {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (ρ : Measure X) {T : Ω → X} (hT : Measurable T)
    {g : X → ℝ} (hg : Measurable g)
    (hLaw : μ.map T = ρ.withDensity (fun x => ENNReal.ofReal (g x)))
    {p : X → Prop} (hp : ∀ᵐ x ∂ρ, g x ≠ 0 → p x) :
    ∀ᵐ ω ∂μ, p (T ω) := by
  have hp' : ∀ᵐ x ∂ρ.withDensity (fun x => ENNReal.ofReal (g x)), p x := by
    apply (ae_withDensity_iff hg.ennreal_ofReal).mpr
    filter_upwards [hp] with x hx hne
    exact hx (fun heq => hne (by simp [heq]))
  have hpres : MeasurePreserving T μ (ρ.withDensity (fun x => ENNReal.ofReal (g x))) := ⟨hT,hLaw⟩
  exact hpres.quasiMeasurePreserving.ae hp'

lemma controlled_integral {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (ρ : Measure X) {T : Ω → X} (hT : Measurable T)
    {g : X → ℝ} (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    (hLaw : μ.map T = ρ.withDensity (fun x => ENNReal.ofReal (g x)))
    {F : X → ℝ} (hi : Integrable (fun x => g x * F x) ρ) :
    Integrable (fun ω => F (T ω)) μ ∧
      (∫ ω, F (T ω) ∂μ) = ∫ x, g x * F x ∂ρ := by
  have htop : ∀ᵐ x ∂ρ, ENNReal.ofReal (g x) < ∞ := Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hFi : Integrable F (ρ.withDensity (fun x => ENNReal.ofReal (g x))) := by
    apply (integrable_withDensity_iff_integrable_smul' hg.ennreal_ofReal htop).mpr
    simpa only [ENNReal.toReal_ofReal (hg0 _), smul_eq_mul] using hi
  have hpres : MeasurePreserving T μ (ρ.withDensity (fun x => ENNReal.ofReal (g x))) := ⟨hT,hLaw⟩
  refine ⟨(hpres.integrable_comp hFi.aestronglyMeasurable).mpr hFi,?_⟩
  have hFm : AEStronglyMeasurable F (μ.map T) := hLaw ▸ hFi.aestronglyMeasurable
  rw [← integral_map hT.aemeasurable hFm, hLaw,
    integral_withDensity_eq_integral_toReal_smul hg.ennreal_ofReal htop]
  simp only [ENNReal.toReal_ofReal (hg0 _), smul_eq_mul]

end TailDecorrelation

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

theorem actual_profile_tail_decorrelation {d : ℕ}
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (hue : UniformElliptic ν)
    (e : Direction d) (f : Fin d) (hef : e.1 ≠ f)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ A : ℝ, 0 < A ∧
      (∀ᵐ ω ∂environmentLaw ν, ∀ x : Lattice d × Lattice d,
        dot (realPosition x.1) (realPosition (step e)) =
          dot (realPosition x.2) (realPosition (step e)) →
        ∀ t : ℕ, 0 < outwardKernelMass e (f,true) (t+1) x ω ∧
          -Real.log (outwardKernelMass e (f,true) (t+1) x ω) ≤
            2*A*Real.log ((t:ℝ)+2)+outwardCanonicalExcess e (f,true) A x ω) ∧
      ∃ M : ℝ, 0 ≤ M ∧
      ∀ (D : Type) [MeasurableSpace D] (δ : Measure D) [IsProbabilityMeasure δ]
        (w : Kernel D (HorizontalLayer e)) [IsFiniteKernel w],
        (∀ z x, 0 < (w z).real {x}) →
        ∀ (g : D × Environment d → ℝ),
          Measurable g → (∀ z, 0 ≤ g z) → Integrable g (δ.prod (environmentLaw ν)) →
          (∫ z, g z ∂δ.prod (environmentLaw ν)) = 1 →
          Integrable (fun z => TailDecorrelation.entropyPlus (g z)) (δ.prod (environmentLaw ν)) →
          ∃ (j : ℕ → D → ℤ) (hj : ∀ r, Measurable (j r)),
            (∀ z (r : ℕ) (k : ℤ),
              TailCuts.score (TailCuts.lower ((w z).map (fun x => x.1 f)))
                (TailCuts.upper ((w z).map (fun x => x.1 f))) (r:ℤ) k ≤
              TailCuts.score (TailCuts.lower ((w z).map (fun x => x.1 f)))
                (TailCuts.upper ((w z).map (fun x => x.1 f))) (r:ℤ) (j r z)) ∧
            let Z : ZeroHeightPair e → Environment d → ℝ :=
              fun p => outwardCanonicalExcess e (f,true) A p.1
            let κ := fun r : ℕ => profilePairKernel e f w (r:ℤ) (j r) (hj r)
            (∀ r, ∀ᵐ z ∂δ.prod (environmentLaw ν), g z ≠ 0 →
              Integrable (fun p => Z p z.2) (κ r z.1)) ∧
            (∀ r, Integrable (fun z => g z * (∫ p, Z p z.2 ∂κ r z.1))
              (δ.prod (environmentLaw ν))) ∧
            (∀ ε : ℝ, 0 < ε → ∀ᶠ r in atTop,
              (∫ z, g z * (∫ p, Z p z.2 ∂κ r z.1) ∂δ.prod (environmentLaw ν)) ≤ M + ε) ∧
            Filter.limsup (fun r => ∫ z, g z * (∫ p, Z p z.2 ∂κ r z.1)
              ∂δ.prod (environmentLaw ν)) atTop ≤ M := by
  classical
  obtain ⟨A,hA,hpoint,hba,hdec⟩ := actual_kernel_tail_decorrelation ν hue e (f,true) hef htrans
  let Z : ZeroHeightPair e → Environment d → ℝ :=
    fun p => outwardCanonicalExcess e (f,true) A p.1
  let M : ℝ := ⨆ p : ZeroHeightPair e, ∫ ω, Z p ω ∂environmentLaw ν
  let p0 : ZeroHeightPair e := ⟨(0,0), by simp [PairAtHeight, dot, realPosition]⟩
  have hM : 0 ≤ M :=
    (integral_nonneg fun ω => canonicalLogExcess_nonneg _ _ ω).trans (le_ciSup hba p0)
  refine ⟨A,hA,hpoint,M,hM,?_⟩
  intro D mD δ hδ w hw hfull g hgm hg0 hgi hg1 hgH
  obtain ⟨j,hj,hmax,hesc⟩ := TailSampling.measurable_profile_cuts w (fun x => x.1 f)
    (measurable_of_countable _) (horizontal_coordinate_surjective e f hef) hfull
  let κ := fun r : ℕ => profilePairKernel e f w (r:ℤ) (j r) (hj r)
  let : ∀ r, IsMarkovKernel (κ r) :=
    fun r => profilePairKernel_markov e f hef w hfull (r:ℤ) (j r) (hj r)
  refine ⟨j,hj,hmax,?_⟩
  apply hdec D δ g hgm hg0 hgi hg1 hgH κ j (fun r z => j r z+(r:ℤ))
  · exact Eventually.of_forall hesc
  · intro r
    exact Eventually.of_forall fun z =>
      profilePairKernel_supported e f hef w hfull (r:ℤ) (j r) (hj r) z

end DirectionalTransience

end

end OAI
