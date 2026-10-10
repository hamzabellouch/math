import OAI.Geometry.TranslativeCovering.BodySelection

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2

namespace AllLatticeExclusion
open Set Metric MeasureTheory SourceParameters LocalizationRates PatternEnumeration SourceLocalization
open scoped ENNReal Classical
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
lemma intensity_bound {n : ℕ} {I : Type u_1} [Fintype I] {F K : Set (Space n)}
    (hF0 : volume F≠0) (_hFtop : volume F≠∞) (_hKtop : volume K≠∞)
    {R : ℝ} (hR : 0≤R)
    (hvol : 2*v*volume.real (closedBall (0:Space n) a)<volume.real K)
    (hdensity : volume K*((Fintype.card I:ℝ≥0∞)/volume F)≤ENNReal.ofReal R) :
    ((Fintype.card I:ℝ≥0∞)/volume F)*volume (closedBall (0:Space n) a)≤ENNReal.ofReal (R/(2*v)) := by
  let ρ : ℝ≥0∞ := (Fintype.card I:ℝ≥0∞)/volume F
  have hρtop : ρ≠∞ := ENNReal.div_ne_top (by finiteness) hF0
  have hVtop : volume (closedBall (0:Space n) a)≠∞ := (isCompact_closedBall _ _).measure_ne_top
  have hv : 0<v := by norm_num [v]
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hdensity
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal hR] at hh
  have hp : ρ.toReal*volume.real (closedBall (0:Space n) a)≤R/(2*v) := by
    apply (le_div_iff₀ (by positivity : (0:ℝ)<2*v)).mpr
    have hmul := mul_le_mul_of_nonneg_right hvol.le (ENNReal.toReal_nonneg (a:=ρ))
    change (volume K).toReal*ρ.toReal≤R at hh
    dsimp [Measure.real] at hmul ⊢
    nlinarith only [hmul,hh]
  apply (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top hρtop hVtop) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (div_nonneg hR (by positivity))]
  exact hp

theorem no_cover {n : ℕ} [NeZero n] {R : ℝ} (hR : 1≤R) (hRn : R≤(n:ℝ)^2)
    (hn : 1≤n) (hr : 0<rminus n) (hβ : 0<β n) (houter : (β n/a)^n≤3)
    (hinner : (n:ℝ)^2/(2*v)*(rminus n/a)^n≤1/200)
    (hlip : (2*(n:ℝ)/a)*(Real.sqrt n*h n/2)≤1)
    (U : PoissonConfig.Config (SphericalLaw.Sphere n))
    (hvol : 2*v*volume.real (closedBall (0:Space n) a)<volume.real (RandomBody.body (b n) 1 U))
    (hbad : U ∉ BodySelection.bad R)
    {I : Type u_2} [Fintype I] (Λ : Submodule ℤ (Space n)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (p : I → Space n) {F : Set (Space n)}
    (hF : IsAddFundamentalDomain Λ F volume) (hF0 : volume F≠0) (hFtop : volume F≠∞)
    (hdensity : volume (RandomBody.body (b n) 1 U)*((Fintype.card I:ℝ≥0∞)/volume F)≤ENNReal.ofReal R) :
    ¬ (∀ y,∃ (i:I) (l:Λ), y-p i-l.val ∈ RandomBody.body (b n) 1 U) := by
  intro hc
  have hρ := intensity_bound hF0 hFtop (RandomBody.body_compact _ _ _).measure_ne_top (by linarith only [hR]) hvol hdensity
  obtain ⟨P,hP⟩ := SourceLocalization.localize Λ p hF hF0 hFtop hR hRn hn hr hβ houter hinner hlip hρ U hc
  exact hbad (Set.mem_iUnion.mpr ⟨P,hP⟩)
end AllLatticeExclusion

end OAI
