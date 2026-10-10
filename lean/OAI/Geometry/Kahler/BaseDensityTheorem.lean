import OAI.Geometry.Kahler.BaseDensityThreshold

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open scoped ContDiff
open Set Filter Topology
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

theorem uniform_representing_densities {a : ℝ} (p : RadialProfiles a) :
    ∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∀ D : ℝ, 2*Real.sqrt (2*p.R) < D →
    ∀ kmin : ℕ, ∃ Q₀ : ℕ, ∀ Q : ℕ, Q₀ ≤ Q →
    2 ≤ Q ∧ kmin ≤ Q ∧ ∀ P : ℕ → Finset Sphere,
      (∀ j, ProjectivelySeparated (D/Real.sqrt (Q^(j+1):ℕ)) (P (Q^(j+1)))) →
      ∀ j, ContDiff ℝ ∞ (density Q p.R p.f p.b P j) ∧
        DensityStage (density Q p.R p.f p.b P) Q c K j ∧
        PhaseBandwidth (density Q p.R p.f p.b P j) (densityBandwidth Q j) ∧
        OrbitMeanOne (density Q p.R p.f p.b P j) ∧
        IsProbabilityMeasure (densityMeasure (density Q p.R p.f p.b P j)) ∧
        Represents (densityMeasure (density Q p.R p.f p.b P j)) := by
  obtain ⟨B,F₁,B₁,hB,hF₁,hB₁,hbv,hfd,hbd⟩ := p.bounds
  obtain ⟨c,K,N,hc,hc1,hK,hN,hgap,hder⟩ := exists_density_constants p hB hF₁ hB₁
  refine ⟨c,K,hc,hK,?_⟩
  intro D hD kmin
  have hev := density_conditions_eventually (C₁ := 2*(Real.exp K*(2/c))*4^N*Real.exp 2)
    (R := p.R) (B := B) (D := 1+2*Real.sqrt (2*p.R)) hgap hder
  have hnat := tendsto_natCast_atTop_atTop.eventually hev
  obtain ⟨Q₁,hQ₁⟩ := eventually_atTop.mp hnat
  obtain ⟨Q₂,hQ₂⟩ := exists_nat_ge (2*p.R)
  refine ⟨max (max Q₁ Q₂) (max 2 kmin),?_⟩
  intro Q hQ
  have hQ1 : Q₁ ≤ Q := (le_max_left _ _).trans ((le_max_left _ _).trans hQ)
  have hQ2 : Q₂ ≤ Q := (le_max_right _ _).trans ((le_max_left _ _).trans hQ)
  have hQn : 2 ≤ Q := (le_max_left _ _).trans ((le_max_right _ _).trans hQ)
  have hQk : kmin ≤ Q := (le_max_right _ _).trans ((le_max_right _ _).trans hQ)
  have hQR : 2*p.R ≤ Q := hQ₂.trans (by exact_mod_cast hQ2)
  obtain ⟨hH,hsmall,hphase,hsecond,hderH,hderT⟩ := hQ₁ Q hQ1
  refine ⟨hQn,hQk,?_⟩
  intro P hP j
  have hq : 0 < Q := by omega
  have hdis : ∀ i, (P (Q^(i+1)):Set Sphere).PairwiseDisjoint (peakPatch (Q^(i+1)) p.R) :=
    fun i => peakPatch_disjoint (pow_pos hq _) p.R_pos hD (hP i)
  have hstage := density_induction hQn p.R_pos p.cutoff_lt hQR p.F_nonneg hB hF₁ hB₁
    (by nlinarith [Real.sqrt_nonneg (2*p.R)] : 1 ≤ 1+2*Real.sqrt (2*p.R)) (by linarith : 2*Real.sqrt (2*p.R) ≤ 1+2*Real.sqrt (2*p.R))
    hc hc1 hK.le hN p.smooth_f p.smooth_b p.tail p.small hbv hfd hbd P hdis
    hH hsmall hphase hsecond hderH hderT j
  have hsm := density_smooth hq p.cutoff_lt p.smooth_f p.smooth_b p.tail P j
  refine ⟨hsm,hstage,density_bandwidth hq p.cutoff_lt p.smooth_f p.smooth_b p.tail P j,
    density_orbit_mean hQn p.cutoff_lt p.smooth_f p.smooth_b p.tail P j,?_,?_⟩
  · exact densityMeasure_probability hsm.continuous (fun ξ => (hstage.positive ξ).le)
      (density_mass_one hQn p.R_pos p.cutoff_lt p.smooth_f p.smooth_b p.ode p.b_zero p.tail P j)
  · exact densityMeasure_represents hsm.continuous (fun ξ => (hstage.positive ξ).le)
      (density_polynomial_moment hQn p.R_pos p.cutoff_lt p.smooth_f p.smooth_b p.ode p.b_zero p.tail P j)

end PinchedHartogs.BaseConstruction

end

end OAI
