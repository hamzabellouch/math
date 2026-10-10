import OAI.Probability.InvariantIsing.Core.FinitePopulationCoupling

namespace OAI

/-! Continuity in positive field populations, with the same finite field
alphabet and a bound independent of all optimizing parameters. -/
noncomputable section
open Filter Set
open scoped BigOperators Topology
namespace InvariantIsing

theorem finiteMagneticFunctional_population_le {A ι : Type*}
    [Fintype A] [DecidableEq A] [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a=1)
    (γ δ b : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hδ : ∀ a, 0 < δ a)
    (hγsum : ∑ a, γ a=1) (hδsum : ∑ a, δ a=1)
    {ε D : ℝ} (hε : ε ≤ 1) (hdom : ∀ a, (1-ε)*γ a ≤ δ a) (hb : ∀ a, |b a| ≤ D) :
    (finiteMagneticFunctional (finiteR ρ eig hρ hsum) γ b).toReal ≤
      (finiteMagneticFunctional (finiteR ρ eig hρ hsum) δ b).toReal+2*D*ε := by
  have hh := finiteMagneticFunctional_transport_le ρ eig hρ hsum
    (retainedPopulationCoupling γ δ ε) γ b δ b
    (retainedPopulationCoupling_nonneg γ δ hε hγ hdom) hγ hδ hγsum hδsum
    (retainedPopulationCoupling_row γ δ hγsum hδsum ε)
    (retainedPopulationCoupling_col γ δ hγsum ε)
  exact hh.trans (add_le_add le_rfl (retainedPopulationCoupling_cost γ δ b hγ hγsum hδsum hdom hb))

theorem finiteMagneticFunctional_tendsto_populations {A ι : Type*}
    [Fintype A] [DecidableEq A] [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a=1)
    (γs : ℕ → A → ℝ) (γ b : A → ℝ)
    (hγs : ∀ k a, 0 < γs k a) (hγssum : ∀ k, ∑ a, γs k a=1)
    (hγ : ∀ a, 0 < γ a) (hγsum : ∑ a, γ a=1)
    (hlim : Tendsto γs atTop (𝓝 γ)) :
    Tendsto (fun k => (finiteMagneticFunctional (finiteR ρ eig hρ hsum) (γs k) b).toReal)
      atTop (𝓝 (finiteMagneticFunctional (finiteR ρ eig hρ hsum) γ b).toReal) := by
  classical
  let D := ∑ a, |b a|
  have hD : 0 ≤ D := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hb a : |b a|≤D := Finset.single_le_sum (f := fun a => |b a|) (fun _ _ => abs_nonneg _) (Finset.mem_univ a)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let t := min (1/2 : ℝ) (ε/(4*(D+1)))
  have ht : 0 < t := lt_min (by norm_num) (div_pos hε (by positivity))
  have ht1 : t ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hleft : ∀ᶠ k in atTop, ∀ a, (1-t)*γ a ≤ γs k a := by
    apply Filter.eventually_all.mpr
    intro a
    exact (((tendsto_pi_nhds.mp hlim) a).eventually
      (Ioi_mem_nhds (by nlinarith [hγ a]))).mono (fun _ h => h.le)
  have hright : ∀ᶠ k in atTop, ∀ a, (1-t)*γs k a ≤ γ a := by
    apply Filter.eventually_all.mpr
    intro a
    exact ((((tendsto_pi_nhds.mp hlim) a).const_mul (1-t)).eventually
      (Iio_mem_nhds (by nlinarith [hγ a]))).mono (fun _ h => h.le)
  have hsmall : 2*D*t<ε := by
    have hh : t*(4*(D+1))≤ε := (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    nlinarith
  filter_upwards [hleft,hright] with k hl hr
  have h1 := finiteMagneticFunctional_population_le ρ eig hρ hsum γ (γs k) b
    (fun a => (hγ a).le) (hγs k) hγsum (hγssum k) ht1 hl hb
  have h2 := finiteMagneticFunctional_population_le ρ eig hρ hsum (γs k) γ b
    (fun a => (hγs k a).le) hγ (hγssum k) hγsum ht1 hr hb
  rw [Real.dist_eq,abs_lt]
  constructor <;> linarith

end InvariantIsing

end

end OAI
