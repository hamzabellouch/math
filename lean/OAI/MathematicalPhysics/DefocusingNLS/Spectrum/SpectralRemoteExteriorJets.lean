import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteExteriorGrowth

namespace OAI

/-! Uniform exterior jets above a fixed order-dependent radius, before
restricting to any chosen sequence of remote endpoints. -/

open Set Filter Topology Polynomial
open scoped ContDiff
namespace DefocusingNLS

theorem spectralRemote_exterior_eventual_jets
    (nu a : ℕ → ℂ) (nu0 a0 : ℂ) (hnu : Tendsto nu atTop (𝓝 nu0))
    (ha : Tendsto a atTop (𝓝 a0)) (delta L : ℝ) (hd : 0 < delta)
    (ha0 : ‖a0‖+2*delta < 1)
    (hX : ∀ᶠ n in atTop, HasRadialExterior (nu n) n (a n) L) :
    ∀ k : ℕ, ∃ B T : ℝ, 0 ≤ B ∧ ∀ᶠ n in atTop, ∀ t, T ≤ t →
      ‖iteratedDeriv k (fun s => (radialExteriorCanonical (nu n) n (a n) L s).1) t‖ ≤ B := by
  let F := fun n t => (radialExteriorCanonical (nu n) n (a n) L t).1
  let P := fun n j => radialExteriorPolynomialFunction (radialExteriorExpansion (nu n) n (a n) j)
  have hF : ∀ᶠ n in atTop, ContDiffOn ℝ ∞ (F n) (Ioi L) := by
    filter_upwards [hX] with n hn
    exact radialExteriorODE_position_contDiffOn _ _ _ L
      (fun t ht => ((radialExteriorCanonical_spec hn).2.2 t ht.le).2)
  have hP : ∀ n j, ContDiff ℝ ∞ (P n j) := fun _ _ => radialPolynomialFunction_contDiff _
  have hp : ∀ j k : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ n in atTop,
      ∀ t, 0 ≤ t → ‖iteratedDeriv k (P n j) t‖ ≤ D := by
    intro j k
    exact spectralRemote_polynomial_jet_bound _ (radialFreeExpansion nu0 a0 j) j k
      (Eventually.of_forall (fun _ => radialExteriorExpansion_degree _ _ _ _))
      (radialFreeExpansion_degree _ _ _) (fun i _ =>
        radialExteriorExpansion_coefficient_limit nu a nu0 a0 hnu ha (by linarith) j i)
  intro k
  obtain ⟨j,_,A,T,hA,hb⟩ := spectralRemote_uniform_expansion_derivatives F P L hF hP
    (spectralRemote_exterior_uniform_growth nu a nu0 a0 hnu ha delta L hd ha0 hX)
    hp (spectralRemote_exterior_uniform_approximation nu a nu0 a0 hnu ha delta L hd ha0 hX)
    k 0 le_rfl 0
  obtain ⟨D,hD,hpD⟩ := hp j k
  refine ⟨A+D,max T (max L 0)+1,add_nonneg hA hD,?_⟩
  filter_upwards [hF,hb,hpD] with n hFn hbn hpn
  intro t ht
  have hTt : T ≤ t := (le_max_left T _).trans (by linarith)
  have hLt : L < t := lt_of_le_of_lt ((le_max_left L 0).trans (le_max_right T _)) (by linarith)
  have ht0 : 0 ≤ t := ((le_max_right L 0).trans (le_max_right T _)).trans (by linarith)
  have hf := ((hFn t hLt).contDiffAt (Ioi_mem_nhds hLt)).of_le (by simp : (k : ℕ∞ω) ≤ ∞)
  have hpol := (hP n j).contDiffAt (x := t) |>.of_le (by simp : (k : ℕ∞ω) ≤ ∞)
  have he : iteratedDeriv k (F n) t = iteratedDeriv k (fun s => F n s-P n j s) t+
      iteratedDeriv k (P n j) t := by
    rw [iteratedDeriv_fun_sub hf hpol]
    abel
  have hh := hbn t hTt
  simp only [neg_zero,zero_mul,Real.exp_zero,mul_one] at hh
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add hh (hpn t ht0))

end DefocusingNLS

end OAI
