import OAI.Probability.GammaPassage.UniformShapeGeometry
import OAI.Probability.GammaPassage.ActualTimeConstant
import OAI.Probability.GammaPassage.SpatialModulus

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP Real Filter Set
open GammaFPP.RealDirectionBridge GammaFPP.UniformShapeBridge
open scoped Topology

namespace UniformShapeBridge
/-- Deterministic upgrade of a coefficient-A spatial bound. -/
theorem rescaledPassage_modulus (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (A : ℝ) (hA : 0 < A)
    (hc : ∀ k : ℕ, ∀ᶠ n : ℕ in atTop, ∀ p ∈ latticeBox n, ∀ q ∈ latticeBox n,
      passageTime w p q < A*(latticeDistance p q : ℝ)+(1/(k+1 : ℝ))*n) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ v u, ‖v‖ ≤ 2 → ‖u‖ ≤ 2 →
      |rescaledPassage w n v-rescaledPassage w n u| ≤ (2*A)*‖v-u‖+ε := by
  intro ε hε
  obtain ⟨k,hk⟩ := exists_nat_one_div_lt (show 0 < ε/6 by linarith)
  have hthree : Tendsto (fun n : ℕ => 3*n) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    omega
  have hlarge : ∀ᶠ n : ℕ in atTop, 16*A/ε < (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (16*A/ε))
  filter_upwards [hthree.eventually (hc k), eventually_ge_atTop 1, hlarge]
    with n hn hn1 hnlarge
  intro v u hv hu
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hscale : 16*A < (n : ℝ)*ε := (div_lt_iff₀ hε).mp hnlarge
  have hconn := hn (latticeFloor ((n : ℝ) • v)) (latticeFloor_mem_box hv hn1)
    (latticeFloor ((n : ℝ) • u)) (latticeFloor_mem_box hu hn1)
  have hd := latticeDistance_floor_le v u n
  rw [norm_sub_rev] at hd
  have had := mul_le_mul_of_nonneg_left hd hA.le
  have hdiff := passageTime_origin_difference_le w hw (latticeFloor ((n : ℝ) • v))
    (latticeFloor ((n : ℝ) • u))
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hconn
  unfold rescaledPassage
  rw [← sub_div, abs_div, abs_of_pos hnpos]
  apply (div_le_iff₀ hnpos).mpr
  have hk' := mul_lt_mul_of_pos_right hk hnpos
  nlinarith
end UniformShapeBridge

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- Countable tolerances only; the endpoint pair may be chosen adaptively on
the resulting event. The spatial coefficient is the actual Gamma allowance. -/
theorem GammaEnvironment.ae_rescaledPassage_modulus
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate) :
    ∀ᵐ ω ∂P, ∀ ε > 0, ∀ᶠ n in atTop, ∀ v u, ‖v‖ ≤ 2 → ‖u‖ ≤ 2 →
      |rescaledPassage (fun e => τ e ω) n v-rescaledPassage (fun e => τ e ω) n u| ≤
        (2*coordinateAllowance shape rate)*‖v-u‖+ε := by
  have hc : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ᶠ n : ℕ in atTop,
      ∀ p ∈ latticeBox n, ∀ q ∈ latticeBox n,
      passageTime (fun e => τ e ω) p q < coordinateAllowance shape rate*
        (latticeDistance p q : ℝ)+(1/(k+1 : ℝ))*n := by
    rw [ae_all_iff]
    intro k
    exact h.ae_eventually_passageTime_connections hs hr (by positivity)
  filter_upwards [h.ae_positive_edges, hc] with ω hp hm
  exact UniformShapeBridge.rescaledPassage_modulus _ (fun e => (hp e).le)
    (coordinateAllowance shape rate) (coordinateAllowance_pos hs hr) hm

/-- Uniform convergence on the closed Euclidean unit ball for the actual
constructed Gamma mean norm. There is no arbitrary norm/shape premise. -/
theorem GammaEnvironment.ae_uniform_rescaledPassage
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate) :
    ∀ᵐ ω ∂P, ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ v, ‖v‖ ≤ 1 →
      |rescaledPassage (fun e => τ e ω) n v-gammaMeanNorm h hs hr v| < ε := by
  obtain ⟨u,hu⟩ := TopologicalSpace.exists_dense_seq Plane
  obtain ⟨B,hB,hBlip⟩ := timeConstantNorm_lipschitz_bound (gammaMeanNorm h hs hr)
    (gammaMeanNorm_laws h hs hr)
  have hp : ∀ᵐ ω ∂P, ∀ i : ℕ,
      Tendsto (fun n : ℕ => rescaledPassage (fun e => τ e ω) n (u i))
        atTop (𝓝 (gammaMeanNorm h hs hr (u i))) := by
    rw [ae_all_iff]
    intro i
    filter_upwards [h.isTimeConstant hs hr (u i)] with ω hω
    exact hω.comp tendsto_natCast_atTop_atTop
  filter_upwards [hp, h.ae_rescaledPassage_modulus hs hr] with ω hp hm
  exact uniform_on_unit_ball_of_dense_limits _ _ u hu
    (2*coordinateAllowance shape rate) B
    (by have := coordinateAllowance_pos hs hr; positivity) hB hBlip hp hm

/-- Exact origin-fixed, same-event all-lattice-endpoint uniform shape.
The embedding is the literal Euclidean coordinate embedding extracted in
RealDirectionBridge; adaptive endpoints are allowed after the AE quantifier. -/
theorem GammaEnvironment.uniform_shape
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate) :
    ∀ᵐ ω ∂P, UniformShapeBridge.UniformShape (fun e => τ e ω) (gammaMeanNorm h hs hr) := by
  filter_upwards [h.ae_uniform_rescaledPassage hs hr] with ω hω
  exact uniformShape_of_uniform_rescaled _ _ (gammaMeanNorm_laws h hs hr) hω

/-- Integer-scale inside-ball estimate, with all C and epsilon on one event. -/
theorem GammaEnvironment.ae_uniform_inside_ball
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate) :
    ∀ᵐ ω ∂P, ∀ C : ℕ, 0 < C → ∀ ε > 0,
      ∀ᶠ n : ℕ in atTop, ∀ z : Vertex, ‖latticeEmbed z‖ ≤ (C : ℝ)*n →
      |passageTime (fun e => τ e ω) 0 z-gammaMeanNorm h hs hr (latticeEmbed z)| ≤ ε*n := by
  filter_upwards [h.ae_uniform_rescaledPassage hs hr] with ω hω
  intro C hC ε hε
  exact uniform_rescaled_ball_bound _ _ (gammaMeanNorm_laws h hs hr) hω C hC ε hε

/-- Real-scale local-travel form, still origin-fixed and all endpoints on the
same AE event. No stationarity or simultaneous moving-origin assertion here. -/
theorem GammaEnvironment.ae_uniform_inside_ball_real
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate) :
    ∀ᵐ ω ∂P, ∀ C > 0, ∀ ε > 0,
      ∀ᶠ s : ℝ in atTop, ∀ z : Vertex, ‖latticeEmbed z‖ ≤ C*s →
      |passageTime (fun e => τ e ω) 0 z-gammaMeanNorm h hs hr (latticeEmbed z)| ≤ ε*s := by
  filter_upwards [h.ae_uniform_inside_ball hs hr] with ω hω
  intro C hC ε hε
  exact uniform_inside_ball_real_of_integer _ _ hω C hC ε hε

end GammaFPP

end OAI
