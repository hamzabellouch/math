import Mathlib.Analysis.Complex.LocallyUniformLimit
import OAI.AlgebraicGeometry.PlaneCurves.AnalyticFactorization
import OAI.AlgebraicGeometry.PlaneCurves.CollisionBounds

namespace OAI

/-!
# Fixed-curve holomorphic collision bounds
-/

section

namespace Nagata.W20

open Filter Metric
open scoped Topology BigOperators

/-- A quantitative holomorphic collision theorem. The total vanishing order
is k times the number of centers, with no convergence assumption on quotients. -/
theorem order_collision_of_holomorphic_factorization {ι : Type*} [Fintype ι]
    (ξ : ℕ → ι → ℂ) (k : ℕ) (H G : ℕ → ℂ → ℂ) (f : ℂ → ℂ)
    {r M : ℝ} (hr : 0 < r)
    (hξlim : ∀ i, Tendsto (fun n => ξ n i) atTop (𝓝 0))
    (hξbound : ∀ᶠ n in atTop, ∀ i, ‖ξ n i‖ ≤ r / 2)
    (hf : DifferentiableOn ℂ f (ball 0 r))
    (hlim : ∀ z ∈ ball (0 : ℂ) r, Tendsto (fun n => H n z) atTop (𝓝 (f z)))
    (hG : ∀ n, DiffContOnCl ℂ (G n) (ball 0 r))
    (hfactor : ∀ n, ∀ z ∈ closedBall (0 : ℂ) r,
      H n z = (∏ i, (z - ξ n i) ^ k) * G n z)
    (hupper : ∀ᶠ n in atTop, ∀ z ∈ sphere (0 : ℂ) r, ‖H n z‖ ≤ M) :
    (↑(k * Fintype.card ι) : ℕ∞) ≤ analyticOrderAt f 0 := by
  classical
  let a := (r / 2) ^ (k * Fintype.card ι)
  have ha : 0 < a := pow_pos (by positivity) _
  apply analyticOrderAt_lower_of_growth f (k * Fintype.card ι) hr hf
  intro z hz
  apply collision_limit_growth_eventually ξ k hξlim H G f z (M / a) (hlim z hz)
  · intro n
    exact hfactor n z (ball_subset_closedBall hz)
  · filter_upwards [hξbound, hupper] with n hξn hn
    apply quotient_bound_on_closedBall (H n) (fun w => ∏ i, (w - ξ n i) ^ k)
      (G n) hr ha (hG n)
    · intro w hw
      exact hfactor n w (sphere_subset_closedBall hw)
    · intro w hw
      apply collision_product_boundary_lower (ξ n) k hr hξn
      simpa only [Metric.mem_sphere, dist_zero_right] using hw
    · exact hn
    · exact ball_subset_closedBall hz

/-- Collision on an actual open complex domain. Locally uniform convergence
supplies holomorphicity of the limit and the required uniform boundary bound;
only the genuine holomorphic factorizations remain as explicit inputs. -/
theorem collision_of_locally_uniform_limit_and_factorizations
    {ι : Type*} [Fintype ι] {U : Set ℂ} (hU : IsOpen U)
    (ξ : ℕ → ι → ℂ) (k : ℕ) (H G : ℕ → ℂ → ℂ) (f : ℂ → ℂ)
    {r : ℝ} (hr : 0 < r) (hsub : closedBall (0 : ℂ) r ⊆ U)
    (hξlim : ∀ i, Tendsto (fun n => ξ n i) atTop (𝓝 0))
    (hH : ∀ n, DifferentiableOn ℂ (H n) U)
    (hlim : TendstoLocallyUniformlyOn H f atTop U)
    (hG : ∀ n, DifferentiableOn ℂ (G n) U)
    (hfactor : ∀ n, ∀ z ∈ U, H n z = (∏ i, (z - ξ n i) ^ k) * G n z) :
    (↑(k * Fintype.card ι) : ℕ∞) ≤ analyticOrderAt f 0 := by
  have hf : DifferentiableOn ℂ f U :=
    hlim.differentiableOn (Filter.Eventually.of_forall hH) hU
  have hsphere : sphere (0 : ℂ) r ⊆ U := sphere_subset_closedBall.trans hsub
  have hconv := (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hlim
    (sphere (0 : ℂ) r) hsphere (isCompact_sphere _ _)
  obtain ⟨M, hM⟩ := eventual_uniform_bound_on_compact (sphere (0 : ℂ) r)
    (isCompact_sphere _ _) H f (hf.continuousOn.mono hsphere) hconv
  apply order_collision_of_holomorphic_factorization ξ k H G f hr hξlim
    (centers_eventually_half_disk ξ hξlim hr)
    (hf.mono (ball_subset_closedBall.trans hsub))
  · intro z hz
    exact hlim.tendsto_at (hsub (ball_subset_closedBall hz))
  · intro n
    exact (hG n).diffContOnCl_ball hsub
  · intro n z hz
    exact hfactor n z (hsub hz)
  · exact hM

end Nagata.W20

end

section

/-! The analytic moving-center collision theorem for genuine holomorphic
functions. Its proof constructs the quotients, bounds them by maximum modulus,
and uses removable singularities for the limiting vanishing order. -/

namespace Nagata.W20

open Filter Metric
open scoped Topology BigOperators

/-- Colliding q distinct zeros of order at least k produces a zero of order
at least q*k in the locally uniform holomorphic limit. -/
theorem holomorphic_collision_order {q : ℕ} {U : Set ℂ}
    (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U)
    (ξ : ℕ → Fin q → ℂ) (k : ℕ) (H : ℕ → ℂ → ℂ) (f : ℂ → ℂ)
    (hξlim : ∀ i, Tendsto (fun n => ξ n i) atTop (𝓝 0))
    (hξinj : ∀ n, Function.Injective (ξ n))
    (hξmem : ∀ n i, ξ n i ∈ U)
    (hH : ∀ n, DifferentiableOn ℂ (H n) U)
    (hlim : TendstoLocallyUniformlyOn H f atTop U)
    (horder : ∀ n i, (k : ℕ∞) ≤ analyticOrderAt (H n) (ξ n i)) :
    (↑(q * k) : ℕ∞) ≤ analyticOrderAt f 0 := by
  classical
  have hex := fun n => Nagata.W19.exists_holomorphic_factorization hU (H n)
    (hH n) (ξ n) (hξinj n) (hξmem n) k (horder n)
  let G : ℕ → ℂ → ℂ := fun n => Classical.choose (hex n)
  have hG : ∀ n, DifferentiableOn ℂ (G n) U :=
    fun n => (Classical.choose_spec (hex n)).1
  have hfactor : ∀ n, ∀ z ∈ U, H n z = (∏ i, (z - ξ n i) ^ k) * G n z :=
    fun n z _ => (Classical.choose_spec (hex n)).2 z
  obtain ⟨r, hr, hsub⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds h0)
  have hresult := collision_of_locally_uniform_limit_and_factorizations hU ξ k H G f
    hr hsub hξlim hH hlim hG hfactor
  simpa only [Fintype.card_fin, Nat.mul_comm] using hresult

/-- Derivative form of the collision theorem, matching the row conditions
of the manuscript's fixed-surface jet map. -/
theorem holomorphic_collision_jets {q : ℕ} {U : Set ℂ}
    (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U)
    (ξ : ℕ → Fin q → ℂ) (k : ℕ) (H : ℕ → ℂ → ℂ) (f : ℂ → ℂ)
    (hξlim : ∀ i, Tendsto (fun n => ξ n i) atTop (𝓝 0))
    (hξinj : ∀ n, Function.Injective (ξ n))
    (hξmem : ∀ n i, ξ n i ∈ U)
    (hH : ∀ n, DifferentiableOn ℂ (H n) U)
    (hlim : TendstoLocallyUniformlyOn H f atTop U)
    (horder : ∀ n i, (k : ℕ∞) ≤ analyticOrderAt (H n) (ξ n i)) :
    ∀ ℓ < q * k, iteratedDeriv ℓ f 0 = 0 := by
  have hf := hlim.differentiableOn (Filter.Eventually.of_forall hH) hU
  apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
    (hf.analyticAt (hU.mem_nhds h0))).mp
  exact holomorphic_collision_order hU h0 ξ k H f hξlim hξinj hξmem hH hlim horder

end Nagata.W20

end

end OAI
