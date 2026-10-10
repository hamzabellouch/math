import OAI.Geometry.RCD.Harmonic.FirstOrderBarrierMass
import OAI.Geometry.RCD.Harmonic.FirstOrderGramDefectLimit

namespace OAI

/-! # A supporting halfspace forces a definite first-order Gram error -/

open Set Filter MeasureTheory Metric
open scoped InnerProductSpace NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.first_order_support_threshold {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n) :
    ∃ C : ℝ, 0<C ∧ ∀ (p : X) (r ε : ℝ), 0<r → -1≤K*(16*r)^2 → 0≤ε → ε≤1 →
      ∀ (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (v : X → Euclidean n),
        FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (16*r) ε u v →
        ∀ (a : Euclidean n), ‖a‖=1 →
          (∀ x∈ball p (r/48), |‖v x-v p‖/r-dist x p/r|≤1/4096) →
          (∀ x∈ball p (r/48), ⟪v x-v p,a⟫_ℝ≤r/4096) → 1≤C*ε := by
  have hn0 : (2:ℝ)≤n := by exact_mod_cast hn
  have hnne : (n:ℝ)≠0 := by linarith
  let α := 1/(262144*(n:ℝ))
  have hα : 0<α := by dsimp [α]; positivity
  have hα1 : α≤1 := by
    dsimp [α]
    apply (div_le_one (by positivity)).mpr
    linarith
  obtain ⟨D,hD,hvol⟩ := hX.rescaled_ball_volume_factor hn (by norm_num : (0:ℝ)≤1) hα hα1
  let Q := (1/4096:ℝ)^2+(2*(n:ℝ)+1/4096)*2*((n:ℝ)+1)*(2*(n:ℝ))
  have hQ : 0<Q := by dsimp [Q]; positivity
  let C := (2*4096^2)*Q*(n:ℝ)^2*D
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro p r ε hr hcurv hε hε1 u v hs a ha hmetric hsupport
  let μ := hausdorff n X
  let ρ := r/(16384*(n:ℝ))
  have hρ : 0<ρ := by dsimp [ρ]; positivity
  have hm : 0<μ.real (ball p ρ) := ENNReal.toReal_pos (hX.fullSupport p ρ hρ).ne'
    (hX.finiteOnBounded _ isBounded_ball).ne
  have hv : μ.real (ball p (16*r))≤D*μ.real (ball p ρ) := by
    have hh := hvol p (16*r) (by positivity) hcurv p (by simp; positivity)
    have he : α*(16*r)=ρ := by dsimp [α,ρ]; field_simp; ring
    simpa only [he] using hh
  have hi : (∫ x in ball p (r/48), gramDefect μ hX.quadratic u x ∂μ) ≤
      (n:ℝ)^2*ε*μ.real (ball p (16*r)) := by
    have hfin := (hX.finiteOnBounded (ball p (16*r)) isBounded_ball).ne
    have hib := gramDefect_integrableOn μ hX.quadratic u hfin
    apply (setIntegral_mono_set hib (Eventually.of_forall (gramDefect_nonneg μ hX.quadratic u))
      (Eventually.of_forall (ball_subset_ball (by linarith : r/48≤16*r)))).trans
    exact gramDefect_integral_bound μ hX.quadratic
      (ENNReal.toReal_pos (hX.fullSupport p _ (by positivity)).ne' hfin) hfin hs
  have hb := hX.first_order_barrier_mass hn hr hε hε1 u v hs a ha hmetric hsupport
  have hcoef : (r/4096)^2+(2*(n:ℝ)*r+r/4096)*2*((n:ℝ)+1)*(2*(n:ℝ)*r)=Q*r^2 := by
    dsimp [Q]
    ring
  rw [hcoef] at hb
  have hb' : ((r/4096)^2/2)*μ.real (ball p ρ)≤
      (Q*r^2*((n:ℝ)^2*ε)*D)*μ.real (ball p ρ) := by
    calc
      _≤Q*r^2*(∫ x in ball p (r/48), gramDefect μ hX.quadratic u x ∂μ) := hb
      _≤Q*r^2*((n:ℝ)^2*ε*μ.real (ball p (16*r))) :=
        mul_le_mul_of_nonneg_left hi (by positivity)
      _≤Q*r^2*((n:ℝ)^2*ε*(D*μ.real (ball p ρ))) := by gcongr
      _=_ := by ring
  have hb'' := (mul_le_mul_iff_of_pos_right hm).mp hb'
  have hr2 : 0<r^2 := sq_pos_of_pos hr
  have hratio : (1:ℝ)/(2*4096^2)≤Q*(n:ℝ)^2*D*ε := by
    apply (mul_le_mul_iff_of_pos_right hr2).mp
    convert hb'' using 1 <;> ring
  dsimp [C]
  nlinarith

end RegularPointCoordinates

end

end OAI
