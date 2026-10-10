import OAI.Geometry.RCD.Heat.HeatHamiltonWeighted
import OAI.Geometry.RCD.Heat.HeatReversePoincare
import OAI.Geometry.RCD.Coordinates.RegularizedHamiltonIntegrability

namespace OAI

/-! # The regularized Hamilton bound almost everywhere

Finite-measure indicators test the actual entropy inequality. The bounded
regularized logarithm makes every such local integral finite, even when
the ambient measure is infinite.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2≤n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn p

omit hn p [SeparableSpace X] [IsLocallyFiniteMeasure (hausdorff n X)] in
private theorem heat_hamilton_regularized_integrableOn
    (f : Lp ℝ 2 (hausdorff n X)) (hf0 : 0≤f) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x|≤A)
    {T ε : ℝ} (hT : 0<T) (hε : 0<ε) :
    ∀ s : Set X, hausdorff n X s<∞ →
      IntegrableOn (fun x => T*Real.exp (-2*|K| * T)*localGamma (hausdorff n X) hX.quadratic
        (heatSobolev (hausdorff n X) hX.quadratic T hT f)
        (heatSobolev (hausdorff n X) hX.quadratic T hT f) x /
        (ε+heatAt (hausdorff n X) hX.quadratic T f x)) s (hausdorff n X) ∧
      IntegrableOn (fun x => (ε+heatAt (hausdorff n X) hX.quadratic T f x)*
        (Real.log (ε+A)-Real.log (ε+heatAt (hausdorff n X) hX.quadratic T f x))) s (hausdorff n X) := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  let u := heatSobolev μ Q T hT f
  let v := heatAt μ Q T f
  let c := T*Real.exp (-2*|K| * T)
  have hv : ∀ᵐ x ∂μ, v x∈Icc 0 (A:ℝ) := by
    filter_upwards [(Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ Q T f hf0),
      heatAt_abs_le_const μ Q T A f hf] with x hx hy
    exact ⟨hx,(le_abs_self _).trans hy⟩
  have hu : ∀ᵐ x ∂μ, 0≤SobolevSpace.toLp μ Q u x := by
    simpa only [u,heatSobolev_toLp] using hv.mono (fun _ hx => hx.1)
  have hFi := regularized_gamma_integrable μ Q u hε hu c
  intro s hs
  refine ⟨?_,shifted_log_gap_integrableOn μ v hε A hv hs⟩
  simpa only [u,heatSobolev_toLp] using hFi.integrableOn (s:=s)


theorem heat_hamilton_regularized
    (f : Lp ℝ 2 (hausdorff n X)) (hf0 : 0≤f) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x|≤A)
    {T ε : ℝ} (hT : 0<T) (hε : 0<ε) :
    ∀ᵐ x ∂hausdorff n X, T*Real.exp (-2*|K| * T)*
      localGamma (hausdorff n X) hX.quadratic
        (heatSobolev (hausdorff n X) hX.quadratic T hT f)
        (heatSobolev (hausdorff n X) hX.quadratic T hT f) x ≤
      (ε+heatAt (hausdorff n X) hX.quadratic T f x)^2*
        (Real.log (ε+A)-Real.log (ε+heatAt (hausdorff n X) hX.quadratic T f x)) := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  let u := heatSobolev μ Q T hT f
  let v := heatAt μ Q T f
  let c := T*Real.exp (-2*|K| * T)
  let F := fun x => c*localGamma μ Q u u x/(ε+v x)
  let R := fun x => (ε+v x)*(Real.log (ε+A)-Real.log (ε+v x))
  have hv : ∀ᵐ x ∂μ, v x∈Icc 0 (A:ℝ) := by
    filter_upwards [(Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ Q T f hf0),
      heatAt_abs_le_const μ Q T A f hf] with x hx hy
    exact ⟨hx,(le_abs_self _).trans hy⟩
  have hdata := hX.heat_hamilton_regularized_integrableOn f hf0 A hf hT hε
  have hFi (s : Set X) (hs : μ s<∞) : IntegrableOn F s μ := (hdata s hs).1
  have hRi (s : Set X) (hs : μ s<∞) : IntegrableOn R s μ := (hdata s hs).2
  have hp : 0≤ᵐ[μ] fun x => R x-F x := by
    apply ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite
    · intro s _ hs
      exact (hRi s hs).sub (hFi s hs)
    · intro s hs hfin
      let w : Lp ℝ 2 μ := indicatorConstLp 2 hs hfin.ne 1
      have hwr : w =ᵐ[μ] s.indicator (fun _ => (1:ℝ)) := indicatorConstLp_coeFn
      have hw0 : 0≤w := by
        apply (Lp.coeFn_nonneg _).mp
        filter_upwards [hwr] with x hx
        rw [hx]
        by_cases h : x∈s <;> simp [h]
      have hwb : ∀ᵐ x ∂μ, |w x|≤(1:ℝ≥0) := by
        filter_upwards [hwr] with x hx
        rw [hx]
        by_cases h : x∈s <;> simp [h]
      have hh := hX.heat_hamilton_weighted hn p f w hf0 hw0 A 1 hf hwb
        (integrable_indicatorConstLp hs hfin.ne 1) hT hε
      have hi : (∫ x, w x*localGamma μ Q u u x/(ε+v x) ∂μ) =
          ∫ x in s, localGamma μ Q u u x/(ε+v x) ∂μ := by
        calc
          _ = ∫ x, w x*(localGamma μ Q u u x/(ε+v x)) ∂μ := by simp only [mul_div_assoc]
          _ = _ := integral_indicatorConstLp_mul μ s hs hfin.ne _
      have hr : (∫ x, w x*(ε+v x)*(Real.log (ε+A)-Real.log (ε+v x)) ∂μ) =
          ∫ x in s, R x ∂μ := by
        calc
          _ = ∫ x, w x*R x ∂μ := by dsimp only [R]; simp only [mul_assoc]
          _ = _ := integral_indicatorConstLp_mul μ s hs hfin.ne _
      change c*(∫ x, w x*localGamma μ Q u u x/(ε+v x) ∂μ)≤_ at hh
      rw [hi,hr] at hh
      rw [integral_sub (hRi s hfin) (hFi s hfin)]
      have hFint : (∫ x in s, F x ∂μ) = c*(∫ x in s, localGamma μ Q u u x/(ε+v x) ∂μ) := by
        dsimp only [F]
        simp only [mul_div_assoc,integral_const_mul]
      rw [hFint]
      linarith only [hh]
  filter_upwards [hp,hv] with x hx hvx
  have hden : 0<ε+v x := add_pos_of_pos_of_nonneg hε hvx.1
  have hle : F x≤R x := sub_nonneg.mp hx
  have hm := (div_le_iff₀ hden).mp hle
  dsimp only [F,R] at hm
  dsimp only [c,u,v] at hm ⊢
  nlinarith only [hm]

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
