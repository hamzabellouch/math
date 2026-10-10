import OAI.Geometry.RCD.Heat.HeatLiYauWeighted
import OAI.Geometry.RCD.Coordinates.RegularizedHamiltonIntegrability
import OAI.Geometry.RCD.Heat.HeatReversePoincare

namespace OAI

/-! # The regularized Li--Yau estimate almost everywhere

Finite-measure indicators identify the actual generator and gradient
representatives. All source integrals are justified locally in L².
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

theorem heat_liYau_regularized (hK : K≤0)
    (f : Lp ℝ 2 (hausdorff n X)) (hf0 : 0≤f) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x|≤A)
    {T ε : ℝ} (hT : 0<T) (hε : 0<ε) :
    ∀ᵐ x ∂hausdorff n X,
      localGamma (hausdorff n X) hX.quadratic
        (heatSobolev (hausdorff n X) hX.quadratic T hT f)
        (heatSobolev (hausdorff n X) hX.quadratic T hT f) x ≤
      2*(ε+heatAt (hausdorff n X) hX.quadratic T f x)*
        (-heatGeneratorAt (hausdorff n X) hX.quadratic T f) x+
      (2*(n:ℝ)*(|K|+1/T))*(ε+heatAt (hausdorff n X) hX.quadratic T f x)^2 := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  let u := heatSobolev μ Q T hT f
  let v := heatAt μ Q T f
  let d := -heatGeneratorAt μ Q T f
  let c := 2*(n:ℝ)*(|K|+1/T)
  let F := fun x => localGamma μ Q u u x/(ε+v x)
  let R := fun x => c*(ε+v x)+2*d x
  have hv : ∀ᵐ x ∂μ, 0≤v x := by
    filter_upwards [(Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ Q T f hf0)] with x hx
    exact hx
  have hu : ∀ᵐ x ∂μ, 0≤SobolevSpace.toLp μ Q u x := hv
  have hFi : Integrable F μ := by
    simpa only [F,one_mul,u,heatSobolev_toLp] using regularized_gamma_integrable μ Q u hε hu 1
  have hRi (s : Set X) (hs : μ s<∞) : IntegrableOn R s μ := by
    let : IsFiniteMeasure (μ.restrict s) := ⟨by simpa only [Measure.restrict_apply_univ] using hs⟩
    have hvi := ((Lp.memLp v).restrict s).integrable (by norm_num)
    have hdi := ((Lp.memLp d).restrict s).integrable (by norm_num)
    exact (((integrable_const ε).add hvi).const_mul c).add (hdi.const_mul 2)
  have hp : 0≤ᵐ[μ] fun x => R x-F x := by
    apply ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite
    · intro s _ hs
      exact (hRi s hs).sub hFi.integrableOn
    · intro s hs hfin
      by_cases hs0 : μ s=0
      · have he : μ.restrict s=0 := Measure.restrict_eq_zero.mpr hs0
        simp only [he,integral_zero_measure,le_refl]
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
      have hmass : (∫ x, w x ∂μ)=μ.real s := by
        simpa only [w,smul_eq_mul,mul_one] using integral_indicatorConstLp (p:=2) hs hfin.ne (1:ℝ)
      have hwm : 0<∫ x, w x ∂μ := hmass.symm ▸ ENNReal.toReal_pos hs0 hfin.ne
      have hh := hX.heat_liYau_weighted hn p hK f w hf0 hw0 A 1 hf hwb
        (integrable_indicatorConstLp hs hfin.ne 1) hwm hT hε
      have he (g : Lp ℝ 2 μ) : inner ℝ w g=∫ x in s, g x ∂μ := by
        rw [L2.inner_def]
        simpa only [Real.inner_apply] using integral_indicatorConstLp_mul μ s hs hfin.ne g
      have hF : (∫ x, w x*localGamma μ Q u u x/(ε+v x) ∂μ)=∫ x in s, F x ∂μ := by
        simp only [mul_div_assoc]
        exact integral_indicatorConstLp_mul μ s hs hfin.ne F
      change (∫ x, w x*localGamma μ Q u u x/(ε+v x) ∂μ)-2*inner ℝ w d≤
        2*(n:ℝ)*(ε*(∫ x, w x ∂μ)+inner ℝ w v)*(|K|+1/T) at hh
      rw [hF,he d,he v,hmass] at hh
      let : IsFiniteMeasure (μ.restrict s) := ⟨by simpa only [Measure.restrict_apply_univ] using hfin⟩
      have hvi := ((Lp.memLp v).restrict s).integrable (by norm_num)
      have hdi := ((Lp.memLp d).restrict s).integrable (by norm_num)
      have hR : (∫ x in s, R x ∂μ)=c*(ε*μ.real s+∫ x in s, v x ∂μ)+2*(∫ x in s, d x ∂μ) := by
        have hadd := integral_add (((integrable_const ε).add hvi).const_mul c) (hdi.const_mul 2)
        have hsum := integral_add (integrable_const ε) hvi
        simp only [Pi.add_apply] at hadd hsum
        change (∫ x in s, c*(ε+v x)+2*d x ∂μ)=_
        rw [hadd,integral_const_mul,integral_const_mul,hsum,integral_const]
        simp only [Measure.restrict_apply_univ,smul_eq_mul,Measure.real]
        ring
      rw [integral_sub (hRi s hfin) hFi.integrableOn,hR]
      dsimp only [c]
      nlinarith only [hh]
  filter_upwards [hp,hv] with x hx hy
  have hden : 0<ε+v x := add_pos_of_pos_of_nonneg hε hy
  have hle : F x≤R x := sub_nonneg.mp hx
  have hb := (div_le_iff₀ hden).mp hle
  dsimp only [F,R,c,u,v,d] at hb ⊢
  nlinarith only [hb]

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
