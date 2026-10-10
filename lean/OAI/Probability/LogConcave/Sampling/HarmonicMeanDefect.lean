import Mathlib
import OAI.Probability.LogConcave.Sampling.ProbabilityNodes

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory
open scoped Classical BigOperators RealInnerProductSpace NNReal

theorem harmonic_integral_equation {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {Y P : ℝ → E} {f : E → E}
    (hY : Continuous Y) (hP : Continuous P) (hf : Continuous f)
    (hderY : ∀v∈Icc (0:ℝ) 1,HasDerivWithinAt Y (P v) (Icc (0:ℝ) 1) v)
    (hderP : ∀v∈Icc (0:ℝ) 1,HasDerivWithinAt P (-Y v-f (Y v)) (Icc (0:ℝ) 1) v)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    Y t=Real.cos t • Y 0+Real.sin t • P 0-
      ∫v in 0..t,Real.sin (t-v) • f (Y v) := by
  let g : ℝ → E := fun v => Real.cos (t-v) • Y v+Real.sin (t-v) • P v
  have hg : Continuous g := by unfold g; fun_prop
  have hfg : Continuous (fun v => -Real.sin (t-v) • f (Y v)) := by fun_prop
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 hg.continuousOn
    (f':=fun v => -Real.sin (t-v) • f (Y v))
    (fun v hv => by
      have hm : v∈Icc (0:ℝ) 1 := ⟨hv.1.le,hv.2.le.trans ht.2⟩
      have hn := Icc_mem_nhds hv.1 (hv.2.trans_le ht.2)
      have hDY := (hderY v hm).hasDerivAt hn
      have hDP := (hderP v hm).hasDerivAt hn
      have hcos : HasDerivAt (fun u => Real.cos (t-u)) (Real.sin (t-v)) v := by
        convert ((hasDerivAt_const v t).sub (hasDerivAt_id v)).cos using 1 <;> simp
      have hsin : HasDerivAt (fun u => Real.sin (t-u)) (-Real.cos (t-v)) v := by
        convert ((hasDerivAt_const v t).sub (hasDerivAt_id v)).sin using 1 <;> simp
      convert (hcos.smul hDY).add (hsin.smul hDP) using 1
      module)
    (hfg.intervalIntegrable 0 t)
  change (∫v in 0..t,-Real.sin (t-v) • f (Y v))=g t-g 0 at he
  simp only [g,sub_self,Real.cos_zero,Real.sin_zero,one_smul,zero_smul,add_zero,sub_zero] at he
  simp_rw [neg_smul] at he
  rw [intervalIntegral.integral_neg] at he
  exact (sub_eq_iff_eq_add.mp he.symm).trans (by abel)

theorem conditional_harmonic_integral {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)
    (Ξ : Point (d+d) → ℝ → Point (d+d))
    (hc : ∀y,Continuous (Ξ y))
    (hder : ∀y v,v∈Icc (0:ℝ) 1 → HasDerivWithinAt (Ξ y)
      (skewLieField (productPotential (interpolationPotential F x r T) (fun z : Point d => ‖z‖^2/2)) (harmonicSkew d) (Ξ y v)) (Icc (0:ℝ) 1) v)
    (y : Point (d+d)) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    let W := fun v => (productPointEquiv d d (Ξ y v)).1
    let P := fun v => (productPointEquiv d d (Ξ y v)).2
    W t=Real.cos t • W 0+Real.sin t • P 0-
      (r*T) • (∫v in 0..t,Real.sin (t-v) • conditionalFieldMean F x r T (W v)) := by
  intro W P
  have hH : Differentiable ℝ (interpolationPotential F x r T) :=
    (interpolationPotential_smooth hF x hr hl hT0 hT1).differentiable (by norm_cast)
  have hD (v : ℝ) (hv : v∈Icc (0:ℝ) 1) :
      HasDerivWithinAt (fun s => productPointEquiv d d (Ξ y s))
        (P v,-W v-(r*T) • conditionalFieldMean F x r T (W v)) (Icc (0:ℝ) 1) v := by
    have h := (productPointEquiv d d).toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt v (hder y v hv)
    change HasDerivWithinAt (fun s => productPointEquiv d d (Ξ y s))
      (productPointEquiv d d (skewLieField
        (productPotential (interpolationPotential F x r T) (fun z : Point d => ‖z‖^2/2))
        (harmonicSkew d) (Ξ y v))) (Icc (0:ℝ) 1) v at h
    rw [harmonicSkew_field hH] at h
    rw [interpolationPotential_gradient hF x hr hl hT0 hT1] at h
    simpa only [W,P,neg_add_rev,sub_eq_add_neg,add_comm] using h
  have he := harmonic_integral_equation ((productPointEquiv d d).continuous.comp (hc y)).fst
    ((productPointEquiv d d).continuous.comp (hc y)).snd
    ((conditionalFieldMean_lipschitz hF x hr hl hT0 hT1).continuous.const_smul (r*T))
    (fun v hv => (hD v hv).fst) (fun v hv => (hD v hv).snd) ht
  change W t=Real.cos t • W 0+Real.sin t • P 0-
    ∫v in 0..t,Real.sin (t-v) • ((r*T) • conditionalFieldMean F x r T (W v)) at he
  simp_rw [smul_comm (Real.sin (t-_)) (r*T)] at he
  rw [intervalIntegral.integral_smul] at he
  exact he

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory TensorEnergy Quadrature
open scoped Classical BigOperators NNReal RealInnerProductSpace

local instance harmonicMeanDefectDecidableEqUnit : DecidableEq Unit := Classical.decEq _

def harmonicMeanDefect {d : ℕ} (F : Point d → ℝ) (x : Point d) (r T z : ℝ)
    (Ξ : Point (d+d) → ℝ → Point (d+d)) (n : ℕ) (i : Fin (n+1)) (y : Point (d+d)) : Point d :=
  let M := fun t => conditionalFieldMean F x r T (productPointEquiv d d (Ξ y (z*t))).1
  z • (∫t in 0..probabilityNodes n i,Real.sin (z*(probabilityNodes n i-t)) • M t)-
    ∑j,harmonicWeight n z i j • M (probabilityNodes n j)

lemma interpolation_error_measurable {I E Ω : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace Ω] [SecondCountableTopology E] (u : I → ℝ) (f : ℝ × Ω → E)
    (hf : Measurable f) : Measurable (fun p : ℝ × Ω => f p-
      interpolation u (fun j => f (u j,p.2)) p.1) := by
  apply hf.sub
  apply Finset.measurable_sum
  intro j hj
  exact ((basis_continuous u j).measurable.comp measurable_fst).smul
    (hf.comp (measurable_const.prodMk measurable_snd))

lemma harmonicMean_measurable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T z : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)
    (Ξ : Point (d+d) → ℝ → Point (d+d))
    (hm : Measurable (fun p : ℝ × Point (d+d) => Ξ p.2 p.1)) :
    Measurable (fun p : ℝ × Point (d+d) =>
      conditionalFieldMean F x r T (productPointEquiv d d (Ξ p.2 (z*p.1))).1) := by
  have h1 : Measurable (fun p : ℝ × Point (d+d) => Ξ p.2 (z*p.1)) :=
    hm.comp ((measurable_const.mul measurable_fst).prodMk measurable_snd)
  have h2 : Measurable (fun p : ℝ × Point (d+d) => (productPointEquiv d d (Ξ p.2 (z*p.1))).1) :=
    ((productPointEquiv d d).continuous.measurable.comp h1).fst
  exact (conditionalFieldMean_lipschitz hF x hr hl hT0 hT1).continuous.measurable.comp h2

theorem harmonic_mean_quadrature_rms (n : ℕ) (hn : 0<n) :
    ∃C : ℝ,1≤C ∧ ∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
      ∀_ : Primitive F lam,∀(x : Point d) {r R T : ℝ},
      0<r → 0<lam → (lam:ℝ)*r^2≤1/2 → 0<R → R^2≤1-T^2 → 0≤T → T<1 →
      ∀Ξ : Point (d+d) → ℝ → Point (d+d),
      (∀y,Continuous (Ξ y)) →
      (∀y v,v∈Icc (0:ℝ) 1 → HasDerivWithinAt (Ξ y)
        (skewLieField (centeringPotential F x r T) (harmonicSkew d) (Ξ y v)) (Icc (0:ℝ) 1) v) →
      Measurable (fun p : ℝ × Point (d+d) => Ξ p.2 p.1) →
      (∀v∈Icc (0:ℝ) 1,(gibbs (centeringPotential F x r T)).map (fun y => Ξ y v)=
        gibbs (centeringPotential F x r T)) →
      ∀z : ℝ,0≤z → z≤1 → ∀i : Fin (n+1),
      Integrable (fun y => ‖harmonicMeanDefect F x r T z Ξ n i y‖^2)
          (gibbs (centeringPotential F x r T)) ∧
      (∫y,‖harmonicMeanDefect F x r T z Ξ n i y‖^2 ∂gibbs (centeringPotential F x r T))≤
        4*C^2*(z^(n+1)/(n.factorial:ℝ))^2*
          ((d*((lam:ℝ)*r)^2)*(R⁻¹)^(4*(n+1))*harmonicMeanBudget (n+1)) := by
  obtain ⟨C,hC,hC'⟩ := harmonic_point_interpolation_rms n hn
  refine ⟨C,hC,?_⟩
  intro d F lam hF x r R T hr hlam hl hR hRT hT0 hT1 Ξ hc hder hm hlaw z hz hz1 i
  have hH := productPotential_polySmooth
    (interpolationPotential_polySmooth hF x hr hlam hl hT0 hT1) (gaussianPotential_polySmooth d)
  have ht := productPotential_lowerTail
    (interpolationPotential_lowerTail hF x hr.le (by linarith) hT0 hT1) (gaussianPotential_lowerTail d)
  let : IsProbabilityMeasure (gibbs (centeringPotential F x r T)) :=
    probability_gibbs_of_gaussianTail hH.smooth.continuous ht
  let M := fun t y => conditionalFieldMean F x r T (productPointEquiv d d (Ξ y (z*t))).1
  let B := 4*C^2*(z^(n+1)/(n.factorial:ℝ))^2*
    ((d*((lam:ℝ)*r)^2)*(R⁻¹)^(4*(n+1))*harmonicMeanBudget (n+1))
  have hB0 : 0≤B := by dsimp [B]; positivity [harmonicMeanBudget_nonneg (n+1)]
  have hMcont := (conditionalFieldMean_lipschitz hF x hr.le hl hT0 hT1).continuous
  have hMc (y : Point (d+d)) : Continuous (fun t => M t y) :=
    hMcont.comp (((productPointEquiv d d).continuous.comp
      ((hc y).comp (continuous_const.mul continuous_id))).fst)
  have hMm := harmonicMean_measurable (z:=z) hF x hr.le hl hT0 hT1 Ξ hm
  have hErr := interpolation_error_measurable (probabilityNodes n) _ hMm
  have hi := probabilityNodes_mem hn i
  have hmem (t : ℝ) (ht : t∈Ioc 0 (probabilityNodes n i)) : t∈Icc (0:ℝ) 1 :=
    ⟨ht.1.le,ht.2.trans hi.2⟩
  have he := harmonic_quadrature_error_rms n z i M hi.1 hB0 hMc hErr.aestronglyMeasurable
    (fun t ht => (hC' hF x hr hlam hl hR hRT hT0 hT1 Ξ hder hm hlaw z hz hz1 t (hmem t ht)).1)
    (fun t ht => (hC' hF x hr hlam hl hR hRT hT0 hT1 Ξ hder hm hlaw z hz hz1 t (hmem t ht)).2)
  refine ⟨he.1,he.2.trans ?_⟩
  have hz2 : z^2≤1 := pow_le_one₀ hz hz1
  have hi2 : (probabilityNodes n i)^2≤1 := pow_le_one₀ hi.1 hi.2
  exact (mul_le_mul_of_nonneg_right ((mul_le_of_le_one_left (sq_nonneg _) hz2).trans hi2) hB0).trans_eq (one_mul _)

lemma harmonicPicard_exact_defect {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T z : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)
    (Ξ : Point (d+d) → ℝ → Point (d+d)) (hc : ∀y,Continuous (Ξ y))
    (hinit : ∀y,Ξ y 0=y)
    (hder : ∀y v,v∈Icc (0:ℝ) 1 → HasDerivWithinAt (Ξ y)
      (skewLieField (centeringPotential F x r T) (harmonicSkew d) (Ξ y v)) (Icc (0:ℝ) 1) v)
    (hz : 0≤z) (hz1 : z≤1) (n : ℕ) (hn : 0<n) (i : Fin (n+1)) (y : Point (d+d)) :
    FinitePicard.step (harmonicWeight n z) (fun _ => harmonicMeanVelocity F x r T)
      (harmonicFree n z (productPointEquiv d d y))
      (fun j => (productPointEquiv d d (Ξ y (z*probabilityNodes n j))).1) i-
      (productPointEquiv d d (Ξ y (z*probabilityNodes n i))).1=
      (r*T) • harmonicMeanDefect F x r T z Ξ n i y := by
  have hi := probabilityNodes_mem hn i
  have hzi : z*probabilityNodes n i∈Icc (0:ℝ) 1 :=
    ⟨mul_nonneg hz hi.1,(mul_le_of_le_one_right hz hi.2).trans hz1⟩
  have he := conditional_harmonic_integral hF x hr hl hT0 hT1 Ξ hc hder y hzi
  dsimp only at he
  rw [hinit] at he
  have hchange := intervalIntegral.smul_integral_comp_mul_left
    (fun v => Real.sin (z*probabilityNodes n i-v) •
      conditionalFieldMean F x r T (productPointEquiv d d (Ξ y v)).1)
    (a:=0) (b:=probabilityNodes n i) z
  simp only [mul_zero] at hchange
  simp_rw [←mul_sub] at hchange
  rw [←hchange] at he
  change (harmonicFree n z (productPointEquiv d d y) i+
    ∑j,harmonicWeight n z i j • harmonicMeanVelocity F x r T
      (productPointEquiv d d (Ξ y (z*probabilityNodes n j))).1)-_= _
  have hvel (u : Point d) : harmonicMeanVelocity F x r T u=-(r*T) • conditionalFieldMean F x r T u := by
    simp only [harmonicMeanVelocity,probabilityMeanVelocity,smul_smul,mul_neg,mul_comm]
  simp_rw [hvel,smul_comm (harmonicWeight n z i _) (-(r*T))]
  rw [←Finset.smul_sum,neg_smul,he]
  dsimp only [harmonicFree,harmonicMeanDefect]
  rw [smul_sub]
  abel
end LogConcaveSampling

end

end

end

end OAI
