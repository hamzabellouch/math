import Mathlib
import OAI.Probability.SKSupport.Parabolic.VarianceTilted

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma hasDerivWithinAt_varianceHeat_weightExp {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g) (c : ℝ)
    {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    HasDerivWithinAt (fun s => varianceHeat s (fun z => g z*Real.exp (c*f z)) x)
      ((1/2:ℝ)*varianceHeat t (deriv (deriv (fun z => g z*Real.exp (c*f z)))) x)
      (Set.Ici 0) t := by
  exact hasDerivWithinAt_varianceHeat
    ((hg.smooth.mul (contDiff_const.mul hf.smooth).exp).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (by simpa only [iteratedDeriv_zero] using exponentialBound_weightExp_iteratedDeriv hf hLip hg c 0)
    (by simpa only [iteratedDeriv_one] using exponentialBound_weightExp_iteratedDeriv hf hLip hg c 1)
    (by simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using
      exponentialBound_weightExp_iteratedDeriv hf hLip hg c 2) ht x

lemma hasDerivWithinAt_varianceTilted {f g q r : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g) (c : ℝ)
    (hq : deriv (deriv (fun z => g z*Real.exp (c*f z))) = fun z => q z*Real.exp (c*f z))
    (hr : deriv (deriv (fun z => Real.exp (c*f z))) = fun z => r z*Real.exp (c*f z))
    {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    HasDerivWithinAt (fun s => varianceTilted c s f g x)
      ((1/2:ℝ)*(varianceTilted c t f q x-varianceTilted c t f g x*varianceTilted c t f r x))
      (Set.Ici 0) t := by
  have hd := (hasDerivWithinAt_varianceHeat_weightExp hf hLip hg c ht x).div
    (hasDerivWithinAt_varianceHeat_exp hf hLip c ht x)
    (ne_of_gt (varianceHeat_exp_pos hLip c t x))
  rw [hq, hr] at hd
  convert hd using 1 <;> try rfl
  all_goals
    try dsimp only [varianceTilted]
    field_simp [ne_of_gt (varianceHeat_exp_pos hLip c t x)]

lemma varianceTilted_time_lipschitz {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g) (c : ℝ) :
    ∃ C : ℝ≥0, ∀ x, LipschitzOnWith C (fun t => varianceTilted c t f g x) (Set.Ici 0) := by
  obtain ⟨q,hqs,hq⟩ := weightExp_iteratedDeriv_weight hf hg c 2
  obtain ⟨r,hrs,hr⟩ := exp_iteratedDeriv_weight hf c 2
  simp only [iteratedDeriv_succ, iteratedDeriv_zero] at hq hr
  obtain ⟨Q,hQ⟩ := hqs.bound
  obtain ⟨R,hR⟩ := hrs.bound
  obtain ⟨G,hG⟩ := hg.bound
  refine ⟨(Q+G*R)/2, fun x => ?_⟩
  apply (convex_Ici (0:ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun t ht => hasDerivWithinAt_varianceTilted hf hLip hg c hq hr ht x)
  intro t ht
  apply NNReal.coe_le_coe.mp
  simp only [coe_nnnorm, Real.norm_eq_abs, NNReal.coe_div, NNReal.coe_add,
    NNReal.coe_mul, NNReal.coe_ofNat]
  rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  have hb : |varianceTilted c t f q x-varianceTilted c t f g x*varianceTilted c t f r x| ≤
      (Q:ℝ)+(G:ℝ)*(R:ℝ) := by
    calc
      _ ≤ |varianceTilted c t f q x|+|varianceTilted c t f g x*varianceTilted c t f r x| := abs_sub _ _
      _ ≤ (Q:ℝ)+(G:ℝ)*(R:ℝ) := by
        apply add_le_add (varianceTilted_bound hLip hqs.smooth.continuous.measurable hQ c t x)
        rw [abs_mul]
        exact mul_le_mul
          (varianceTilted_bound hLip hg.smooth.continuous.measurable hG c t x)
          (varianceTilted_bound hLip hrs.smooth.continuous.measurable hR c t x)
          (abs_nonneg _) G.coe_nonneg
  linarith

lemma varianceTilted_space_lipschitz {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g)
    {c : ℝ} (hc : 0 ≤ c) :
    ∃ C : ℝ≥0, ∀ t, LipschitzWith C (varianceTilted c t f g) := by
  obtain ⟨C,hC⟩ := uniform_tiltedMean_bounds hf hLip hg hc 1
  refine ⟨C, fun t => ?_⟩
  have he : varianceTilted c t f g = tiltedMean c (Real.toNNReal t) f g :=
    funext (varianceTilted_eq_tiltedMean hf.smooth.continuous.measurable
      hg.smooth.continuous.measurable c t)
  rw [he]
  apply lipschitzWith_of_nnnorm_deriv_le
    ((contDiff_tiltedMean hf hLip hg hc _).differentiable (by simp))
  intro x
  exact NNReal.coe_le_coe.mp (by
    simpa only [coe_nnnorm, Real.norm_eq_abs, iteratedDeriv_one] using (hC (Real.toNNReal t) x))

lemma varianceTilted_joint_bound {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g)
    {c : ℝ} (hc : 0 ≤ c) :
    ∃ L : ℝ≥0, ∀ t ∈ Set.Ici (0:ℝ), ∀ s ∈ Set.Ici (0:ℝ), ∀ x y,
      |varianceTilted c t f g x-varianceTilted c s f g y| ≤ (L:ℝ)*(|t-s|+|x-y|) := by
  obtain ⟨A,hA⟩ := varianceTilted_time_lipschitz hf hLip hg c
  obtain ⟨B,hB⟩ := varianceTilted_space_lipschitz hf hLip hg hc
  refine ⟨A+B, fun t ht s hs x y => ?_⟩
  have ha := (hA x).dist_le_mul t ht s hs
  have hb := (hB s).dist_le_mul x y
  simp only [Real.dist_eq] at ha hb
  have htri := abs_sub_le (varianceTilted c t f g x) (varianceTilted c s f g x)
    (varianceTilted c s f g y)
  simp only [NNReal.coe_add]
  nlinarith [mul_nonneg A.coe_nonneg (abs_nonneg (x-y)),
    mul_nonneg B.coe_nonneg (abs_nonneg (t-s))]

end ZeroTemperatureSK.Heat

namespace ZeroTemperatureSK.Heat

lemma varianceHeat_const_mul (a t : ℝ) (g : ℝ → ℝ) (x : ℝ) :
    varianceHeat t (fun z => a*g z) x = a*varianceHeat t g x := by
  exact integral_const_mul a _

lemma varianceTilted_zero (t : ℝ) (f g : ℝ → ℝ) (x : ℝ) :
    varianceTilted 0 t f g x = varianceHeat t g x := by
  simp [varianceTilted, varianceHeat, scaled]

def generatorWeight (c : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun z => deriv (deriv f) z+c*(deriv f z)^2

lemma boundedSmooth_generatorWeight {f : ℝ → ℝ} (hf : RegularDatum f) (c : ℝ) :
    BoundedSmooth (generatorWeight c f) := by
  have hh := hf.deriv_bounded.deriv.add ((hf.deriv_bounded.mul hf.deriv_bounded).const_mul c)
  change BoundedSmooth (fun z => deriv (deriv f) z+c*(deriv f z)^2)
  simpa only [pow_two] using hh

lemma deriv_exp_comp {f : ℝ → ℝ} (hf : RegularDatum f) (c : ℝ) :
    deriv (fun z => Real.exp (c*f z)) = fun z => c*deriv f z*Real.exp (c*f z) := by
  funext z
  convert (((hf.smooth.differentiable (by simp) z).hasDerivAt.const_mul c).exp).deriv using 1
  ring

lemma deriv_deriv_exp_comp {f : ℝ → ℝ} (hf : RegularDatum f) (c : ℝ) :
    deriv (deriv (fun z => Real.exp (c*f z))) =
      fun z => c*(generatorWeight c f z*Real.exp (c*f z)) := by
  rw [deriv_exp_comp hf c, deriv_weightExp hf (hf.deriv_bounded.const_mul c) c]
  funext z
  have hd : deriv (fun z => c*deriv f z) z = c*deriv (deriv f) z :=
    (((hf.deriv_bounded.smooth.differentiable (by simp) z).hasDerivAt).const_mul c).deriv
  simp only [hd, generatorWeight]
  ring

lemma varianceLogHeat_time_derivative {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (c : ℝ)
    {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    HasDerivWithinAt (fun s => varianceLogHeat c s f x)
      ((1/2:ℝ)*varianceTilted c t f (generatorWeight c f) x) (Set.Ici 0) t := by
  by_cases hc : c = 0
  · subst c
    have he : (fun s => varianceLogHeat 0 s f x) = fun s => varianceHeat s f x := by
      funext s; simp [varianceLogHeat]
    rw [he, varianceTilted_zero]
    have hw : generatorWeight 0 f = deriv (deriv f) := by funext z; simp [generatorWeight]
    rw [hw]
    obtain ⟨C,hC⟩ := hf.deriv_bounded.bound
    obtain ⟨C',hC'⟩ := hf.deriv_bounded.deriv.bound
    exact hasDerivWithinAt_varianceHeat
      (hf.smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
      (exponentialBound_of_lipschitz hLip) (ExponentialBound.of_bounded hC)
      (ExponentialBound.of_bounded hC') ht x
  · have hd := ((hasDerivWithinAt_varianceHeat_exp hf hLip c ht x).log
        (ne_of_gt (varianceHeat_exp_pos hLip c t x))).div_const c
    have he : (fun s => varianceLogHeat c s f x) = fun s =>
        Real.log (varianceHeat s (fun z => Real.exp (c*f z)) x)/c := by
      funext s; simp [varianceLogHeat, hc]
    rw [he]
    rw [deriv_deriv_exp_comp hf c, varianceHeat_const_mul] at hd
    convert hd using 1
    dsimp only [varianceTilted]
    field_simp [hc, ne_of_gt (varianceHeat_exp_pos hLip c t x)]

lemma varianceLogHeat_generator_identity {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (c : ℝ)
    {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    (1/2:ℝ)*varianceTilted c t f (generatorWeight c f) x =
      (1/2:ℝ)*deriv (deriv (varianceLogHeat c t f)) x+
        c/2*(deriv (varianceLogHeat c t f) x)^2 := by
  have h₁ := (varianceLogHeat_time_derivative hf hLip c ht x).derivWithin
    (uniqueDiffOn_Ici (0:ℝ) t ht)
  have h₂ := (varianceLogHeat_equation hf hLip c ht x).derivWithin
    (uniqueDiffOn_Ici (0:ℝ) t ht)
  exact h₁.symm.trans h₂

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI
