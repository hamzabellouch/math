import Mathlib
import OAI.Analysis.Conductivity.Walls.SeamCutoff

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped NNReal

lemma seamCutoff_sq_error_bound (n : ℕ) (t a : ℝ) :
    (seamCutoff n t*a-a)^2 ≤ a^2 := by
  have hb := seamCutoff_bounds n t
  have h₁ : |seamCutoff n t-1|≤1 := abs_le.mpr ⟨by linarith,by linarith⟩
  have h₂ : |seamCutoff n t*a-a|≤|a| := by
    calc
      _ = |seamCutoff n t-1| *|a| := by rw [←abs_mul]; congr 1; ring
      _ ≤ 1*|a| := mul_le_mul_of_nonneg_right h₁ (abs_nonneg a)
      _ = |a| := one_mul _
  exact (sq_le_sq).mpr h₂

lemma seamCutoff_L2_approx {τ u : R3 → ℝ} (hτ : Continuous τ)
    (hu : MemLp u 2 volume) (hz : ∀ᵐ x,τ x≤0 → u x=0) :
    Tendsto (fun n => ∫ x,(seamCutoff n (τ x)*u x-u x)^2) atTop (𝓝 0) := by
  have hc (n : ℕ) : AEStronglyMeasurable (fun x => seamCutoff n (τ x)*u x-u x) volume :=
    (((seamCutoff_smooth n).continuous.comp hτ).aestronglyMeasurable.mul hu.aestronglyMeasurable).sub hu.aestronglyMeasurable
  have ht := tendsto_integral_of_dominated_convergence (F:=fun n x => (seamCutoff n (τ x)*u x-u x)^2) (fun x => u x^2)
    (fun n => (hc n).pow 2) hu.integrable_sq
    (fun n => ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact seamCutoff_sq_error_bound n (τ x) (u x)))
    (f:=fun _ => (0:ℝ)) (by
      filter_upwards [hz] with x hx
      by_cases hp : 0<τ x
      · exact tendsto_const_nhds.congr' (by
          filter_upwards [seamCutoff_eventually_one hp] with n hn
          simp [hn])
      · have he := hx (le_of_not_gt hp)
        simpa only [he,mul_zero,sub_self,zero_pow (by norm_num : 2≠0)] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0)))
  simpa only [integral_zero] using ht

lemma seamCutoff_mul_lineDeriv {τ u : R3 → ℝ} {K : ℝ≥0}
    (hτ : LipschitzWith K τ) (v : R3) {g : R3 → ℝ}
    (hd : ∀ᵐ x,0<τ x → HasLineDerivAt ℝ u (g x) x v)
    (hz : ∀ᵐ x,τ x≤0 → u x=0 ∧ g x=0) (n : ℕ) :
    (fun x => lineDeriv ℝ (fun y => seamCutoff n (τ y)*u y) x v)=ᵐ[volume]
      (fun x => seamCutoff n (τ x)*g x+
        deriv (seamCutoff n) (τ x)*lineDeriv ℝ τ x v*u x) := by
  filter_upwards [hτ.ae_lineDifferentiableAt (μ:=volume) v,hd,hz] with x hx hu hzero
  by_cases hp : 0<τ x
  · have hc : HasDerivAt (seamCutoff n) (deriv (seamCutoff n) (τ x)) (τ x) :=
      ((seamCutoff_smooth n).differentiable (by simp)).differentiableAt.hasDerivAt
    have hdu := hu hp
    have hdt := hx.hasLineDerivAt
    change HasDerivAt (fun t : ℝ => u (x+t•v)) (g x) 0 at hdu
    change HasDerivAt (fun t : ℝ => τ (x+t•v)) (lineDeriv ℝ τ x v) 0 at hdt
    have hcc : HasDerivAt (seamCutoff n) (deriv (seamCutoff n) (τ x)) (τ (x+(0:ℝ)•v)) := by simpa using hc
    have hc' := hcc.comp (0:ℝ) hdt
    have hh := hc'.mul hdu
    have hh' : HasLineDerivAt ℝ (fun y => seamCutoff n (τ y)*u y)
        (seamCutoff n (τ x)*g x+deriv (seamCutoff n) (τ x)*lineDeriv ℝ τ x v*u x) x v := by
      change HasDerivAt (fun t : ℝ => seamCutoff n (τ (x+t•v))*u (x+t•v)) _ 0
      simpa only [Pi.mul_def,Function.comp_def,zero_smul,add_zero,add_comm] using hh
    exact hh'.lineDeriv
  · have hn := le_of_not_gt hp
    have he : (fun y => seamCutoff n (τ y)*u y)=ᶠ[𝓝 x] (fun _ => 0) := by
      have hx' : ((n:ℝ)+1)*τ x<1 := by nlinarith [Nat.cast_nonneg (α:=ℝ) n]
      filter_upwards [isOpen_lt (continuous_const.mul hτ.continuous) continuous_const |>.mem_nhds hx'] with y hy
      rw [seamCutoff_zero n hy.le,zero_mul]
    rw [he.lineDeriv_eq,(differentiableAt_const (0:ℝ)).lineDeriv_eq_fderiv]
    simp [(hzero hn).1,(hzero hn).2]

def seamLayer (τ : R3 → ℝ) (n : ℕ) : Set R3 :=
  {x | 0<τ x ∧ ((n:ℝ)+1)*τ x≤2}

lemma measurableSet_seamLayer {τ : R3 → ℝ} (hτ : Continuous τ) (n : ℕ) :
    MeasurableSet (seamLayer τ n) :=
  (isOpen_lt continuous_const hτ).measurableSet.inter
    (isClosed_le (continuous_const.mul hτ) continuous_const).measurableSet

lemma seamCutoff_remainder_sq_bound {τ u : R3 → ℝ} {K : ℝ≥0}
    (hτ : LipschitzWith K τ) (v : R3) {D : ℝ} (hD : 0≤D)
    (hb : ∀ n t,|deriv (seamCutoff n) t|≤D*((n:ℝ)+1))
    (hz : ∀ᵐ x,τ x≤0 → u x=0) (n : ℕ) :
    ∀ᵐ x,(deriv (seamCutoff n) (τ x)*lineDeriv ℝ τ x v*u x)^2 ≤
      (D^2*((K:ℝ)*‖v‖)^2)*((n:ℝ)+1)^2*(seamLayer τ n).indicator (fun x => u x^2) x := by
  filter_upwards [hz] with x hx
  by_cases hs : x∈seamLayer τ n
  · rw [indicator_of_mem hs]
    have hd : |lineDeriv ℝ τ x v|≤(K:ℝ)*‖v‖ := norm_lineDeriv_le_of_lipschitz ℝ hτ
    have hp : |deriv (seamCutoff n) (τ x)*lineDeriv ℝ τ x v|≤
        D*((n:ℝ)+1)*((K:ℝ)*‖v‖) := by
      rw [abs_mul]
      exact mul_le_mul (hb n (τ x)) hd (abs_nonneg _) (mul_nonneg hD (by positivity))
    have hsqr : (deriv (seamCutoff n) (τ x)*lineDeriv ℝ τ x v)^2≤
        (D*((n:ℝ)+1)*((K:ℝ)*‖v‖))^2 := by
      apply (sq_le_sq).mpr
      have hn : 0≤D*((n:ℝ)+1)*((K:ℝ)*‖v‖) := by positivity
      simpa only [abs_of_nonneg hn] using hp
    calc
      _ = (deriv (seamCutoff n) (τ x)*lineDeriv ℝ τ x v)^2*u x^2 := mul_pow _ _ _
      _ ≤ (D*((n:ℝ)+1)*((K:ℝ)*‖v‖))^2*u x^2 := mul_le_mul_of_nonneg_right hsqr (sq_nonneg _)
      _ = _ := by ring
  · rw [indicator_of_notMem hs,mul_zero]
    by_cases hp : 0<τ x
    · have ht : 2<((n:ℝ)+1)*τ x := lt_of_not_ge (fun ht => hs ⟨hp,ht⟩)
      rw [seamCutoff_deriv_zero n ht,zero_mul,zero_mul]
      norm_num
    · rw [hx (le_of_not_gt hp),mul_zero]
      norm_num

lemma seamCutoff_gradient_L2_approx {τ u g : R3 → ℝ} {K : ℝ≥0}
    (hτ : LipschitzWith K τ) (v : R3) (hu : MemLp u 2 volume) (hg : MemLp g 2 volume)
    (hd : ∀ᵐ x,0<τ x → HasLineDerivAt ℝ u (g x) x v)
    (hz : ∀ᵐ x,τ x≤0 → u x=0 ∧ g x=0)
    (hm : ∀ n,MemLp (fun x => lineDeriv ℝ (fun y => seamCutoff n (τ y)*u y) x v) 2 volume)
    (hthin : Tendsto (fun n : ℕ => ((n:ℝ)+1)^2*∫ x in seamLayer τ n,u x^2) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x,(lineDeriv ℝ (fun y => seamCutoff n (τ y)*u y) x v-g x)^2)
      atTop (𝓝 0) := by
  obtain ⟨D,hD,hDb⟩ := seamCutoff_deriv_bound
  let C : ℝ := D^2*((K:ℝ)*‖v‖)^2
  have hC : 0≤C := by dsimp [C]; positivity
  have hz₁ : ∀ᵐ x,τ x≤0 → u x=0 := hz.mono (fun x hx ht => (hx ht).1)
  have hz₂ : ∀ᵐ x,τ x≤0 → g x=0 := hz.mono (fun x hx ht => (hx ht).2)
  have hlim := (seamCutoff_L2_approx hτ.continuous hg hz₂).const_mul 2 |>.add (hthin.const_mul (2*C))
  simp only [mul_zero,add_zero] at hlim
  apply squeeze_zero (fun n => integral_nonneg (fun x => sq_nonneg _)) _ hlim
  intro n
  have hcut : MemLp (fun x => seamCutoff n (τ x)*g x-g x) 2 volume := by
    apply hg.mono (((seamCutoff_smooth n).continuous.comp hτ.continuous).aestronglyMeasurable.mul hg.aestronglyMeasurable |>.sub hg.aestronglyMeasurable)
    filter_upwards with x
    exact (sq_le_sq).mp (seamCutoff_sq_error_bound n (τ x) (g x))
  have hi := (hcut.integrable_sq.const_mul 2).add
    ((hu.integrable_sq.indicator (measurableSet_seamLayer hτ.continuous n)).const_mul (2*C*((n:ℝ)+1)^2))
  have hle := integral_mono_ae ((hm n).sub hg).integrable_sq hi (by
    filter_upwards [seamCutoff_mul_lineDeriv hτ v hd hz n,
      seamCutoff_remainder_sq_bound hτ v hD hDb hz₁ n] with x hx hb
    simp only [Pi.sub_apply,Pi.add_apply]
    rw [hx]
    dsimp only [C] at hb ⊢
    nlinarith [sq_nonneg (seamCutoff n (τ x)*g x-g x-
      deriv (seamCutoff n) (τ x)*lineDeriv ℝ τ x v*u x)])
  simp only [Pi.sub_apply,Pi.add_apply] at hle
  rw [integral_add (hcut.integrable_sq.const_mul 2)
    ((hu.integrable_sq.indicator (measurableSet_seamLayer hτ.continuous n)).const_mul (2*C*((n:ℝ)+1)^2)),
    integral_const_mul,integral_const_mul,integral_indicator (measurableSet_seamLayer hτ.continuous n)] at hle
  simpa only [mul_assoc] using hle

end ScalarConductivity

end

end OAI
