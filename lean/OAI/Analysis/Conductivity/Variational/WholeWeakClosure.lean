import Mathlib
import OAI.Analysis.Conductivity.Variational.CompactBridge

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped RealInnerProductSpace

lemma wholeL2_pair_integral (f : WholeL2) {g : R3 → ℝ} (hg : MemLp g 2 volume) :
    inner ℝ f (hg.toLp g)=∫ x,f x*g x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hg.coeFn_toLp] with x hx
  simp [hx,mul_comm]

lemma wholeL2_pair_tendsto {f : ℕ → WholeL2} {f₀ : WholeL2}
    (hf : Tendsto f atTop (𝓝 f₀)) {g : R3 → ℝ} (hg : MemLp g 2 volume) :
    Tendsto (fun n => ∫ x,f n x*g x) atTop (𝓝 (∫ x,f₀ x*g x)) := by
  simpa only [wholeL2_pair_integral _ hg] using
    (hf.inner (tendsto_const_nhds (x:=hg.toLp g)) :
      Tendsto (fun n => inner ℝ (f n) (hg.toLp g)) atTop (𝓝 (inner ℝ f₀ (hg.toLp g))))

lemma WeakL2Direction.closed {f g : ℕ → WholeL2} {f₀ g₀ : WholeL2} {v : R3}
    (hf : Tendsto f atTop (𝓝 f₀)) (hg : Tendsto g atTop (𝓝 g₀))
    (hw : ∀ n,WeakL2Direction (f n) (g n) v) :
    WeakL2Direction f₀ g₀ v := by
  intro ψ hψ hc
  have hm : MemLp ψ 2 volume := hψ.continuous.memLp_of_hasCompactSupport hc
  have hd : MemLp (fun x => fderiv ℝ ψ x v) 2 volume :=
    ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ v)
  have hleft := wholeL2_pair_tendsto hf hd
  have hright := (wholeL2_pair_tendsto hg hm).neg
  exact tendsto_nhds_unique hleft (hright.congr' (Eventually.of_forall (fun n => (hw n ψ hψ hc).symm)))

lemma wholeL2_tendsto_of_sq {f : ℕ → WholeL2} {f₀ : WholeL2}
    (hf : Tendsto (fun n => ∫ x,(f n x-f₀ x)^2) atTop (𝓝 0)) :
    Tendsto f atTop (𝓝 f₀) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have he (n : ℕ) : ‖f n-f₀‖^2=∫ x,(f n x-f₀ x)^2 := by
    rw [wholeL2_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (f n) f₀] with x hx
    rw [hx]
    rfl
  have hsq : Tendsto (fun n => ‖f n-f₀‖^2) atTop (𝓝 0) := by
    simpa only [he] using hf
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hh

lemma memLp_toLp_tendsto_of_sq {f : ℕ → R3 → ℝ} {f₀ : R3 → ℝ}
    (hm : ∀ n,MemLp (f n) 2 volume) (hm₀ : MemLp f₀ 2 volume)
    (hf : Tendsto (fun n => ∫ x,(f n x-f₀ x)^2) atTop (𝓝 0)) :
    Tendsto (fun n => (hm n).toLp (f n)) atTop (𝓝 (hm₀.toLp f₀)) := by
  apply wholeL2_tendsto_of_sq
  convert hf using 1
  ext n
  apply integral_congr_ae
  filter_upwards [(hm n).coeFn_toLp,hm₀.coeFn_toLp] with x hx hy
  rw [hx,hy]

end ScalarConductivity

end

end OAI
