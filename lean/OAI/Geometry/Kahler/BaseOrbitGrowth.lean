import OAI.Geometry.Kahler.BaseHorizontalGeometry

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
namespace PinchedHartogs.BaseConstruction

lemma positive_log_growth {f : ℝ → ℝ} (hf : Differentiable ℝ f) (hp : ∀ t, 0 < f t)
    {K : ℝ} (hK : 0 ≤ K) (hd : ∀ t, |deriv f t| ≤ K*f t) (θ u : ℝ) :
    f (θ+u) ≤ Real.exp (K*|u|)*f θ := by
  let bound : NNReal := ⟨K,hK⟩
  have hlog : ∀ t, HasDerivAt (fun t => Real.log (f t)) (deriv f t/f t) t :=
    fun t => (hf t).hasDerivAt.log (hp t).ne'
  have hbound : ∀ t ∈ (univ : Set ℝ), ‖deriv (fun t => Real.log (f t)) t‖ ≤ bound := by
    intro t ht
    rw [(hlog t).deriv,Real.norm_eq_abs,abs_div,abs_of_pos (hp t)]
    exact (div_le_iff₀ (hp t)).mpr (hd t)
  have hh := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
    (fun t _ => (hlog t).differentiableAt) hbound (mem_univ θ) (mem_univ (θ+u))
  simp only [add_sub_cancel_left,Real.norm_eq_abs] at hh
  change |Real.log (f (θ+u))-Real.log (f θ)| ≤ K*|u| at hh
  have hb : Real.log (f (θ+u)) ≤ K*|u|+Real.log (f θ) := by linarith [le_abs_self (Real.log (f (θ+u))-Real.log (f θ))]
  have he := Real.exp_le_exp.mpr hb
  simpa only [Real.exp_add,Real.exp_log (hp (θ+u)),Real.exp_log (hp θ)] using he

lemma orbit_growth_nat {Q n N : ℕ} (hQ : 2 ≤ Q) {c K : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hK : 0 ≤ K) (hN : 2/c ≤ (2:ℝ)^N) (W : ℕ → ℝ → ℝ)
    (hzero : W 0 = fun _ => 1)
    (hpos : ∀ j ≤ n, ∀ θ, 0 < W j θ)
    (hdiff : ∀ j ≤ n, Differentiable ℝ (W j))
    (hder : ∀ j ≤ n, ∀ θ, |deriv (W j) θ| ≤ K*Q^j*W j θ)
    (hstep : ∀ j, j < n → ∀ θ, c*W j θ ≤ W (j+1) θ ∧ W (j+1) θ ≤ 2*W j θ)
    (θ u : ℝ) :
    W n (θ+u) ≤ Real.exp K*(2/c)*(max 1 ((Q:ℝ)^n*|u|))^N*W n θ := by
  have hQ0 : (0:ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hQ2 : (2:ℝ) ≤ Q := by exact_mod_cast hQ
  have hR : 1 ≤ 2/c := (le_div_iff₀ hc).mpr (by linarith)
  have hRQ : 2/c ≤ (Q:ℝ)^N := hN.trans (pow_le_pow_left₀ (by norm_num) hQ2 N)
  have hexp : 1 ≤ Real.exp K := Real.one_le_exp hK
  have hall : ∀ j ≤ n, W j (θ+u) ≤ Real.exp K*(2/c)*(max 1 ((Q:ℝ)^j*|u|))^N*W j θ := by
    intro j hj
    induction j with
    | zero =>
      rw [hzero]
      have hm : (1:ℝ) ≤ (max 1 ((Q:ℝ)^0*|u|))^N := one_le_pow₀ (le_max_left _ _)
      nlinarith [mul_le_mul_of_nonneg_left hR (Real.exp_pos K).le,
        mul_le_mul_of_nonneg_left hm (show 0 ≤ Real.exp K*(2/c) by positivity)]
    | succ j ih =>
      have hjn : j ≤ n := by omega
      have hjlt : j < n := by omega
      have hsθ := (hstep j hjlt θ).1
      have hsu := (hstep j hjlt (θ+u)).2
      have hwn : 0 < W (j+1) θ := hpos _ hj θ
      have hwp : 0 < W j θ := hpos _ hjn θ
      have hratio : W j θ ≤ (1/c)*W (j+1) θ := by
        have hh : W j θ ≤ W (j+1) θ / c := (le_div_iff₀ hc).mpr (by nlinarith)
        calc
          W j θ ≤ W (j+1) θ/c := hh
          _ = (1/c)*W (j+1) θ := by ring
      by_cases hsmall : (Q:ℝ)^j*|u| ≤ 1
      · have hg := positive_log_growth (hdiff j hjn) (hpos j hjn)
          (mul_nonneg hK (pow_nonneg hQ0.le _)) (hder j hjn) θ u
        have he : Real.exp (K*(Q:ℝ)^j*|u|) ≤ Real.exp K := by
          apply Real.exp_le_exp.mpr
          nlinarith
        have hg1 : W j (θ+u) ≤ Real.exp K*W j θ := hg.trans (mul_le_mul_of_nonneg_right he hwp.le)
        have hg2 : W (j+1) (θ+u) ≤ Real.exp K*(2/c)*W (j+1) θ := by
          have hm := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 2*Real.exp K by positivity)
          simp only [div_eq_mul_inv,one_mul] at hm ⊢
          nlinarith
        have hm : 1 ≤ (max 1 ((Q:ℝ)^(j+1)*|u|))^N := one_le_pow₀ (le_max_left _ _)
        have hmul := mul_le_mul_of_nonneg_left hm (show 0 ≤ Real.exp K*(2/c)*W (j+1) θ by positivity)
        nlinarith
      · have hpj : 1 < (Q:ℝ)^j*|u| := lt_of_not_ge hsmall
        have hcur : 1 ≤ (Q:ℝ)^(j+1)*|u| := by
          rw [pow_succ]
          nlinarith
        have hp : 0 ≤ ((Q:ℝ)^j*|u|)^N := pow_nonneg (by positivity) _
        have hi := ih hjn
        rw [max_eq_right hpj.le] at hi
        rw [max_eq_right hcur]
        have heq : ((Q:ℝ)^(j+1)*|u|)^N = (Q:ℝ)^N*((Q:ℝ)^j*|u|)^N := by
          rw [show (Q:ℝ)^(j+1)*|u| = (Q:ℝ)*((Q:ℝ)^j*|u|) by rw [pow_succ]; ring,mul_pow]
        rw [heq]
        have hm := mul_le_mul_of_nonneg_right hRQ hp
        have hm2 := mul_le_mul_of_nonneg_right hm (show 0 ≤ Real.exp K*(2/c)*W (j+1) θ by positivity)
        have hm3 := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 2*Real.exp K*(2/c)*((Q:ℝ)^j*|u|)^N by positivity)
        simp only [div_eq_mul_inv,one_mul] at hi hm2 hm3 ⊢
        nlinarith
  exact hall n le_rfl

end PinchedHartogs.BaseConstruction

end

end OAI
