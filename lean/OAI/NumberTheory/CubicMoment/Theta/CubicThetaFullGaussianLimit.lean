import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFullGaussianBound

namespace OAI

/-! The leading heat coefficient of the actual four-dimensional affine
lattice. The limit is independent of the upper-half-space point. -/
noncomputable section
open scoped Topology
open Filter
namespace CubicFirstMoment

lemma cubicThetaLatticeGaussianTail_tendsto_zero :
    Tendsto cubicThetaLatticeGaussianTail atTop (𝓝 0) := by
  apply cubicThetaLatticeGaussianTail_isBigO_exp.trans_tendsto
  have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    ((tendsto_id : Tendsto (fun x : ℝ => x) atTop atTop).atTop_mul_const
      (by norm_num : (0:ℝ)<1/2))
  simpa only [Function.comp_def,id_eq,neg_mul,div_eq_mul_inv,one_mul] using h

lemma cubicThetaLatticeGaussianTail_tendsto_div {c : ℝ} (hc : 0<c) :
    Tendsto (fun t : ℝ => cubicThetaLatticeGaussianTail (c/t)) (𝓝[>] 0) (𝓝 0) := by
  have h := cubicThetaLatticeGaussianTail_tendsto_zero.comp
    ((tendsto_inv_nhdsGT_zero : Tendsto (fun t : ℝ => t⁻¹) (𝓝[>] 0) atTop).const_mul_atTop hc)
  simpa only [Function.comp_def,div_eq_mul_inv] using h

lemma cubicThetaScalarGaussian_lead_product {v t : ℝ} (hv : 0<v) (ht : 0<t) :
    (2*Real.pi/(9*Real.sqrt 3*(t/v)))*(2*Real.pi/(9*Real.sqrt 3*(t*v)))=
      (4*Real.pi^2/243)/t^2 := by
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hs0 : Real.sqrt 3≠0 := by positivity
  field_simp
  nlinarith [hs]

theorem cubicThetaFullGaussian_leading {p : ℂ × ℝ} (hp : 0<p.2) :
    Tendsto (fun t : ℝ => t^2*cubicThetaFullGaussian p t) (𝓝[>] 0)
      (𝓝 (4*Real.pi^2/243)) := by
  let C := 4*Real.pi^2/243
  let T (t : ℝ) := cubicThetaLatticeGaussianTail (4*Real.pi^2/(27*(t/p.2)))
  let U (t : ℝ) := cubicThetaLatticeGaussianTail (4*Real.pi^2/(27*(t*p.2)))
  have hT : Tendsto T (𝓝[>] 0) (𝓝 0) := by
    have h := cubicThetaLatticeGaussianTail_tendsto_div
      (c:=4*Real.pi^2*p.2/27) (by positivity)
    convert h using 1
    ext t
    dsimp [T]
    congr 1
    field_simp
  have hU : Tendsto U (𝓝[>] 0) (𝓝 0) := by
    have h := cubicThetaLatticeGaussianTail_tendsto_div
      (c:=4*Real.pi^2/(27*p.2)) (by positivity)
    convert h using 1
    ext t
    dsimp [U]
    congr 1
    ring
  have hb : ∀ᶠ t : ℝ in 𝓝[>] 0,
      ‖t^2*cubicThetaFullGaussian p t-C‖≤C*(T t*(1+U t)+U t) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0<t at ht
    have he := cubicThetaFullGaussian_error hp ht
    rw [cubicThetaScalarGaussian_lead_product hp ht] at he
    have hm := mul_le_mul_of_nonneg_left he (sq_nonneg t)
    have hleft : t^2*|cubicThetaFullGaussian p t-C/t^2|=
        |t^2*cubicThetaFullGaussian p t-C| := by
      calc
        _ = |t^2| * |cubicThetaFullGaussian p t-C/t^2| := by
          rw [abs_of_nonneg (sq_nonneg t)]
        _ = |t^2*(cubicThetaFullGaussian p t-C/t^2)| := (abs_mul _ _).symm
        _ = _ := by
          congr 1
          field_simp [ht.ne']
    have hright : t^2*(C/t^2*(T t*(1+U t)+U t))=C*(T t*(1+U t)+U t) := by
      field_simp [ht.ne']
    rw [hleft,hright] at hm
    simpa only [Real.norm_eq_abs] using hm
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  change Tendsto (fun t : ℝ => ‖t^2*cubicThetaFullGaussian p t-C‖) (𝓝[>] 0) (𝓝 0)
  apply squeeze_zero' (Filter.Eventually.of_forall (fun t : ℝ => _root_.norm_nonneg (t^2*cubicThetaFullGaussian p t-C))) hb
  have h := (hT.mul ((tendsto_const_nhds (x:=(1:ℝ))).add hU)).add hU
  simpa only [zero_mul,add_zero,mul_zero] using h.const_mul C

end CubicFirstMoment

end

end OAI
