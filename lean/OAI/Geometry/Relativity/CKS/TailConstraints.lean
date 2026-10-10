import OAI.Geometry.Relativity.CKS.ConstructedOuterMetric

namespace OAI

noncomputable section
namespace CKSRealizedRound
noncomputable section
open Set Filter CKSCalculus CKSRound CKSBending CKSLocalBending
open scoped Topology ContDiff

lemma smooth_energy_residual {F a b : Point → ℝ} {v β : ℝ → ℝ} {x : Point} {ζ : ℝ}
    (hF : ContDiffAt ℝ 2 F x) (hv : ContDiffAt ℝ 2 v (x 0))
    (hβ : DifferentiableAt ℝ β (x 0))
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x)
    (hr : x 0 ≠ 0) (hs : Real.sin (x 1) ≠ 0) (hpos : 0 < radicand F v x)
    (hheat : D (basis 0) F x = ζ * (massJet F x).laplace (Real.sin (x 1)) (Real.cos (x 1)) /
      (2*x 0*A (v (x 0))) + 1/(x 0*Real.sqrt (x 0))) :
    (metricJet (lapse F v) x).energy (tensorJet (lapse F v) v (radial (normalEntry v β))
      (correctedComponent v a) (correctedComponent v b) x) =
      C (x 0) (lapse F v x) (v (x 0)) (deriv v (x 0)-v (x 0)/x 0)
        (β (x 0)) ζ ((massJet F x).laplace (Real.sin (x 1)) (Real.cos (x 1)))
        (a x) (b x/Real.sin (x 1)) (sphereGrad (massJet F x) (Real.sin (x 1))) := by
  have hlapse := (contDiffAt_lapse hF hv hr hpos).differentiableAt (by norm_num)
  rw [constructed_metricJet hF hv hr hs hpos,
    tensorJet_eq_round (lapse F v) v (radial (normalEntry v β))
      (correctedComponent v a) (correctedComponent v b) x hlapse (hv.differentiableAt (by norm_num))
      ((diffAt_normalEntry hv hβ hr).comp x (coord 0).differentiableAt)
      (diffAt_correctedComponent hv ha hr) (lapse_pos hpos).ne',
    lapseJet_eq_mass hF hv hr hpos,roundTensor_correction hv hβ ha hb hr]
  exact computed_energy_eq_residual (massJet F x) hr (lapse_pos hpos).ne' hs
    (by simpa [A,massJet] using lapse_sq hpos) hheat

end
end CKSRealizedRound

end

noncomputable section
namespace CKSBending
noncomputable section
open Set Filter
open scoped Topology ContDiff

lemma bendingV_tail_deriv {R r : ℝ} (hR : 0 < R) (hr : 2*R^2 < r) :
    deriv (bendingV R) r = 0 := by
  have hh : bendingV R =ᶠ[𝓝 r] (fun _ => 0) := by
    filter_upwards [eventually_gt_nhds hr] with y hy
    exact bendingV_tail hR hy.le
  rw [hh.deriv_eq]
  exact deriv_const _ _

lemma bendingBeta_tail {R r : ℝ} (hR : 12 ≤ R) (hr : 2*R^2 ≤ r) :
    bendingBeta R r = 0 := by
  apply beta_zero
  exact (le_div_iff₀ (by linarith : 0 < R)).mpr (by nlinarith)

lemma bendingZeta_tail {R r : ℝ} (hR : 12 ≤ R) (hr : 2*R^2 ≤ r) :
    bendingZeta R r = 1 := by
  apply zeta_one
  exact (le_div_iff₀ (by linarith : 0 < R)).mpr (by nlinarith)

lemma vanishing_tail_energy_bound {r u F M B Δ a b : ℝ} {grad : Vec2}
    (hr : 1 ≤ r) (hu : 0 < u) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hm : |F| ≤ M) (hR : 4*M ≤ r) (hmass : u^2 = A 0-2*F/r)
    (hΔ : |Δ| ≤ B) (hg : ‖grad‖ ≤ B) :
    |C r u 0 0 0 1 Δ a b grad| ≤ (2+4*M*B+12*B^2)/(r^3*Real.sqrt r) := by
  have hrp : 0 < r := by linarith
  have hl := (lapse_comparison hrp hm hR hmass).1
  have hi := inv_u_sq_le_two hu hl
  have hd := abs_reciprocal_difference hrp hu hm hl hmass
  have hd' : |1-1/u^2| ≤ 4*M/r := by simpa [A] using hd
  have hterm : |Δ/r^3*(1-1/u^2)| ≤ 4*M*B/r^4 := by
    rw [abs_mul,abs_div,abs_of_pos (pow_pos hrp _)]
    calc
      _ ≤ (B/r^3)*(4*M/r) := mul_le_mul (div_le_div_of_nonneg_right hΔ (pow_nonneg hrp.le _))
        hd' (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hg2 : ‖grad‖^2 ≤ B^2 := pow_le_pow_left₀ (norm_nonneg _) hg 2
  have hi2 : (1/u^2)^2 ≤ 4 := by
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 1/u^2) hi 2
    norm_num at hh ⊢
    exact hh
  have hgrad : 3*‖grad‖^2/(r^4*u^4) ≤ 12*B^2/r^4 := by
    calc
      _ = (3*‖grad‖^2/r^4)*(1/u^2)^2 := by ring
      _ ≤ (3*B^2/r^4)*4 := mul_le_mul (by gcongr) hi2 (sq_nonneg _) (by positivity)
      _ = _ := by ring
  have hs : Real.sqrt r ≤ r := (Real.sqrt_le_iff).mpr ⟨hrp.le,by nlinarith⟩
  have hp : 0 < r^3*Real.sqrt r := by positivity
  have hpoly : r^3*Real.sqrt r ≤ r^4 := by calc
    _ ≤ r^3*r := by gcongr
    _ = _ := by ring
  have hsum : |C r u 0 0 0 1 Δ a b grad| ≤
      2/(r^3*Real.sqrt r) + (4*M*B+12*B^2)/r^4 := by
    simp only [C,A,zero_pow (by decide : 2 ≠ 0),zero_mul,mul_zero,zero_div,
      add_zero,one_pow,div_one,zero_add,sub_zero]
    rw [add_div]
    obtain ⟨hlΔ,huΔ⟩ := abs_le.mp hterm
    have hpad : 0 ≤ 2/(r^3*Real.sqrt r) := by positivity
    have hgg : 0 ≤ 3*‖grad‖^2/(r^4*u^4) := by positivity
    have hmb : 0 ≤ 4*M*B/r^4 := by positivity
    have hbb : 0 ≤ 12*B^2/r^4 := by positivity
    apply abs_le.mpr
    constructor <;> linarith
  calc
    _ ≤ _ := hsum
    _ ≤ 2/(r^3*Real.sqrt r)+(4*M*B+12*B^2)/(r^3*Real.sqrt r) := by
      gcongr
    _ = _ := by ring

end
end CKSBending

end

end OAI
