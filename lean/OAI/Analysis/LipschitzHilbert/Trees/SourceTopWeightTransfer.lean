import OAI.Analysis.LipschitzHilbert.Estimates.TwoPointEnvelope

namespace OAI

/-! A top's reciprocal quadratic weight can be moved across a shorter
tile by spending one fixed power of packet decay. -/
noncomputable section
namespace LipschitzHilbert

theorem top_weight_base_transfer (a s L ell x v : ℝ)
    (hell : 0<ell) (hL : ell≤L) (hv : |v-s|≤ell) :
    1+((v-a)/L)^2≤6*(1+((x-a)/L)^2)*(1+((x-s)/ell)^2) := by
  have hLp : 0<L := hell.trans_le hL
  have hvs : |v-s|/L≤1 := (div_le_one hLp).mpr (hv.trans hL)
  have hxs : |x-s|/L≤|x-s|/ell :=
    div_le_div_of_nonneg_left (abs_nonneg _) hell hL
  have hdist : |(v-x)/L|≤1+|(x-s)/ell| := by
    rw [abs_div,abs_of_pos hLp]
    calc
      _ ≤ (|v-s|+|s-x|)/L := div_le_div_of_nonneg_right (abs_sub_le _ _ _) hLp.le
      _ = |v-s|/L+|x-s|/L := by rw [add_div,abs_sub_comm s x]
      _ ≤ 1+|x-s|/ell := add_le_add hvs hxs
      _ = _ := by rw [abs_div,abs_of_pos hell]
  have hs := pow_le_pow_left₀ (abs_nonneg _) hdist 2
  rw [sq_abs] at hs
  have hsq : 1+((v-x)/L)^2≤3*(1+((x-s)/ell)^2) := by
    nlinarith [sq_nonneg (|(x-s)/ell|-1),sq_abs ((x-s)/ell)]
  have ht := envelope_triangle_base x L v a
  have hrewrite : ((a-x)/L)^2=((x-a)/L)^2 := by rw [div_pow,div_pow,sub_sq_comm]
  rw [hrewrite] at ht
  have hm := mul_le_mul_of_nonneg_right hsq (by positivity : 0≤1+((x-a)/L)^2)
  nlinarith only [ht,hm]

theorem top_weight_envelope_transfer (a s L ell x v : ℝ)
    (hell : 0<ell) (hL : ell≤L) (hv : |v-s|≤ell) :
    lineEnvelope a L 1 x*lineEnvelope s ell 2 x≤
      6*lineEnvelope a L 1 v*lineEnvelope s ell 1 x := by
  let A := 1+((v-a)/L)^2
  let B := 1+((x-a)/L)^2
  let D := 1+((x-s)/ell)^2
  have hA : 0<A := by dsimp [A]; positivity
  have hB : 0<B := by dsimp [B]; positivity
  have hD : 0<D := by dsimp [D]; positivity
  have hbase : A≤6*B*D := top_weight_base_transfer a s L ell x v hell hL hv
  simp only [lineEnvelope,pow_one]
  change B⁻¹*(D^2)⁻¹≤6*A⁻¹*D⁻¹
  calc
    _ = 1/(B*D^2) := by field_simp
    _ ≤ 6/(A*D) := by
      apply (div_le_div_iff₀ (mul_pos hB (pow_pos hD 2)) (mul_pos hA hD)).mpr
      have hm := mul_le_mul_of_nonneg_right hbase hD.le
      nlinarith only [hm]
    _ = _ := by field_simp

end LipschitzHilbert

end

end OAI
