import OAI.Geometry.RuledCovering.SingularBounds

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma inverse_in_closedBall {V : Plane → Plane} {q : Plane} {R k : ℝ} (hR : 0 ≤ R)
    (hcont : ∀ z ∈ Metric.closedBall q R, DifferentiableAt ℝ V z)
    (hsize : ∀ z ∈ Metric.closedBall q R, |k| *‖V z‖ ≤ R)
    (hder : ∀ z ∈ Metric.closedBall q R, |k| *‖fderiv ℝ V z‖ ≤ 1/2) :
    ∃ z ∈ Metric.closedBall q R, q = z+k • V z := by
  let S := Metric.closedBall q R
  let F : S → S := fun z => ⟨q-k • V z,by
    rw [Metric.mem_closedBall,dist_eq_norm,sub_sub_cancel_left,norm_neg,norm_smul,Real.norm_eq_abs]
    exact hsize z z.2⟩
  have hL : ContractingWith (1/2 : NNReal) F := by
    refine ⟨by norm_num,LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    have he := Convex.norm_image_sub_le_of_norm_fderiv_le
      (f := fun z => k • V z) (C := 1/2)
      (fun z hz => (hcont z hz).const_smul k)
      (fun z hz => by
        rw [fderiv_fun_const_smul (hcont z hz),norm_smul,Real.norm_eq_abs]
        exact hder z hz)
      (convex_closedBall q R) y.2 x.2
    change ‖(q-k • V x)-(q-k • V y)‖ ≤ (1/2)*‖(x:Plane)-(y:Plane)‖
    rw [sub_sub_sub_cancel_left,norm_sub_rev]
    exact he
  have : Nonempty S := ⟨⟨q,Metric.mem_closedBall_self hR⟩⟩
  have : IsClosed S := Metric.isClosed_closedBall
  let z := ContractingWith.fixedPoint F hL
  have hz := congrArg Subtype.val hL.fixedPoint_isFixedPt
  refine ⟨z,z.2,?_⟩
  change q-k • V z = z at hz
  exact (sub_eq_iff_eq_add.mp hz)

lemma singular_inverse_small {p : ℝ} (hp2 : p < 2) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (d c B T k : ℝ), 0 < d → 0 ≤ c →
      c*C*d^(p-2) ≤ 1/8 → 2*d ≤ T → T ≤ 1 → |B| ≤ T → |k| ≤ c →
      ∃ z : Plane, d ≤ z 1 ∧ z 1 ≤ 2 ∧ |z 0| ≤ z 1 ∧
        vec2 B T = z+k • singularField p z := by
  obtain ⟨C,hC,hbound⟩ := singular_uniform_bounds p
  refine ⟨C,hC,?_⟩
  intro d c B T k hd hc hsmall hT hT1 hB hk
  have hTp : 0 < T := by linarith
  have hCp : 0 ≤ C := by linarith
  have hball : ∀ z ∈ Metric.closedBall (vec2 B T) (T/4),
      d ≤ z 1 ∧ z 1 ≤ 5*T/4 ∧ |z 0| ≤ 2*z 1 := by
    intro z hz
    rw [Metric.mem_closedBall,dist_eq_norm] at hz
    have hr := (plane_coordinate_le (z-vec2 B T) 1).trans hz
    have hb := (plane_coordinate_le (z-vec2 B T) 0).trans hz
    change |z 1-T| ≤ T/4 at hr
    change |z 0-B| ≤ T/4 at hb
    obtain ⟨hrl,hru⟩ := abs_le.mp hr
    have hb' : |z 0| ≤ T/4+T := by
      calc
        _ = |(z 0-B)+B| := by congr 1; ring
        _ ≤ |z 0-B|+|B| := abs_add_le _ _
        _ ≤ T/4+T := add_le_add hb hB
    exact ⟨by linarith,by linarith,by linarith⟩
  have hprod : ∀ z ∈ Metric.closedBall (vec2 B T) (T/4), |k| * C*(z 1)^(p-2) ≤ 1/8 := by
    intro z hz
    have hz' := hball z hz
    have hzp : 0 < z 1 := hd.trans_le hz'.1
    calc
      _ ≤ c*C*(z 1)^(p-2) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hk hCp) (by positivity)
      _ ≤ c*C*d^(p-2) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hd hz'.1 (by linarith)) (mul_nonneg hc hCp)
      _ ≤ _ := hsmall
  obtain ⟨z,hz,heq⟩ := inverse_in_closedBall (V := singularField p)
    (k := k) (show 0 ≤ T/4 by positivity)
    (fun z hz => (singularField_contDiffAt p (hd.trans_le (hball z hz).1)).differentiableAt (by norm_num))
    (fun z hz => by
      have hz' := hball z hz
      have hzp := hd.trans_le hz'.1
      have hV := (hbound z hzp hz'.2.2).1
      calc
        _ ≤ |k| * (C*(z 1)^(p-1)) := mul_le_mul_of_nonneg_left hV (abs_nonneg _)
        _ = (|k| * C*(z 1)^(p-2))*z 1 := by
          rw [show p-1=p-2+1 by ring,Real.rpow_add_one hzp.ne']
          ring
        _ ≤ (1/8)*z 1 := mul_le_mul_of_nonneg_right (hprod z hz) hzp.le
        _ ≤ T/4 := by linarith)
    (fun z hz => by
      have hz' := hball z hz
      have hV := (hbound z (hd.trans_le hz'.1) hz'.2.2).2.1
      exact ((mul_le_mul_of_nonneg_left hV (abs_nonneg _)).trans
        (by simpa only [mul_assoc] using hprod z hz)).trans (by norm_num))
  have hz' := hball z hz
  have hzp := hd.trans_le hz'.1
  have htheta : ∀ e : ℝ, |e| ≤ 1 →
      0 < 1+k*((z 1/(1/2:ℝ))^(p-2)/2*((2-p)*(z 0/z 1)+e*p)) := by
    intro e he
    have ht := mul_le_mul_of_nonneg_left ((hbound z hzp hz'.2.2).2.2 e he) (abs_nonneg k)
    rw [← abs_mul] at ht
    have ht' : |k*((z 1/(1/2:ℝ))^(p-2)/2*((2-p)*(z 0/z 1)+e*p))| ≤ 1/8 := by
      exact ht.trans (by simpa only [mul_assoc] using hprod z hz)
    have := (abs_le.mp ht').1
    linarith
  have he0 := congrArg (fun w : Plane => w 0) heq
  have he1 := congrArg (fun w : Plane => w 1) heq
  change B = z 0+k*singularField p z 0 at he0
  change T = z 1+k*singularField p z 1 at he1
  have hw := singularField_wall p (b := z 0) hzp
  rw [vec2_coordinates] at hw
  have hwplus : T+B = (z 1+z 0)*(1+k*((z 1/(1/2:ℝ))^(p-2)/2*((2-p)*(z 0/z 1)+1*p))) := by
    calc
      _ = z 1+z 0+k*(singularField p z 1+singularField p z 0) := by rw [he0,he1]; ring
      _ = _ := by rw [hw.1]; ring
  have hwminus : T-B = (z 1-z 0)*(1+k*((z 1/(1/2:ℝ))^(p-2)/2*((2-p)*(z 0/z 1)+(-1)*p))) := by
    calc
      _ = z 1-z 0+k*(singularField p z 1-singularField p z 0) := by rw [he0,he1]; ring
      _ = _ := by rw [hw.2]; ring
  have hp0 : 0 ≤ z 1+z 0 := (mul_nonneg_iff_of_pos_right (htheta 1 (by norm_num))).mp
    (by rw [← hwplus]; linarith [(abs_le.mp hB).1])
  have hm0 : 0 ≤ z 1-z 0 := (mul_nonneg_iff_of_pos_right (htheta (-1) (by norm_num))).mp
    (by rw [← hwminus]; linarith [(abs_le.mp hB).2])
  exact ⟨z,hz'.1,by linarith [hz'.2.1],abs_le.mpr ⟨by linarith,by linarith⟩,heq⟩

end RuledApproximation

end

end OAI
