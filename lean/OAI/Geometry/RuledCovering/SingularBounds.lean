import OAI.Geometry.RuledCovering.SingularField

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma plane_norm_sq (z : Plane) : ‖z‖^2 = z 0^2+z 1^2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg ‖z i‖))]
  simp [Fin.sum_univ_succ,Real.norm_eq_abs]

lemma plane_coordinate_le (z : Plane) (i : Fin 2) : |z i| ≤ ‖z‖ := by
  simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z i

lemma plane_norm_le_sum (z : Plane) : ‖z‖ ≤ |z 0|+|z 1| := by
  have h := plane_norm_sq z
  have h0 := abs_nonneg (z 0)
  have h1 := abs_nonneg (z 1)
  nlinarith [sq_abs (z 0),sq_abs (z 1)]

lemma singularField_homogeneous_bounds (p : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ z : Plane, 0 < z 1 → |z 0| ≤ 2*z 1 →
      ‖singularField p z‖ ≤ C*(z 1)^(p-1) ∧
      ‖fderiv ℝ (singularField p) z‖ ≤ C*(z 1)^(p-2) := by
  let S : Set Plane := (fun b : ℝ => vec2 b 1) '' Icc (-2 : ℝ) 2
  have hS : IsCompact S := isCompact_Icc.image (by unfold vec2; fun_prop)
  have hpos : ∀ z ∈ S, 0 < z 1 := by
    rintro z ⟨b,hb,rfl⟩
    norm_num [vec2]
  obtain ⟨C₁,hC₁⟩ := hS.exists_bound_of_continuousOn
    (fun z hz => (singularField_contDiffAt p (hpos z hz)).continuousAt.continuousWithinAt)
  obtain ⟨C₂,hC₂⟩ := hS.exists_bound_of_continuousOn
    (fun z hz => ((singularField_contDiffAt p (hpos z hz)).continuousAt_fderiv
      (by norm_num)).continuousWithinAt)
  refine ⟨max 1 (max C₁ C₂),le_max_left _ _,?_⟩
  intro z hz hcone
  let u := vec2 (z 0/z 1) 1
  have hu : u ∈ S := by
    refine ⟨z 0/z 1,?_,rfl⟩
    have ht : |z 0/z 1| ≤ 2 := by
      rw [abs_div,abs_of_pos hz,div_le_iff₀ hz]
      exact hcone
    exact abs_le.mp ht
  have hue : z 1 • u = z := by
    ext i
    fin_cases i <;> simp [u,vec2]
    field_simp
  have hf := singularField_smul p hz (z := u) (by norm_num [u,vec2])
  have hd := singularField_fderiv_smul p hz (z := u) (by norm_num [u,vec2])
  rw [hue] at hf hd
  constructor
  · rw [hf,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hz _)]
    calc
      _ ≤ (z 1)^(p-1)*C₁ := mul_le_mul_of_nonneg_left (hC₁ u hu) (by positivity)
      _ ≤ (z 1)^(p-1)*max 1 (max C₁ C₂) := mul_le_mul_of_nonneg_left
        ((le_max_left _ _).trans (le_max_right _ _)) (by positivity)
      _ = _ := mul_comm _ _
  · rw [hd,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hz _)]
    calc
      _ ≤ (z 1)^(p-2)*C₂ := mul_le_mul_of_nonneg_left (hC₂ u hu) (by positivity)
      _ ≤ (z 1)^(p-2)*max 1 (max C₁ C₂) := mul_le_mul_of_nonneg_left
        ((le_max_right _ _).trans (le_max_right _ _)) (by positivity)
      _ = _ := mul_comm _ _

lemma singularDomain_isCompact (p gamma c : ℝ) : IsCompact (singularDomain p gamma c) := by
  have hb : Continuous (fun z : Plane => z 0) := by fun_prop
  have hr : Continuous (fun z : Plane => z 1) := by fun_prop
  have hcap : Continuous (fun z : Plane => (1/2:ℝ)+c^2*ceilingPolynomial p (z 0)+c^(5/2:ℝ)) := by
    unfold ceilingPolynomial
    fun_prop
  have hclosed : IsClosed (singularDomain p gamma c) :=
    (isClosed_le continuous_const hr).inter ((isClosed_le hr continuous_const).inter
      ((isClosed_le hb.abs hr).inter (isClosed_le hr hcap)))
  apply (isCompact_closedBall (0 : Plane) 4).of_isClosed_subset hclosed
  intro z hz
  have hz0 : |z 0| ≤ 2 := hz.2.2.1.trans hz.2.1
  have hz1 : |z 1| ≤ 2 := (abs_of_nonneg ((abs_nonneg _).trans hz.2.2.1)).le.trans hz.2.1
  rw [Metric.mem_closedBall,dist_zero_right]
  exact (plane_norm_le_sum z).trans (by linarith)

lemma singularDomain_smoothNear (p gamma : ℝ) {c : ℝ} (hc : 0 < c) :
    SmoothNear ∞ (singularDomain p gamma c) (singularField p) := by
  refine ⟨{z | 0 < z 1},isOpen_lt continuous_const (by fun_prop),?_,singularField_contDiffOn p⟩
  intro z hz
  exact (Real.rpow_pos_of_pos hc gamma).trans_le hz.1

lemma singular_cutoff_small {p gamma : ℝ} (hpg : 0 < 1+gamma*(p-2)) :
    Tendsto (fun c : ℝ => c*(c^gamma)^(p-2)) (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto (fun c : ℝ => c^(1+gamma*(p-2))) (𝓝[>] 0)
      (𝓝 ((0:ℝ)^(1+gamma*(p-2)))) :=
    ((Real.continuous_rpow_const hpg.le).tendsto 0).mono_left nhdsWithin_le_nhds
  rw [Real.zero_rpow hpg.ne'] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with c hc
  have hc : 0 < c := hc
  rw [← Real.rpow_mul hc.le,Real.rpow_add hc,Real.rpow_one]

lemma singular_tip_small {gamma : ℝ} (hg : 1 < gamma) :
    Asymptotics.IsLittleO (𝓝[>] (0:ℝ)) (fun c : ℝ => (c^gamma)^2) (fun c => c^2) := by
  rw [Asymptotics.isLittleO_iff_tendsto']
  · have h : Tendsto (fun c : ℝ => c^(2*gamma-2)) (𝓝[>] 0)
        (𝓝 ((0:ℝ)^(2*gamma-2))) :=
      ((Real.continuous_rpow_const (show 0 ≤ 2*gamma-2 by linarith)).tendsto 0).mono_left nhdsWithin_le_nhds
    rw [Real.zero_rpow (by linarith : 2*gamma-2 ≠ 0)] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with c hc
    have hc : 0 < c := hc
    rw [← Real.rpow_natCast,← Real.rpow_mul hc.le,← Real.rpow_natCast,← Real.rpow_sub hc]
    congr 1
    ring
  · filter_upwards [self_mem_nhdsWithin] with c hc
    exact fun h => False.elim ((ne_of_gt (pow_pos hc 2)) h)

lemma vec2_coordinates (z : Plane) : vec2 (z 0) (z 1) = z := by
  ext i
  fin_cases i <;> rfl

lemma singular_wall_coefficient_bound (p : ℝ) {z : Plane}
    (hz : 0 < z 1) (hb : |z 0| ≤ 2*z 1) {e : ℝ} (he : |e| ≤ 1) :
    |(z 1/(1/2:ℝ))^(p-2)/2*((2-p)*(z 0/z 1)+e*p)| ≤
      ((2:ℝ)^(p-2)/2*(2*|2-p|+|p|))*(z 1)^(p-2) := by
  have hq : |z 0/z 1| ≤ 2 := by
    rw [abs_div,abs_of_pos hz,div_le_iff₀ hz]
    exact hb
  have ha : |(2-p)*(z 0/z 1)+e*p| ≤ 2*|2-p|+|p| := by
    calc
      _ ≤ |(2-p)*(z 0/z 1)|+|e*p| := abs_add_le _ _
      _ = |2-p| *|z 0/z 1|+|e| *|p| := by rw [abs_mul,abs_mul]
      _ ≤ |2-p| *2+1*|p| := add_le_add
        (mul_le_mul_of_nonneg_left hq (abs_nonneg _))
        (mul_le_mul_of_nonneg_right he (abs_nonneg _))
      _ = _ := by ring
  rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ (z 1/(1/2:ℝ))^(p-2)/2)]
  calc
    _ ≤ (z 1/(1/2:ℝ))^(p-2)/2*(2*|2-p|+|p|) :=
      mul_le_mul_of_nonneg_left ha (by positivity)
    _ = _ := by
      rw [show z 1/(1/2:ℝ)=2*z 1 by ring,Real.mul_rpow (by norm_num) hz.le]
      ring

lemma singular_uniform_bounds (p : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ z : Plane, 0 < z 1 → |z 0| ≤ 2*z 1 →
      ‖singularField p z‖ ≤ C*(z 1)^(p-1) ∧
      ‖fderiv ℝ (singularField p) z‖ ≤ C*(z 1)^(p-2) ∧
      ∀ e : ℝ, |e| ≤ 1 → |(z 1/(1/2:ℝ))^(p-2)/2*((2-p)*(z 0/z 1)+e*p)| ≤
        C*(z 1)^(p-2) := by
  obtain ⟨C,hC,hbound⟩ := singularField_homogeneous_bounds p
  let W := (2:ℝ)^(p-2)/2*(2*|2-p|+|p|)
  refine ⟨max C W,hC.trans (le_max_left _ _),?_⟩
  intro z hz hb
  obtain ⟨h0,h1⟩ := hbound z hz hb
  refine ⟨h0.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)),
    h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)),?_⟩
  intro e he
  exact (singular_wall_coefficient_bound p hz hb he).trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

end RuledApproximation

end

end OAI
