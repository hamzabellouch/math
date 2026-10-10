import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.TranslationGates
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.UniformDerivatives

namespace OAI

noncomputable section
namespace VelocityDetection.SmoothBump
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators
open TranslationGates SpatialCalculus

def profile (s : ℝ) : ℝ := window (((3 : ℕ) : ℝ)*s)

@[fun_prop] theorem contDiff_profile : ContDiff ℝ ∞ profile := by unfold profile; fun_prop

theorem profile_bounds (s : ℝ) : profile s ∈ Icc (0:ℝ) 1 := by
  have h₁ := Real.smoothTransition.nonneg (3*s+3)
  have h₂ := Real.smoothTransition.nonneg (3-3*s)
  have h₃ := Real.smoothTransition.le_one (3*s+3)
  have h₄ := Real.smoothTransition.le_one (3-3*s)
  exact ⟨mul_nonneg h₁ h₂,(mul_le_mul h₃ h₄ h₂ (by norm_num)).trans_eq (by ring)⟩

theorem profile_zero {s : ℝ} (hs : 1 ≤ |s|) : profile s = 0 := by
  apply window_zero_outside
  simp only [Nat.cast_ofNat]
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<3)]
  linarith

@[simp] theorem profile_center : profile 0 = 1 := by
  apply window_one
  norm_num

theorem compactSupport_profile : HasCompactSupport profile := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc : IsCompact (Icc (-1:ℝ) 1))
  intro s hs
  have h := lt_of_not_ge (fun h => hs (profile_zero h))
  exact ⟨(abs_lt.mp h).1.le,(abs_lt.mp h).2.le⟩

theorem exists_second_bound : ∃ B : ℕ, 0 < B ∧ ∀ s : ℝ, |deriv (deriv profile) s| ≤ B := by
  obtain ⟨C,hC,h⟩ := UniformDerivatives.compact (I := Unit) contDiff_profile compactSupport_profile 2
  obtain ⟨B,hB⟩ := exists_nat_gt (max C 0)
  refine ⟨B,by exact_mod_cast (lt_of_le_of_lt (le_max_right C 0) hB),fun s => ?_⟩
  have hb := h () s
  simp only [norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_succ,iteratedDeriv_zero,
    Real.norm_eq_abs] at hb
  exact hb.trans ((le_max_left C 0).trans hB.le)

def bound : ℕ := exists_second_bound.choose

theorem bound_pos : 0 < bound := exists_second_bound.choose_spec.1

theorem second_bound (s : ℝ) : |deriv (deriv profile) s| ≤ bound :=
  exists_second_bound.choose_spec.2 s

def packet (R : ℝ) (X : Coord 2) : ℝ := profile (X 0/R)*profile (X 1/R)

@[fun_prop] theorem contDiff_packet (R : ℝ) : ContDiff ℝ ∞ (packet R) := by
  unfold packet
  fun_prop

theorem packet_bounds (R : ℝ) (X : Coord 2) : packet R X ∈ Icc (0:ℝ) 1 :=
  ⟨mul_nonneg (profile_bounds _).1 (profile_bounds _).1,
    (mul_le_mul (profile_bounds _).2 (profile_bounds _).2 (profile_bounds _).1 (by norm_num)).trans_eq (by ring)⟩

@[simp] theorem packet_center (R : ℝ) : packet R 0 = 1 := by simp [packet]

theorem packet_zero {R : ℝ} (hR : 0 < R) {X : Coord 2}
    (hX : ∃ i, R ≤ |X i|) : packet R X = 0 := by
  obtain ⟨i,hi⟩ := hX
  have hh : 1 ≤ |X i/R| := by rw [abs_div,abs_of_pos hR,le_div_iff₀ hR,one_mul]; exact hi
  fin_cases i
  · change 1 ≤ |X 0/R| at hh
    simp only [packet,profile_zero hh,zero_mul]
  · change 1 ≤ |X 1/R| at hh
    simp only [packet,profile_zero hh,mul_zero]

theorem compactSupport_packet {R : ℝ} (hR : 0 < R) : HasCompactSupport (packet R) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Coord 2) R)
  intro X hX
  rw [Metric.mem_closedBall,dist_zero_right,pi_norm_le_iff_of_nonneg hR.le]
  intro i
  exact (lt_of_not_ge (fun h => hX (packet_zero hR ⟨i,h⟩))).le

theorem spatialD_zero (R : ℝ) : spatialD 0 (fun _ X => packet R X) =
    fun _ X => (deriv profile (X 0/R)/R)*profile (X 1/R) := by
  funext t X
  change deriv (fun s => profile (s/R)*profile (X 1/R)) (X 0) = _
  have h := (((contDiff_profile.differentiable (by simp) (X 0/R)).hasDerivAt).comp (X 0)
    ((hasDerivAt_id (X 0)).div_const R)).mul_const (profile (X 1/R))
  simpa only [Function.comp_def,id_eq,div_eq_mul_inv,one_mul] using h.deriv

theorem spatialD_one (R : ℝ) : spatialD 1 (fun _ X => packet R X) =
    fun _ X => profile (X 0/R)*(deriv profile (X 1/R)/R) := by
  funext t X
  change deriv (fun s => profile (X 0/R)*profile (s/R)) (X 1) = _
  have h := (((contDiff_profile.differentiable (by simp) (X 1/R)).hasDerivAt).comp (X 1)
    ((hasDerivAt_id (X 1)).div_const R)).const_mul (profile (X 0/R))
  simpa only [Function.comp_def,id_eq,div_eq_mul_inv,one_mul] using h.deriv

theorem spatialD_zero_zero (R : ℝ) : spatialD 0 (spatialD 0 (fun _ X => packet R X)) =
    fun _ X => (deriv (deriv profile) (X 0/R)/R^2)*profile (X 1/R) := by
  rw [spatialD_zero]
  funext t X
  have hdiff : Differentiable ℝ (deriv profile) :=
    (contDiff_infty_iff_deriv.mp contDiff_profile).2.differentiable (by simp)
  change deriv (fun s => (deriv profile (s/R)/R)*profile (X 1/R)) (X 0) = _
  have h := ((((hdiff (X 0/R)).hasDerivAt).comp (X 0)
    ((hasDerivAt_id (X 0)).div_const R)).div_const R).mul_const (profile (X 1/R))
  convert! h.deriv using 1
  simp only [div_eq_mul_inv]
  ring

theorem spatialD_one_one (R : ℝ) : spatialD 1 (spatialD 1 (fun _ X => packet R X)) =
    fun _ X => profile (X 0/R)*(deriv (deriv profile) (X 1/R)/R^2) := by
  rw [spatialD_one]
  funext t X
  have hdiff : Differentiable ℝ (deriv profile) :=
    (contDiff_infty_iff_deriv.mp contDiff_profile).2.differentiable (by simp)
  change deriv (fun s => profile (X 0/R)*(deriv profile (s/R)/R)) (X 1) = _
  have h := ((((hdiff (X 1/R)).hasDerivAt).comp (X 1)
    ((hasDerivAt_id (X 1)).div_const R)).div_const R).const_mul (profile (X 0/R))
  convert! h.deriv using 1
  simp only [div_eq_mul_inv]
  ring

theorem laplacian_packet (R t : ℝ) (X : Coord 2) :
    laplacian (fun _ X => packet R X) t X =
      (deriv (deriv profile) (X 0/R)*profile (X 1/R)+
        profile (X 0/R)*deriv (deriv profile) (X 1/R))/R^2 := by
  simp only [laplacian,Fin.sum_univ_two,spatialD_zero_zero,spatialD_one_one]
  ring

theorem laplacian_bound {R : ℝ} (hR : 0 < R) (t : ℝ) (X : Coord 2) :
    |laplacian (fun _ X => packet R X) t X| ≤ 2*(bound:ℝ)/R^2 := by
  rw [laplacian_packet,abs_div,abs_of_pos (sq_pos_of_pos hR)]
  apply div_le_div_of_nonneg_right _ (sq_nonneg R)
  have hp (s : ℝ) : |profile s| ≤ 1 := by rw [abs_of_nonneg (profile_bounds s).1]; exact (profile_bounds s).2
  have h₁ := mul_le_mul (second_bound (X 0/R)) (hp (X 1/R)) (abs_nonneg _) (Nat.cast_nonneg bound)
  have h₂ := mul_le_mul (hp (X 0/R)) (second_bound (X 1/R)) (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
  have h := abs_add_le (deriv (deriv profile) (X 0/R)*profile (X 1/R))
    (profile (X 0/R)*deriv (deriv profile) (X 1/R))
  simp only [abs_mul] at h
  nlinarith

theorem eventually_packet_zero {R : ℝ} (hR : 0 < R) {X : Coord 2}
    (hX : ∃ i, R < |X i|) : packet R =ᶠ[𝓝 X] 0 := by
  obtain ⟨i,hi⟩ := hX
  have h : ∀ᶠ Y : Coord 2 in 𝓝 X, R < |Y i| :=
    (isOpen_lt continuous_const ((continuous_apply i).abs)).mem_nhds hi
  exact h.mono (fun X hX => packet_zero hR ⟨i,hX.le⟩)

theorem transport {R t : ℝ} (hR : 0 < R) {c : ℝ → Coord 2}
    (hc : Differentiable ℝ c) (a : VectorField 2)
    (hp : ∀ X, (∀ i, |X i-c t i| ≤ R) → a t X = deriv c t) (X : Coord 2) :
    deriv (fun r => packet R (X-c r)) t +
      advection a (fun r Y => packet R (Y-c r)) t X = 0 := by
  have hdiff := (contDiff_packet R).differentiable (by simp)
  have ht := (hdiff (X-c t)).hasFDerivAt.comp_hasDerivAt t ((hc t).hasDerivAt.const_sub X)
  have ha : advection a (fun r Y => packet R (Y-c r)) t X =
      fderiv ℝ (packet R) (X-c t) (a t X) := by
    rw [fderiv_apply_eq_sum hdiff]
    apply Finset.sum_congr rfl
    intro i _
    rw [congrFun (congrFun (spatialD_translate i (fun _ Y => packet R Y) c) t) X]
    rfl
  simp only [Function.comp_def] at ht
  rw [ht.deriv,ha]
  by_cases hX : ∀ i, |X i-c t i| ≤ R
  · rw [hp X hX,map_neg]
    ring
  · obtain ⟨i,hi⟩ := not_forall.mp hX
    have he := eventually_packet_zero hR (X := X-c t) ⟨i,lt_of_not_ge hi⟩
    rw [he.fderiv_eq]
    simp

end VelocityDetection.SmoothBump
end

end OAI
