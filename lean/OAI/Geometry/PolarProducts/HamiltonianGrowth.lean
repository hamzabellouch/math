import OAI.Geometry.PolarProducts.HamiltonianODE

namespace OAI

universe u119 u120

section NonsqueezingInline

namespace HamiltonianGrowth
noncomputable section
open Set Filter
open scoped ContDiff Topology
open FourierPolynomial DiagonalQuadratic HamiltonianODE
variable {κ : Type u119} [Fintype κ]

 theorem contDiff_gradient {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (gradient H) :=
   (InnerProductSpace.toDual ℝ _).symm.toContinuousLinearEquiv.contDiff.comp
     (hH.fderiv_right (by simp))

 theorem gradient_translate {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) (p z : Vector κ) :
    gradient (fun w => H (w+p)) z = gradient H (z+p) := by
   apply HasGradientAt.gradient
   rw [hasGradientAt_iff_hasFDerivAt]
   have hh := ((hH.differentiable (by simp) (z+p)).hasGradientAt.hasFDerivAt).comp z
       ((hasFDerivAt_id z).add_const p)
   convert! hh using 1

 theorem energy_upper (d : κ → ℝ) (D : ℝ) (hd : ∀ j, d j ≤ D) (z : Vector κ) :
    energy d z ≤ D*‖z‖^2 := by
   simp only [energy, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
   exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hd j) (sq_nonneg _))

 theorem energy_sub_uniform (d : κ → ℝ) (η : ℝ) (z : Vector κ) :
    energy (fun j => d j-η) z = energy d z-η*‖z‖^2 := by
   simp only [energy, sub_mul, Finset.sum_sub_distrib, EuclideanSpace.norm_sq_eq, Finset.mul_sum]

 theorem quadratic_error {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) (h0 : H 0 = 0)
    (d : κ → ℝ) {B : ℝ} (hb : ∀ z, ‖gradient H z-(2 : ℝ) • diag d z‖ ≤ B) (z : Vector κ) :
    |H z-energy d z| ≤ B*‖z‖ := by
   have hr (w : Vector κ) : HasGradientAt (fun v => H v-energy d v)
       (gradient H w-(2 : ℝ) • diag d w) w := by
     rw [hasGradientAt_iff_hasFDerivAt]
     have hh := ((hH.differentiable (by simp) w).hasGradientAt.hasFDerivAt).sub
       (hasGradientAt_energy d w).hasFDerivAt
     convert! hh using 1
     ext v
     change inner (𝕜 := ℝ) (gradient H w-(2 : ℝ) • diag d w) v =
       inner (𝕜 := ℝ) (gradient H w) v-inner (𝕜 := ℝ) ((2 : ℝ) • diag d w) v
     exact inner_sub_left _ _ _
   have bound (w : Vector κ) : ‖fderiv ℝ (fun v => H v-energy d v) w‖ ≤ B := by
     rw [(hr w).hasFDerivAt.fderiv]
     simpa only [LinearIsometryEquiv.norm_map] using hb w
   have hm := (convex_univ : Convex ℝ (univ : Set (Vector κ))).norm_image_sub_le_of_norm_fderiv_le
     (fun w _ => (hr w).hasFDerivAt.differentiableAt) (fun w _ => bound w)
     (mem_univ (0 : Vector κ)) (mem_univ z)
   simpa [h0, energy] using hm

 theorem quartic_bound {H : Vector κ → ℝ} {A B r : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hr : 0 < r)
    (hz : ∀ z, ‖z‖ < r → H z = 0) (hu : ∀ z, H z ≤ A*‖z‖^2+B*‖z‖) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z, H z ≤ M*‖z‖^4 := by
   refine ⟨A/r^2+B/r^3, by positivity, ?_⟩
   intro z
   by_cases hzr : ‖z‖ < r
   · rw [hz z hzr]; positivity
   have hnr : r ≤ ‖z‖ := le_of_not_gt hzr
   have h2 : r^2*‖z‖^2 ≤ ‖z‖^4 := by
     have := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.le hnr 2) (sq_nonneg ‖z‖)
     nlinarith only [this]
   have h3 : r^3*‖z‖ ≤ ‖z‖^4 := by
     have := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.le hnr 3) (norm_nonneg z)
     nlinarith only [this]
   have ha : A*‖z‖^2 ≤ (A/r^2)*‖z‖^4 := by
     rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hr 2)]
     nlinarith only [mul_le_mul_of_nonneg_left h2 hA]
   have hb : B*‖z‖ ≤ (B/r^3)*‖z‖^4 := by
     rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hr 3)]
     nlinarith only [mul_le_mul_of_nonneg_left h3 hB]
   calc
     H z ≤ A*‖z‖^2+B*‖z‖ := hu z
     _ ≤ (A/r^2+B/r^3)*‖z‖^4 := by nlinarith only [ha,hb]

 theorem lower_bound {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) (h0 : H 0 = 0)
    (d : κ → ℝ) {B η : ℝ} (hη : 0 < η)
    (hb : ∀ z, ‖gradient H z-(2 : ℝ) • diag d z‖ ≤ B) (z : Vector κ) :
    energy (fun j => d j-η) z-B^2/(4*η) ≤ H z := by
   have he := (abs_le.mp (quadratic_error hH h0 d hb z)).1
   have hc : (4*η)*(B^2/(4*η)) = B^2 := by field_simp
   rw [energy_sub_uniform]
   nlinarith [sq_nonneg (2*η*‖z‖-B)]

 theorem bounded_remainder_translate {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H)
    (d : κ → ℝ) {B : ℝ} (hb : ∀ z, ‖gradient H z-(2 : ℝ) • diag d z‖ ≤ B)
    (p z : Vector κ) :
    ‖gradient (fun w => H (w+p)) z-(2 : ℝ) • diag d z‖ ≤ B+‖(2 : ℝ) • diag d p‖ := by
   rw [gradient_translate hH]
   have hd : diag d (z+p) = diag d z+diag d p := (diagCLM d).map_add z p
   have he : gradient H (z+p)-(2 : ℝ) • diag d z =
       (gradient H (z+p)-(2 : ℝ) • diag d (z+p))+(2 : ℝ) • diag d p := by
     rw [hd, smul_add]; abel
   rw [he]
   have hh := norm_add_le (gradient H (z+p)-(2 : ℝ) • diag d (z+p)) ((2 : ℝ) • diag d p)
   linarith [hb (z+p)]

 theorem bound_remainder_of_compact {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H)
    (d : κ → ℝ) {S : Set (Vector κ)} (hS : IsCompact S)
    (he : ∀ z ∉ S, gradient H z = (2 : ℝ) • diag d z) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z, ‖gradient H z-(2 : ℝ) • diag d z‖ ≤ B := by
   have hc : Continuous (fun z => gradient H z-(2 : ℝ) • diag d z) :=
     (contDiff_gradient hH).continuous.sub ((diagCLM d).continuous.const_smul (2 : ℝ))
   obtain ⟨B,hB⟩ := hS.exists_bound_of_continuousOn hc.continuousOn
   refine ⟨max B 0,le_max_right _ _,?_⟩
   intro z
   by_cases hz : z ∈ S
   · exact (hB z hz).trans (le_max_left _ _)
   · rw [he z hz, sub_self, norm_zero]
     exact le_max_right _ _

end
end HamiltonianGrowth

namespace HamiltonianPeriodic
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology
open FourierPolynomial DiagonalQuadratic HamiltonianODE HamiltonianGrowth
variable {κ : Type u120} [Fintype κ]

 def actionIntegral (H : Vector κ → ℝ) (x : ℝ → Vector κ) : ℝ :=
   ∫ t in (0:ℝ)..1, inner (𝕜 := ℝ) (gradient H (x t)) (x t)/2-H (x t)

 theorem integral_gradient_pairing {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H)
    {x : ℝ → Vector κ} (hx : ∀ t, HasDerivAt x (Complex.I • gradient H (x t)) t)
    (hp : x 1 = x 0) (p : Vector κ) :
    (∫ t in (0:ℝ)..1, inner (𝕜 := ℝ) (gradient H (x t)) p) = 0 := by
   have hc : Continuous x := continuous_iff_continuousAt.mpr (fun t => (hx t).continuousAt)
   have hi : IntervalIntegrable (fun t => inner (𝕜 := ℝ) (gradient H (x t)) p) volume 0 1 :=
     (((contDiff_gradient hH).continuous.comp hc).inner continuous_const).intervalIntegrable 0 1
   have hd (t : ℝ) : HasDerivAt (fun s => inner (𝕜 := ℝ) (x s) (Complex.I • p))
       (inner (𝕜 := ℝ) (gradient H (x t)) p) t := by
     simpa only [inner_zero_right, add_zero, zero_add, inner_I_I] using
       (hx t).inner ℝ (hasDerivAt_const t (Complex.I • p))
   have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
   simpa only [hp, sub_self] using he

 theorem action_translate {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) (p : Vector κ)
    {y : ℝ → Vector κ}
    (hy : ∀ t, HasDerivAt y (Complex.I • gradient (fun z => H (z+p)) (y t)) t)
    (hp : y 1 = y 0) :
    actionIntegral H (fun t => y t+p) = actionIntegral (fun z => H (z+p)) y := by
   have hc : Continuous y := continuous_iff_continuousAt.mpr (fun t => (hy t).continuousAt)
   have hxt (t : ℝ) : HasDerivAt (fun s => y s+p) (Complex.I • gradient H (y t+p)) t := by
     simpa only [gradient_translate hH] using (hy t).add_const p
   have hz := integral_gradient_pairing hH hxt (by simp only [hp]) p
   have hg : Continuous (fun t => gradient H (y t+p)) :=
     (contDiff_gradient hH).continuous.comp (hc.add continuous_const)
   have hi1 : IntervalIntegrable (fun t => inner (𝕜 := ℝ) (gradient H (y t+p)) (y t)/2-H (y t+p)) volume 0 1 :=
     (((hg.inner hc).div_const 2).sub (hH.continuous.comp (hc.add continuous_const))).intervalIntegrable _ _
   have hi2 : IntervalIntegrable (fun t => inner (𝕜 := ℝ) (gradient H (y t+p)) p/2) volume 0 1 :=
     ((hg.inner continuous_const).div_const 2).intervalIntegrable _ _
   unfold actionIntegral
   simp_rw [gradient_translate hH]
   have he (t : ℝ) : inner (𝕜 := ℝ) (gradient H (y t+p)) (y t+p)/2-H (y t+p) =
       (inner (𝕜 := ℝ) (gradient H (y t+p)) (y t)/2-H (y t+p))+
       inner (𝕜 := ℝ) (gradient H (y t+p)) p/2 := by rw [inner_add_right]; ring
   simp_rw [he]
   rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_div, hz, zero_div, add_zero]

end
end HamiltonianPeriodic

namespace HamiltonianPeriodic
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology
open FourierPolynomial DiagonalQuadratic HamiltonianODE HamiltonianGrowth
variable {κ : Type} [Fintype κ] [DecidableEq κ]

 theorem exists_positive_flat (j₀ : κ) {H : Vector κ → ℝ}
    (hH : ContDiff ℝ ∞ H) (hH0 : ∀ z, 0 ≤ H z)
    (hflat : ∀ᶠ z in 𝓝 (0 : Vector κ), H z = 0)
    (d : κ → ℝ) {η γ B D : ℝ}
    (hη : 0 < η) (hγ : 0 < γ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hd : ∀ j, 2*η ≤ d j) (hd0 : Real.pi+2*η ≤ d j₀) (hdD : ∀ j, |d j| ≤ D)
    (hgap : ∀ m : ℤ, ∀ j, γ ≤ |Real.pi*(m : ℝ)-d j|)
    (hrem : ∀ z, ‖gradient H z-(2 : ℝ) • diag d z‖ ≤ B) :
    ∃ x : ℝ → Vector κ, x 1 = x 0 ∧ 0 < actionIntegral H x ∧
      ∀ t : ℝ, HasDerivAt x (Complex.I • gradient H (x t)) t := by
   have h0 := hflat.self_of_nhds
   obtain ⟨r,hr,hzr⟩ := Metric.eventually_nhds_iff.mp hflat
   have hu (z : Vector κ) : H z ≤ D*‖z‖^2+B*‖z‖ := by
     have he := (abs_le.mp (quadratic_error hH h0 d hrem z)).2
     have hd' := energy_upper d D (fun j => (le_abs_self _).trans (hdD j)) z
     linarith
   obtain ⟨M,hM,hup⟩ := quartic_bound hD hB hr (fun z hz => hzr (by simpa only [dist_zero_right] using hz)) hu
   obtain ⟨x,ha,hx⟩ := exists_positive_periodic j₀ hH hH0 (fun j => d j-η) d hM hη hγ hB hD hup
     (fun j => by linarith [hd j]) (by linarith)
     (lower_bound hH h0 d hη hrem) hdD hgap hrem
   refine ⟨fun t => x (t : Time),?_,?_,hx⟩
   · simp only [AddCircle.coe_period, AddCircle.coe_zero]
   · change 0 < ∫ t in (0:ℝ)..1, (fun s : Time => inner (𝕜 := ℝ) (gradient H (x s)) (x s)/2-H (x s)) (t : Time)
     have he := intervalIntegral_eq_average (fun s : Time => inner (𝕜 := ℝ) (gradient H (x s)) (x s)/2-H (x s))
     exact he.symm ▸ ha

 theorem exists_positive_at_flat_point (j₀ : κ) {H : Vector κ → ℝ}
    (hH : ContDiff ℝ ∞ H) (hH0 : ∀ z, 0 ≤ H z) (p : Vector κ)
    (hflat : ∀ᶠ z in 𝓝 p, H z = 0)
    (d : κ → ℝ) {η γ B D : ℝ}
    (hη : 0 < η) (hγ : 0 < γ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hd : ∀ j, 2*η ≤ d j) (hd0 : Real.pi+2*η ≤ d j₀) (hdD : ∀ j, |d j| ≤ D)
    (hgap : ∀ m : ℤ, ∀ j, γ ≤ |Real.pi*(m : ℝ)-d j|)
    (hrem : ∀ z, ‖gradient H z-(2 : ℝ) • diag d z‖ ≤ B) :
    ∃ x : ℝ → Vector κ, x 1 = x 0 ∧ 0 < actionIntegral H x ∧
      ∀ t : ℝ, HasDerivAt x (Complex.I • gradient H (x t)) t := by
   have ht : ContDiff ℝ ∞ (fun z : Vector κ => H (z+p)) := hH.comp (contDiff_id.add contDiff_const)
   have hz : ∀ᶠ z in 𝓝 (0 : Vector κ), H (z+p) = 0 := by
     have hc : Tendsto (fun z : Vector κ => z+p) (𝓝 0) (𝓝 p) := by
       have hc : Continuous (fun z : Vector κ => z+p) := continuous_id.add continuous_const
       have hc0 : Tendsto (fun z : Vector κ => z+p) (𝓝 0) (𝓝 ((0 : Vector κ)+p)) := hc.continuousAt
       simpa only [zero_add] using hc0
     exact hc.eventually hflat
   obtain ⟨y,hp,ha,hy⟩ := exists_positive_flat j₀ ht (fun z => hH0 (z+p)) hz d hη hγ
     (add_nonneg hB (norm_nonneg _)) hD hd hd0 hdD hgap (bounded_remainder_translate hH d hrem p)
   refine ⟨fun t => y t+p,by simp only [hp],?_,?_⟩
   · rw [action_translate hH p hy hp]
     exact ha
   · intro t
     simpa only [gradient_translate hH] using (hy t).add_const p

end
end HamiltonianPeriodic

end NonsqueezingInline

end OAI
