import OAI.Geometry.RCD.Transport.RelativePowerRemainder

namespace OAI

/-! # Relative quadratic perturbations of the Boltzmann entropy density -/

open Set Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem entropy_unit_remainder {ε : ℝ} (hε : 0<ε) :
    ∃ δ : ℝ, 0<δ ∧ ∀ y : ℝ, |y-1|<δ →
      |y*Real.log y-(y-1)|≤ε*|y-1| := by
  have hd : HasDerivAt (fun y : ℝ => y*Real.log y) 1 1 := by
    convert! (hasDerivAt_id (1:ℝ)).mul (Real.hasDerivAt_log one_ne_zero) using 1
    simp
  obtain ⟨δ,hδ,hb⟩ := Metric.eventually_nhds_iff.mp (hd.isLittleO.bound hε)
  refine ⟨δ,hδ,fun y hy => ?_⟩
  have h := hb (by simpa only [Real.dist_eq] using hy)
  simpa only [Real.log_one,mul_zero,sub_zero,smul_eq_mul,one_mul,mul_one,Real.norm_eq_abs] using h

theorem entropy_density_scale {r z : ℝ} (hr : 0<r) (hz : 0≤z) :
    z*Real.log z=r*(z/r*Real.log (z/r))+(z)*Real.log r := by
  rcases eq_or_lt_of_le hz with h | h
  · simp only [←h,zero_div,zero_mul,mul_zero,add_zero]
  · rw [Real.log_div h.ne' hr.ne']
    field_simp
    ring

theorem relative_entropy_remainder {ε δ B C r z v t : ℝ}
    (hε : 0≤ε) (hr : 0<r) (hz : 0≤z)
    (hunit : ∀ y : ℝ, |y-1|<δ → |y*Real.log y-(y-1)|≤ε*|y-1|)
    (hv : |v|≤B*r) (he : |z-r-t*v|≤C*t^2*r)
    (ht : B*|t|+C*t^2<δ) :
    |z*Real.log z-r*Real.log r-t*((1+Real.log r)*v)|≤
      (ε*(B*|t|+C*t^2)+C*t^2)*r+C*t^2*|r*Real.log r| := by
  let u := z/r
  let η := B*|t|+C*t^2
  have hdiff : |z-r|≤η*r := by
    calc
      _ = |t*v+(z-r-t*v)| := by congr 1; ring
      _ ≤ |t*v|+|z-r-t*v| := abs_add_le _ _
      _ ≤ |t| * (B*r)+C*t^2*r := by
        rw [abs_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left hv (abs_nonneg t)) he
      _ = _ := by dsimp [η]; ring
  have hu : |u-1|≤η := by
    have heq : u-1=(z-r)/r := by dsimp [u]; field_simp
    rw [heq,abs_div,abs_of_pos hr]
    exact (div_le_iff₀ hr).mpr hdiff
  have hunit' := (hunit u (hu.trans_lt ht)).trans (mul_le_mul_of_nonneg_left hu hε)
  have hid : z*Real.log z-r*Real.log r-t*((1+Real.log r)*v)=
      r*(u*Real.log u-(u-1))+(1+Real.log r)*(z-r-t*v) := by
    rw [entropy_density_scale hr hz]
    dsimp [u]
    field_simp
    ring
  have habs : |1+Real.log r|≤1+|Real.log r| := by
    simpa only [abs_one] using abs_add_le (1:ℝ) (Real.log r)
  rw [hid]
  calc
    _ ≤ |r*(u*Real.log u-(u-1))|+|(1+Real.log r)*(z-r-t*v)| := abs_add_le _ _
    _ = r*|u*Real.log u-(u-1)|+|1+Real.log r| * |z-r-t*v| := by
      rw [abs_mul,abs_mul,abs_of_pos hr]
    _ ≤ r*(ε*η)+(1+|Real.log r|)*(C*t^2*r) :=
      add_le_add (mul_le_mul_of_nonneg_left hunit' hr.le)
        (mul_le_mul habs he (abs_nonneg _) (by positivity))
    _ = _ := by rw [abs_mul,abs_of_pos hr]; dsimp [η]; ring

end RegularPointCoordinates

end

end OAI
