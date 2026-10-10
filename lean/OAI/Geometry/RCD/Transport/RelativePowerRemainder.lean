import OAI.Geometry.RCD.Transport.TiltPowerVariation

namespace OAI

/-! # A power remainder estimate relative to a possibly small positive density -/

open Set Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

 theorem power_unit_remainder (q : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, |y-1| < δ →
      |y^q-1-q*(y-1)| ≤ ε*|y-1| := by
  have hd : HasDerivAt (fun y : ℝ => y^q) q 1 := by
    simpa only [Real.one_rpow,mul_one] using
      (Real.hasDerivAt_rpow_const (p := q) (Or.inl (one_ne_zero : (1:ℝ) ≠ 0)))
  obtain ⟨δ,hδ,hb⟩ := Metric.eventually_nhds_iff.mp (hd.isLittleO.bound hε)
  refine ⟨δ,hδ,fun y hy => ?_⟩
  have h := hb (by simpa only [Real.dist_eq] using hy)
  simpa only [Real.one_rpow,smul_eq_mul,Real.norm_eq_abs,mul_comm q] using h

 theorem relative_power_remainder {q ε δ B C r z v t : ℝ}
    (hε : 0 ≤ ε) (hr : 0 < r) (hz : 0 ≤ z)
    (hunit : ∀ y : ℝ, |y-1| < δ → |y^q-1-q*(y-1)| ≤ ε*|y-1|)
    (hv : |v| ≤ B*r) (he : |z-r-t*v| ≤ C*t^2*r)
    (ht : B*|t|+C*t^2 < δ) :
    |z^q-r^q-t*(q*r^(q-1)*v)| ≤
      (ε*(B*|t|+C*t^2)+|q| * C*t^2)*r^q := by
  let u := z/r
  let η := B*|t|+C*t^2
  have hdiff : |z-r| ≤ η*r := by
    calc
      _ = |t*v+(z-r-t*v)| := by congr 1; ring
      _ ≤ |t*v|+|z-r-t*v| := abs_add_le _ _
      _ ≤ |t| * (B*r)+C*t^2*r := by
        rw [abs_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left hv (abs_nonneg t)) he
      _ = _ := by dsimp [η]; ring
  have hu : |u-1| ≤ η := by
    have hu' : u-1=(z-r)/r := by dsimp [u]; field_simp
    rw [hu',abs_div,abs_of_pos hr]
    exact (div_le_iff₀ hr).mpr hdiff
  have huδ : |u-1| < δ := hu.trans_lt ht
  have hunit' := (hunit u huδ).trans (mul_le_mul_of_nonneg_left hu hε)
  have hrq : 0 ≤ r^q := Real.rpow_nonneg hr.le q
  have hrq' : 0 ≤ r^(q-1) := Real.rpow_nonneg hr.le _
  have hmul : r^(q-1)*r=r^q := by
    calc
      _ = r^(q-1)*r^(1:ℝ) := by rw [Real.rpow_one]
      _ = r^(q-1+1) := (Real.rpow_add hr _ _).symm
      _ = _ := by congr 1; ring
  have hzpow : z^q=r^q*u^q := by
    rw [←Real.mul_rpow hr.le (div_nonneg hz hr.le)]
    congr 1
    field_simp
  have hid : z^q-r^q-t*(q*r^(q-1)*v) =
      r^q*(u^q-1-q*(u-1))+(q*r^(q-1))*(z-r-t*v) := by
    rw [hzpow,←hmul]
    dsimp [u]
    field_simp
    ring
  rw [hid]
  calc
    _ ≤ |r^q*(u^q-1-q*(u-1))|+|(q*r^(q-1))*(z-r-t*v)| := abs_add_le _ _
    _ = r^q*|u^q-1-q*(u-1)|+(|q| * r^(q-1))*|z-r-t*v| := by
      rw [abs_mul,abs_mul,abs_mul,abs_of_nonneg hrq,abs_of_nonneg hrq']
    _ ≤ r^q*(ε*η)+(|q| * r^(q-1))*(C*t^2*r) :=
      add_le_add (mul_le_mul_of_nonneg_left hunit' hrq)
        (mul_le_mul_of_nonneg_left he (mul_nonneg (abs_nonneg q) hrq'))
    _ = r^q*(ε*η)+(|q| * C*t^2)*(r^(q-1)*r) := by ring
    _ = _ := by rw [hmul]; dsimp [η]; ring

end RegularPointCoordinates

end

end OAI
