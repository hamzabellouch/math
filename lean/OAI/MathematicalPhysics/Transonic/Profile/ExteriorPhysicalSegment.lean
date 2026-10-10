import OAI.MathematicalPhysics.Transonic.Profile.PhysicalWindow
import OAI.MathematicalPhysics.Transonic.Shooting.ExteriorSegment

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorPolynomial
open Set SourceFamily AxisBarriers PhysicalExterior SonicShooting
open scoped ContDiff

def physicalSegment (p : Parameter) (d : ℝ) (u : ℝ → ℝ) (y : ℝ) : ℝ :=
  velocityToU y (sonicSpeed*u (coordinate (sonicRadius (ShootingParameters.beta p.val)) (d/256) y))

lemma sigma_nonneg (p : Parameter) : 0 ≤ sig p := by
  rw [← source_sigma p,sigma_eq_radius_sq (ne_of_gt (source_q_pos p))]
  exact sq_nonneg _

lemma window_physical_bounds {p : Parameter} {d a y : ℝ} {s : PowerSeries ℝ}
    (W : AdmissibleWindow (sig p) (kap p) d s) (ha : 0<a)
    (hy : y∈Icc (location (sonicRadius (ShootingParameters.beta p.val)) (d/256) a)
      (location (sonicRadius (ShootingParameters.beta p.val)) (d/256) 1)) :
    0<y ∧ |y|<1 := by
  have hb := ShootingParameters.standing_beta_bound p.property
  have hr := (source_parameter_bounds hb.1 hb.2).2.2.2.2.1
  have hh : 0<d/256 := div_pos W.dpos (by norm_num)
  have hl : 0<location (sonicRadius (ShootingParameters.beta p.val)) (d/256) a := by
    unfold location;exact mul_pos hr (by nlinarith [mul_pos hh ha])
  have hyp := hl.trans_le hy.1
  refine ⟨hyp,?_⟩
  rw [abs_of_pos hyp]
  exact hy.2.trans_lt (by simpa [location] using (window_endpoint W).2)

lemma physical_segment_den_ne {p : Parameter} {d a y : ℝ} {s : PowerSeries ℝ}
    (W : AdmissibleWindow (sig p) (kap p) d s) (ha : 0<a)
    {u : ℝ → ℝ} (hb : ∀ x∈Icc a 1, 1<u x ∧ u x<Real.sqrt (5/3))
    (hy : y∈Icc (location (sonicRadius (ShootingParameters.beta p.val)) (d/256) a)
      (location (sonicRadius (ShootingParameters.beta p.val)) (d/256) 1)) :
    profileDenom ell y (physicalSegment p d u y)≠0 := by
  let r := sonicRadius (ShootingParameters.beta p.val)
  let h := d/256
  let x := coordinate r h y
  have hbeta := ShootingParameters.standing_beta_bound p.property
  have hr : 0<r := (source_parameter_bounds hbeta.1 hbeta.2).2.2.2.2.1
  have hh : 0<h := div_pos W.dpos (by norm_num)
  have hx : x∈Icc a 1 := coordinate_mem hr hh hy
  have hur := hb x hx
  have hloc : r*(1+h*x)=y := location_coordinate (ne_of_gt hr) (ne_of_gt hh) y
  have hyp := window_physical_bounds W ha hy
  have hU := scaled_abs ⟨by linarith only [hur.1],hur.2⟩
  have hfa := sonic_exit_factors (r:=r) (z:=1+h*x) (p:=u x)
    (by rw [hloc];exact hyp.2) hU hur.1
  rw [hloc] at hfa
  have hqs : 1<Real.sqrt ell := by
    change 1<Real.sqrt (5/3)
    have he := Real.sq_sqrt (by norm_num : (0:ℝ)≤5/3)
    nlinarith only [he,Real.sqrt_nonneg (5/3:ℝ)]
  have hvr := abs_lt.mp (velocityToU_range hyp.2 hU)
  have hd := denominator_neg hqs hyp.1 hvr hfa.1 hfa.2 le_rfl ⟨hvr.1.le,le_rfl⟩
  rw [Real.sq_sqrt (by norm_num [ell] : (0:ℝ)≤ell)] at hd
  exact ne_of_lt hd

lemma source_chain_factor (p : Parameter) {h du : ℝ} (hh : h≠0) :
    sonicSpeed*(h*du*((1/sonicRadius (ShootingParameters.beta p.val))/h))=
      SepticProfile.q (ShootingParameters.beta p.val)/3*du := by
  rw [sonicRadius_eq]
  field_simp [ne_of_gt (source_q_pos p),ne_of_gt sonicSpeed_bounds.1]

lemma scaled_segment_derivative {p : Parameter} {d a y : ℝ} {s : PowerSeries ℝ}
    (W : AdmissibleWindow (sig p) (kap p) d s) {u : ℝ → ℝ}
    (hd : ∀ x∈Icc a 1, HasDerivWithinAt u (segmentField (sig p) (kap p) d (x,u x)) (Icc a 1) x)
    (hy : y∈Icc (location (sonicRadius (ShootingParameters.beta p.val)) (d/256) a)
      (location (sonicRadius (ShootingParameters.beta p.val)) (d/256) 1)) :
    let beta := ShootingParameters.beta p.val
    let r := sonicRadius beta
    let h := d/256
    let x := coordinate r h y
    let z := 1+h*x
    HasDerivWithinAt (fun y => sonicSpeed*u (coordinate r h y))
      (SepticProfile.q beta/3*(N (kap p) z (u x)/D (sig p) z (u x)))
      (Icc (location r h a) (location r h 1)) y := by
  dsimp only
  let r := sonicRadius (ShootingParameters.beta p.val)
  let h := d/256
  let x := coordinate r h y
  let J := Icc (location r h a) (location r h 1)
  have hbeta := ShootingParameters.standing_beta_bound p.property
  have hr : 0<r := (source_parameter_bounds hbeta.1 hbeta.2).2.2.2.2.1
  have hh : 0<h := div_pos W.dpos (by norm_num)
  have hx : x∈Icc a 1 := coordinate_mem hr hh hy
  have hmap : MapsTo (coordinate r h) J (Icc a 1) := fun _ ht => coordinate_mem hr hh ht
  have hc := ((hd x hx).comp y (coordinate_derivative r h y).hasDerivWithinAt hmap).const_mul sonicSpeed
  apply hc.congr_deriv
  dsimp only [segmentField]
  rw [mul_div_assoc]
  exact source_chain_factor p (ne_of_gt hh)

lemma physical_segment_derivative {p : Parameter} {d a y : ℝ} {s : PowerSeries ℝ}
    (W : AdmissibleWindow (sig p) (kap p) d s) (ha : 0<a)
    {u : ℝ → ℝ}
    (hb : ∀ x∈Icc a 1, 1<u x ∧ u x<Real.sqrt (5/3))
    (hd : ∀ x∈Icc a 1, HasDerivWithinAt u (segmentField (sig p) (kap p) d (x,u x)) (Icc a 1) x)
    (hy : y∈Icc (location (sonicRadius (ShootingParameters.beta p.val)) (d/256) a)
      (location (sonicRadius (ShootingParameters.beta p.val)) (d/256) 1)) :
    HasDerivWithinAt (physicalSegment p d u)
      (field ell (ShootingParameters.beta p.val) (y,physicalSegment p d u y))
      (Icc (location (sonicRadius (ShootingParameters.beta p.val)) (d/256) a)
        (location (sonicRadius (ShootingParameters.beta p.val)) (d/256) 1)) y := by
  let beta := ShootingParameters.beta p.val
  let r := sonicRadius beta
  let h := d/256
  let x := coordinate r h y
  let z := 1+h*x
  let J := Icc (location r h a) (location r h 1)
  have hbeta := ShootingParameters.standing_beta_bound p.property
  have hr : 0<r := (source_parameter_bounds hbeta.1 hbeta.2).2.2.2.2.1
  have hh : 0<h := div_pos W.dpos (by norm_num)
  have hx : x∈Icc a 1 := coordinate_mem hr hh hy
  have hur := hb x hx
  have hD : D (sig p) z (u x)≠0 :=
    ne_of_lt (window_D_neg W (sigma_nonneg p) ⟨ha.le.trans hx.1,hx.2⟩ hur.1)
  let du := N (kap p) z (u x)/D (sig p) z (u x)
  have huc := scaled_segment_derivative W hd hy
  have hnorm : normalizedDenom beta z (u x)*du=normalizedNumer beta z (u x) := by
    dsimp [normalizedDenom,normalizedNumer]
    rw [source_sigma p,source_kappa p]
    change D (sig p) z (u x)*(N (kap p) z (u x)/D (sig p) z (u x))=N (kap p) z (u x)
    exact mul_div_cancel₀ _ hD
  have hsonic := (normalized_equation_iff (ne_of_gt (source_q_pos p)) z (u x) du).mpr hnorm
  have hloc : r*z=y := location_coordinate (ne_of_gt hr) (ne_of_gt hh) y
  rw [hloc] at hsonic
  have hyp := window_physical_bounds W ha hy
  have hU := scaled_abs ⟨by linarith only [hur.1],hur.2⟩
  have hpole : 0<1-y*(sonicSpeed*u x) := by
    have hu := (abs_lt.mp hU).2
    have hy1 := (abs_lt.mp hyp.2).2
    nlinarith only [hy1,mul_nonneg hyp.1.le (sub_nonneg.mpr hu.le)]
  have hv := chart_within_derivative huc (ne_of_gt hpole)
  have heq := inverse_profile_equation (ne_of_gt hpole) hsonic
  apply hv.congr_deriv
  apply (eq_div_iff (physical_segment_den_ne W ha hb hy)).mpr
  exact (mul_comm _ _).trans heq

end SepticProfile.ExteriorPolynomial

end
end

end OAI
