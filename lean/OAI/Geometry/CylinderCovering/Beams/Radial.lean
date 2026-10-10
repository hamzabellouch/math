import OAI.Geometry.CylinderCovering.Radial.SweepDefinitions
import OAI.Geometry.CylinderCovering.Beams.Coverage
import OAI.Geometry.CylinderCovering.Beams.Cost

namespace OAI

open Set
open scoped InnerProductSpace
noncomputable section
namespace ShortenedBeam

private theorem beam_inner_coord (u v : Space) :
    inner ℝ u v = u 0*v 0+u 1*v 1+u 2*v 2 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]
  ring

lemma velocity_hasDerivAt (a p : ℝ) :
    HasDerivAt (velocity a)
      ((-2*a*(2-a)) • (point 0 1 0 + p • point 1 (-1) 0)) p := by
  have hf := (CylinderCovering.BeamAlgebra.hasDerivAt_velocity_first a (2-a) p).smul_const
    (point 1 0 0)
  have hg := (CylinderCovering.BeamAlgebra.hasDerivAt_velocity_second a (2-a) p).smul_const
    (point 0 1 0)
  convert hf.add hg using 1
  all_goals first
    | rfl
    | (funext r; ext i; fin_cases i <;> simp [velocity, point] <;> ring)
    | (ext i; fin_cases i <;> simp [point] <;> ring)

lemma beam_vectors_independent :
    LinearIndependent ℝ ![point 0 1 0, point 1 (-1) 0] := by
  apply linearIndependent_fin2.mpr
  constructor
  · intro h
    have h0 := congrArg (fun z : Space => z 0) h
    simp [point] at h0
  · intro r hr
    have h0 := congrArg (fun z : Space => z 0) hr
    have h1 := congrArg (fun z : Space => z 1) hr
    simp [point] at h0 h1
    subst r
    norm_num at h1
    have : 0 < Real.sqrt (2:ℝ) := by positivity
    linarith

def radialData (a : ℝ) (ha : a ≤ 2) : CylinderCovering.RadialSweep.Data where
  e := point 0 0 1
  a := point 0 1 0
  b := point 1 (-1) 0
  p₀ := point (-1) (-1) 0
  α := 0
  β := 1
  L := 1
  R := fun _ => 2-a
  lam := fun _ => -2*a*(2-a)
  w := velocity a
  interval_nonempty := by norm_num
  length_pos := by norm_num
  normal_unit := by simp [point, EuclideanSpace.norm_eq, Fin.sum_univ_three]
  a_perp := by simp [beam_inner_coord, point]
  b_perp := by simp [beam_inner_coord, point]
  origin_perp := by simp [beam_inner_coord, point]
  independent := beam_vectors_independent
  cap_continuous := continuousOn_const
  cap_nonneg := by intro p hp; linarith
  scalar_continuous := continuousOn_const
  velocity_continuous := by
    have h : Continuous (velocity a) := by unfold velocity point; fun_prop
    exact h.continuousOn
  velocity_perp := by intro p hp; simp [velocity, beam_inner_coord, point]
  aligned := by intro p hp; exact (velocity_hasDerivAt a p).hasDerivWithinAt

lemma point_inner (x y t u v s : ℝ) :
    inner ℝ (point x y t) (point u v s) = (x*u+y*v)/2+t*s := by
  rw [beam_inner_coord]
  change x / Real.sqrt 2 * (u / Real.sqrt 2) +
    y / Real.sqrt 2 * (v / Real.sqrt 2) + t*s = _
  have hsqrt : Real.sqrt 2 * Real.sqrt 2 = (2:ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  rw [div_mul_div_comm, div_mul_div_comm, hsqrt]
  ring

lemma radialData_kappa (a : ℝ) (ha : a ≤ 2) :
    CylinderCovering.RadialSweep.kappa (radialData a ha) = 1/2 := by
  simp only [CylinderCovering.RadialSweep.kappa, radialData, point_inner]
  norm_num

lemma radial_point_eq (a p h t : ℝ) :
    point (-1) (-1) 0 + h • (point 0 1 0 + p • point 1 (-1) 0) +
      t • (point 0 0 1 + velocity a p) =
    point (-1+h*p+t*(1-a*(2-a)*p^2))
      (-1+h*(1-p)+t*(-1+a*(2-a)*(1-p)^2)) t := by
  ext i
  fin_cases i <;> simp [velocity, point] <;> ring

lemma radialData_sweep (a : ℝ) (ha : a ≤ 2) :
    CylinderCovering.RadialSweep.sweep (radialData a ha) = beamMinus a := by
  ext z
  constructor
  · rintro ⟨p,hp,h,hh,t,ht,hz⟩
    change z = point (-1) (-1) 0 + h • (point 0 1 0 + p • point 1 (-1) 0) +
      t • (point 0 0 1 + velocity a p) at hz
    rw [radial_point_eq] at hz
    refine ⟨_,_,t,ht,?_,hz⟩
    exact ⟨p,h,hp.1,hp.2,hh.1,hh.2,rfl,rfl⟩
  · rintro ⟨x,y,t,ht,⟨p,h,hp0,hp1,hh0,hh1,hx,hy⟩,hz⟩
    refine ⟨p,⟨hp0,hp1⟩,h,⟨hh0,hh1⟩,t,ht,?_⟩
    change z = point (-1) (-1) 0 + h • (point 0 1 0 + p • point 1 (-1) 0) +
      t • (point 0 0 1 + velocity a p)
    rw [radial_point_eq, ← hx, ← hy]
    exact hz

def radialDataPlus (a : ℝ) (ha : a ≤ 2) : CylinderCovering.RadialSweep.Data where
  e := point 0 0 1
  a := -point 0 1 0
  b := -point 1 (-1) 0
  p₀ := -point (-1) (-1) 0
  α := 0
  β := 1
  L := 1
  R := fun _ => 2-a
  lam := fun _ => -2*a*(2-a)
  w := fun p => -velocity a p
  interval_nonempty := by norm_num
  length_pos := by norm_num
  normal_unit := by simp [point, EuclideanSpace.norm_eq, Fin.sum_univ_three]
  a_perp := by simp [beam_inner_coord, point]
  b_perp := by simp [beam_inner_coord, point]
  origin_perp := by simp [beam_inner_coord, point]
  independent := by
    have heq : ![-point 0 1 0, -point 1 (-1) 0] = -![point 0 1 0, point 1 (-1) 0] := by
      ext i
      fin_cases i <;> rfl
    rw [heq]
    exact beam_vectors_independent.neg
  cap_continuous := continuousOn_const
  cap_nonneg := by intro p hp; linarith
  scalar_continuous := continuousOn_const
  velocity_continuous := by
    have h : Continuous (fun p => -velocity a p) := by unfold velocity point; fun_prop
    exact h.continuousOn
  velocity_perp := by intro p hp; simp [velocity, beam_inner_coord, point]
  aligned := by
    intro p hp
    convert (velocity_hasDerivAt a p).neg.hasDerivWithinAt (s := Icc (0:ℝ) 1) using 1
    all_goals first | rfl | (simp only [smul_neg, smul_add, neg_add])

lemma radialDataPlus_kappa (a : ℝ) (ha : a ≤ 2) :
    CylinderCovering.RadialSweep.kappa (radialDataPlus a ha) = 1/2 := by
  simp only [CylinderCovering.RadialSweep.kappa, radialDataPlus, inner_neg_neg, point_inner]
  norm_num

lemma radial_point_plus_eq (a p h t : ℝ) :
    -point (-1) (-1) 0 + h • (-point 0 1 0 + p • -point 1 (-1) 0) +
      t • (point 0 0 1 - velocity a p) =
    point (-(-1+h*p+t*(1-a*(2-a)*p^2)))
      (-(-1+h*(1-p)+t*(-1+a*(2-a)*(1-p)^2))) t := by
  ext i
  fin_cases i <;> simp [velocity, point] <;> ring

lemma radialDataPlus_sweep (a : ℝ) (ha : a ≤ 2) :
    CylinderCovering.RadialSweep.sweep (radialDataPlus a ha) = beamPlus a := by
  ext z
  constructor
  · rintro ⟨p,hp,h,hh,t,ht,hz⟩
    change z = -point (-1) (-1) 0 + h • (-point 0 1 0 + p • -point 1 (-1) 0) +
      t • (point 0 0 1 - velocity a p) at hz
    rw [radial_point_plus_eq] at hz
    refine ⟨_,_,t,ht,?_,hz⟩
    refine ⟨p,h,hp.1,hp.2,hh.1,hh.2,?_,?_⟩ <;> simp
  · rintro ⟨x,y,t,ht,⟨p,h,hp0,hp1,hh0,hh1,hx,hy⟩,hz⟩
    refine ⟨p,⟨hp0,hp1⟩,h,⟨hh0,hh1⟩,t,ht,?_⟩
    change z = -point (-1) (-1) 0 + h • (-point 0 1 0 + p • -point 1 (-1) 0) +
      t • (point 0 0 1 - velocity a p)
    rw [radial_point_plus_eq, ← hx, ← hy, neg_neg, neg_neg]
    exact hz

lemma radialDataPlus_weightedArea (a : ℝ) (ha : a ≤ 2) :
    CylinderCovering.RadialSweep.weightedArea (radialDataPlus a ha) =
      CylinderCovering.RadialSweep.weightedArea (radialData a ha) := by
  unfold CylinderCovering.RadialSweep.weightedArea
  rw [radialDataPlus_kappa, radialData_kappa]
  simp only [radialDataPlus, radialData, norm_neg]

lemma velocity_norm_sq (a p : ℝ) :
    ‖velocity a p‖^2 =
      ((1-a*(2-a)*p^2)^2+(-1+a*(2-a)*(1-p)^2)^2)/2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [velocity, point_inner]
  ring

lemma radialData_scalarBound {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 2) :
    CylinderCovering.RadialSweep.scalarBound (radialData a ha') = 2*a*(2-a) := by
  have hN : 0 ≤ 2-a := by linarith
  have hneg : -2*a*(2-a) ≤ 0 := by nlinarith
  unfold CylinderCovering.RadialSweep.scalarBound
  change sSup ((fun _ : ℝ => |-2*a*(2-a)|) '' Icc (0:ℝ) 1) = _
  have him : ((fun _ : ℝ => |-2*a*(2-a)|) '' Icc (0:ℝ) 1) = {|-2*a*(2-a)|} := by
    ext z
    constructor
    · rintro ⟨p,hp,rfl⟩
      rfl
    · rintro rfl
      exact ⟨0,by norm_num,rfl⟩
  rw [him, csSup_singleton, abs_of_nonpos hneg]
  ring

lemma radialData_radialError {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 2) :
    CylinderCovering.RadialSweep.radialError (radialData a ha') = 2*a*(2-a) := by
  unfold CylinderCovering.RadialSweep.radialError
  rw [radialData_scalarBound ha ha']
  change 1*(2*a*(2-a)) = _
  ring

lemma radialData_collar {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 2) :
    CylinderCovering.RadialSweep.collar (radialData a ha') = 6*a*(2-a)+1 := by
  unfold CylinderCovering.RadialSweep.collar
  rw [radialData_radialError ha ha']
  ring

lemma beam_denominator_identity (a p : ℝ) :
    1+‖velocity a p‖^2 = 2*(1-a*(2-a)*(p^2+(1-p)^2)/2 +
      a^2*(2-a)^2*(p^4+(1-p)^4)/4) := by
  rw [velocity_norm_sq]
  ring

lemma radialData_direction (a p : ℝ) (ha : a ≤ 2) :
    CylinderCovering.RadialSweep.direction (radialData a ha) p = axisMinus a p := rfl

lemma radialDataPlus_direction (a p : ℝ) (ha : a ≤ 2) :
    CylinderCovering.RadialSweep.direction (radialDataPlus a ha) p = axisPlus a p := rfl

lemma radialData_weightedArea (a : ℝ) (ha : a ≤ 2) :
    CylinderCovering.RadialSweep.weightedArea (radialData a ha) =
      (Real.sqrt 2/8)*CylinderCovering.BeamCost.beamCost a := by
  unfold CylinderCovering.RadialSweep.weightedArea
  rw [radialData_kappa]
  change (1/2:ℝ)*(∫ p in (0:ℝ)..1, (2-a)^2/(2*Real.sqrt (1+‖velocity a p‖^2))) = _
  have hfunc : (fun p : ℝ => (2-a)^2/(2*Real.sqrt (1+‖velocity a p‖^2))) =
      (fun p => ((2-a)^2/(2*Real.sqrt 2))*CylinderCovering.BeamCost.beamDensity a p) := by
    funext p
    rw [← CylinderCovering.BeamCost.beamDensity_physical a p, ← velocity_norm_sq]
    have htwo : Real.sqrt (2:ℝ) ≠ 0 := by positivity
    have hden : Real.sqrt (1+‖velocity a p‖^2) ≠ 0 := by positivity
    field_simp
  rw [hfunc, intervalIntegral.integral_const_mul]
  unfold CylinderCovering.BeamCost.beamCost
  have hunit : (1:ℝ)/(4*Real.sqrt 2) = Real.sqrt 2/8 := by
    have htwo : Real.sqrt (2:ℝ) ≠ 0 := by positivity
    field_simp
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  calc
    (1/2:ℝ)*((2-a)^2/(2*Real.sqrt 2)*(∫ p in (0:ℝ)..1,
        CylinderCovering.BeamCost.beamDensity a p)) =
      (1/(4*Real.sqrt 2))*(2-a)^2*(∫ p in (0:ℝ)..1,
        CylinderCovering.BeamCost.beamDensity a p) := by ring
    _ = (Real.sqrt 2/8)*((2-a)^2*(∫ p in (0:ℝ)..1,
        CylinderCovering.BeamCost.beamDensity a p)) := by rw [hunit]; ring

lemma radialData_total_weightedArea (a : ℝ) (ha : a ≤ 2) :
    CylinderCovering.RadialSweep.weightedArea (radialData a ha) +
      CylinderCovering.RadialSweep.weightedArea (radialDataPlus a ha) =
      (Real.sqrt 2/4)*CylinderCovering.BeamCost.beamCost a := by
  rw [radialDataPlus_weightedArea, radialData_weightedArea]
  ring

private lemma constant_capMax (c : ℝ) {N : ℕ} (hN : 0 < N) (i : Fin N) :
    CylinderCovering.RadialRiemann.capMax (fun _ => c) 0 1 N i = c := by
  have hNreal : (0:ℝ) < N := by exact_mod_cast hN
  have hstep : 0 < CylinderCovering.RadialRiemann.step 0 1 N := by
    unfold CylinderCovering.RadialRiemann.step
    positivity
  have hcell : (CylinderCovering.RadialRiemann.cell 0 1 N i).Nonempty := by
    refine ⟨CylinderCovering.RadialRiemann.point 0 1 N i, le_rfl, ?_⟩
    unfold CylinderCovering.RadialRiemann.point
    push_cast
    nlinarith
  unfold CylinderCovering.RadialRiemann.capMax
  have him : ((fun _ : ℝ => c) '' CylinderCovering.RadialRiemann.cell 0 1 N i) = {c} := by
    ext z
    constructor
    · rintro ⟨p,hp,rfl⟩
      rfl
    · rintro rfl
      obtain ⟨p,hp⟩ := hcell
      exact ⟨p,hp,rfl⟩
  rw [him, csSup_singleton]

lemma radialData_frozenArea {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 2)
    {N : ℕ} (hN : 0 < N) (tag : Fin N → ℝ) (i : Fin N) :
    CylinderCovering.RadialSweep.frozenArea (radialData a ha') N tag i =
      (1/(N:ℝ))*((2-a)+(8*a*(2-a)+1)/(N:ℝ))^2 /
        (4*Real.sqrt (1+‖velocity a (tag i)‖^2)) := by
  unfold CylinderCovering.RadialSweep.frozenArea
  rw [radialData_kappa, radialData_radialError ha ha', radialData_collar ha ha']
  change (1/2:ℝ)*CylinderCovering.RadialRiemann.step 0 1 N *
    (CylinderCovering.RadialRiemann.capMax (fun _ => 2-a) 0 1 N i +
      (2*a*(2-a)+(6*a*(2-a)+1))*CylinderCovering.RadialRiemann.step 0 1 N)^2 /
      (2*Real.sqrt (1+‖velocity a (tag i)‖^2)) = _
  rw [constant_capMax (2-a) hN i]
  unfold CylinderCovering.RadialRiemann.step
  norm_num only [sub_zero]
  ring

end ShortenedBeam

end

end OAI
