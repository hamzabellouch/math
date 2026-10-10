import OAI.Analysis.CircleDomains.Rigidity.QuarterFluxIntegrability

namespace OAI

/-! The sum of the two axial endpoint integrals is exactly circle flux
for bounded measurable boundary values. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def horizontalCircleIncrement (F : ℂ → ℂ) (c : ℂ) (r y : ℝ) : ℝ :=
    (F (horizontalCirclePoint true c r y)).re-(F (horizontalCirclePoint false c r y)).re
 def verticalCircleIncrement (F : ℂ → ℂ) (c : ℂ) (r x : ℝ) : ℝ :=
    (F (verticalCirclePoint true c r x)).im-(F (verticalCirclePoint false c r x)).im
 def horizontalCircleFlux (F : ℂ → ℂ) (c : ℂ) (r : ℝ) : ℝ :=
    ∫ y in (c.im-r)..(c.im+r), horizontalCircleIncrement F c r y
 def verticalCircleFlux (F : ℂ → ℂ) (c : ℂ) (r : ℝ) : ℝ :=
    ∫ x in (c.re-r)..(c.re+r), verticalCircleIncrement F c r x

 theorem circle_projection_flux {F : ℂ → ℂ} (hF : Measurable F) (c : ℂ) {r B : ℝ}
    (hr : 0 ≤ r) (hB : 0 ≤ B) (hb : ∀ z ∈ closedBall c r, ‖F z‖ ≤ B) :
    horizontalCircleFlux F c r+verticalCircleFlux F c r = quadrantFlux F c r := by
  let q := fun s t θ => F (quadrantPoint c r s t θ)
  let p1 := fun θ => ((q true true θ).re-(q false true θ).re)*(r*Real.cos θ)
  let p2 := fun θ => ((q true false θ).re-(q false false θ).re)*(r*Real.cos θ)
  let p3 := fun θ => ((q true true θ).im-(q true false θ).im)*(r*Real.sin θ)
  let p4 := fun θ => ((q false true θ).im-(q false false θ).im)*(r*Real.sin θ)
  have hq := quadrant_components_integrable hF c hr hB hb
  have hp1 : IntervalIntegrable p1 volume 0 (Real.pi/2) :=
    ((hq true true).1.sub (hq false true).1).mul_continuousOn (by fun_prop)
  have hp2 : IntervalIntegrable p2 volume 0 (Real.pi/2) :=
    ((hq true false).1.sub (hq false false).1).mul_continuousOn (by fun_prop)
  have hp3 : IntervalIntegrable p3 volume 0 (Real.pi/2) :=
    ((hq true true).2.sub (hq true false).2).mul_continuousOn (by fun_prop)
  have hp4 : IntervalIntegrable p4 volume 0 (Real.pi/2) :=
    ((hq false true).2.sub (hq false false).2).mul_continuousOn (by fun_prop)
  have hπ : (0 : ℝ) ≤ Real.pi/2 := by positivity
  have ehp (θ : ℝ) (hθ : θ ∈ Icc 0 (Real.pi/2)) :
      horizontalCircleIncrement F c r (c.im+r*Real.sin θ) =
        (q true true θ).re-(q false true θ).re := by
    change (F _).re-(F _).re = _
    rw [show c.im+r*Real.sin θ = c.im+quadrantSign true*r*Real.sin θ by simp [quadrantSign]]
    rw [horizontalCirclePoint_quarter c hr hθ, horizontalCirclePoint_quarter c hr hθ]
  have ehm (θ : ℝ) (hθ : θ ∈ Icc 0 (Real.pi/2)) :
      horizontalCircleIncrement F c r (c.im-r*Real.sin θ) =
        (q true false θ).re-(q false false θ).re := by
    change (F _).re-(F _).re = _
    rw [show c.im-r*Real.sin θ = c.im+quadrantSign false*r*Real.sin θ by simp [quadrantSign,sub_eq_add_neg]]
    rw [horizontalCirclePoint_quarter c hr hθ, horizontalCirclePoint_quarter c hr hθ]
  have evp (θ : ℝ) (hθ : θ ∈ Icc 0 (Real.pi/2)) :
      verticalCircleIncrement F c r (c.re+r*Real.cos θ) =
        (q true true θ).im-(q true false θ).im := by
    change (F _).im-(F _).im = _
    rw [show c.re+r*Real.cos θ = c.re+quadrantSign true*r*Real.cos θ by simp [quadrantSign]]
    rw [verticalCirclePoint_quarter c hr hθ, verticalCirclePoint_quarter c hr hθ]
  have evm (θ : ℝ) (hθ : θ ∈ Icc 0 (Real.pi/2)) :
      verticalCircleIncrement F c r (c.re-r*Real.cos θ) =
        (q false true θ).im-(q false false θ).im := by
    change (F _).im-(F _).im = _
    rw [show c.re-r*Real.cos θ = c.re+quadrantSign false*r*Real.cos θ by simp [quadrantSign,sub_eq_add_neg]]
    rw [verticalCirclePoint_quarter c hr hθ, verticalCirclePoint_quarter c hr hθ]
  have e1 : (∫ θ in (0 : ℝ)..(Real.pi/2), p1 θ) =
      ∫ y in c.im..(c.im+r), horizontalCircleIncrement F c r y := by
    rw [← integral_quarter_sin (horizontalCircleIncrement F c r) c.im hr]
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [uIcc_of_le hπ] at hθ
    dsimp only [p1]
    rw [ehp θ hθ]
  have e2 : (∫ θ in (0 : ℝ)..(Real.pi/2), p2 θ) =
      ∫ y in (c.im-r)..c.im, horizontalCircleIncrement F c r y := by
    rw [← integral_quarter_sin_sub (horizontalCircleIncrement F c r) c.im hr]
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [uIcc_of_le hπ] at hθ
    dsimp only [p2]
    rw [ehm θ hθ]
  have e3 : (∫ θ in (0 : ℝ)..(Real.pi/2), p3 θ) =
      ∫ x in c.re..(c.re+r), verticalCircleIncrement F c r x := by
    rw [← integral_quarter_cos (verticalCircleIncrement F c r) c.re hr]
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [uIcc_of_le hπ] at hθ
    dsimp only [p3]
    rw [evp θ hθ]
  have e4 : (∫ θ in (0 : ℝ)..(Real.pi/2), p4 θ) =
      ∫ x in (c.re-r)..c.re, verticalCircleIncrement F c r x := by
    rw [← integral_quarter_cos_sub (verticalCircleIncrement F c r) c.re hr]
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [uIcc_of_le hπ] at hθ
    dsimp only [p4]
    rw [evm θ hθ]
  obtain ⟨hh,hv⟩ := circle_projection_integrable hF c hr hB hb
  obtain ⟨hhl,hhr⟩ := (IntervalIntegrable.trans_iff (show c.im ∈ uIcc (c.im-r) (c.im+r) by
    rw [uIcc_of_le (by linarith)]; constructor <;> linarith)).mp hh
  obtain ⟨hvl,hvr⟩ := (IntervalIntegrable.trans_iff (show c.re ∈ uIcc (c.re-r) (c.re+r) by
    rw [uIcc_of_le (by linarith)]; constructor <;> linarith)).mp hv
  have edensity (θ : ℝ) : r*(∑ s : Bool, ∑ t : Bool,
      (F (quadrantPoint c r s t θ)*star (quadrantNormal s t θ)).re) =
      p1 θ+p2 θ+p3 θ+p4 θ := by
    simp [quadrantNormal,quadrantSign,p1,p2,p3,p4,q,Complex.mul_re]
    ring
  symm
  change (∫ θ in (0 : ℝ)..(Real.pi/2), _) = _
  simp_rw [edensity]
  rw [intervalIntegral.integral_add ((hp1.add hp2).add hp3) hp4,
    intervalIntegral.integral_add (hp1.add hp2) hp3,intervalIntegral.integral_add hp1 hp2,
    e1,e2,e3,e4]
  have eh := intervalIntegral.integral_add_adjacent_intervals hhl hhr
  have ev := intervalIntegral.integral_add_adjacent_intervals hvl hvr
  unfold horizontalCircleFlux verticalCircleFlux
  dsimp only [horizontalCircleIncrement,verticalCircleIncrement]
  linarith

end CircleDomainRigidity

end

end OAI
