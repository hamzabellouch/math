import OAI.Geometry.IsometricImmersion.Caps.CapReflectionGeometry

namespace OAI

noncomputable section
open Set Function Filter
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow.Reflection
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.HighEquation

theorem reflectPoint_coordinatePoint (t s : ℝ) :
    reflectPoint (coordinatePoint t s) = coordinatePoint t (-s) := by
  ext i
  fin_cases i <;> simp [coordinatePoint]

theorem reflectPoint_mem_capChartDomain (p : Coord) :
    reflectPoint p ∈ capChartDomain ↔ p ∈ capChartDomain := by
  change (reflectPoint p 0 ∈ Ioo (-2 : ℝ) 2 ∧ reflectPoint p 1 ∈ Ioo (-2 : ℝ) 2) ↔ _
  simp only [reflectPoint_zero,reflectPoint_one,mem_Ioo]
  change ((-2 < p 0 ∧ p 0 < 2) ∧ -2 < -p 1 ∧ -p 1 < 2) ↔
    ((-2 < p 0 ∧ p 0 < 2) ∧ -2 < p 1 ∧ p 1 < 2)
  constructor <;> rintro ⟨ht,hs⟩ <;> refine ⟨ht,?_,?_⟩ <;> linarith [hs.1,hs.2]

theorem coordPartial_reflectedScalar {f : Coord → ℝ} {p : Coord}
    (hf : DifferentiableAt ℝ f (reflectPoint p)) (i : Fin 2) :
    coordPartial i (reflectedScalar f) p =
      if i=0 then coordPartial 0 f (reflectPoint p) else -coordPartial 1 f (reflectPoint p) := by
  have hfa : DifferentiableAt ℝ f (affineCoordinates 0 reflectionMatrix p) := by
    rwa [←reflectPoint_eq_affine]
  have hh := coordPartial_affine_comp 0 reflectionMatrix p hfa i
  rw [←reflectPoint_eq_affine] at hh
  fin_cases i <;>
    simpa [reflectedScalar,reflectionMatrix,Fin.sum_univ_two] using hh

theorem verticalJet_reflectedScalar {f : Coord → ℝ} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (n : ℕ)
    {p : Coord} (hp : reflectPoint p ∈ U) :
    verticalJet (reflectedScalar f) n p = (-1 : ℝ)^n * verticalJet f n (reflectPoint p) := by
  induction n generalizing p with
  | zero => simp [verticalJet,reflectedScalar]
  | succ n ih =>
    have he : verticalJet (reflectedScalar f) n =ᶠ[𝓝 p]
        (fun q => (-1 : ℝ)^n * verticalJet f n (reflectPoint q)) := by
      filter_upwards [(reflectedDomain_isOpen hU).mem_nhds hp] with q hq
      exact ih hq
    have hfn := verticalJet_contDiffOn hU hf n
    have hdr : DifferentiableAt ℝ (reflectedScalar (verticalJet f n)) p :=
      ((reflectedScalar_contDiffOn hfn).contDiffAt
        ((reflectedDomain_isOpen hU).mem_nhds hp)).differentiableAt (by simp)
    have hd : DifferentiableAt ℝ (verticalJet f n) (reflectPoint p) :=
      (hfn.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
    change coordPartial 1 (verticalJet (reflectedScalar f) n) p = _
    rw [coordPartial_eq_of_eventuallyEq he 1]
    change coordPartial 1 (fun q => (-1 : ℝ)^n * reflectedScalar (verticalJet f n) q) p = _
    rw [AffineCalculus.coordPartial_const_mul_at hdr,
      coordPartial_reflectedScalar hd 1]
    simp only [show (1 : Fin 2) ≠ 0 by decide,ite_false,verticalJet,pow_succ]
    ring

theorem negOnePow_square (n : ℕ) : ((-1 : ℝ)^n)^2 = 1 := by
  rw [←pow_mul,Nat.mul_comm,pow_mul]
  norm_num

def conjugateFlow (Y : ℝ → ℝ → ℝ) (s t : ℝ) : ℝ := -Y (-s) t

theorem conjugateFlow_chart (Y : ℝ → ℝ → ℝ) (p : Coord) :
    capChart (conjugateFlow Y) p = reflectPoint (capChart Y (reflectPoint p)) := by
  simp only [capChart,capFlowHeight,conjugateFlow,reflectPoint_zero,reflectPoint_one,
    reflectPoint_coordinatePoint]

theorem conjugateFlow_start {Y : ℝ → ℝ → ℝ}
    (h : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s) :
    ∀ s ∈ Icc (-2 : ℝ) 2, conjugateFlow Y s 0 = s := by
  intro s hs
  have hn : -s ∈ Icc (-2 : ℝ) 2 := by constructor <;> linarith [hs.1,hs.2]
  simp [conjugateFlow,h (-s) hn]

theorem conjugateFlow_chart_contDiffOn {Y : ℝ → ℝ → ℝ}
    (hY : ContDiffOn ℝ ∞ (capChart Y) capChartDomain) :
    ContDiffOn ℝ ∞ (capChart (conjugateFlow Y)) capChartDomain := by
  have hh := reflectPoint_contDiff.comp_contDiffOn
    (hY.comp reflectPoint_contDiff.contDiffOn
      (fun p hp => (reflectPoint_mem_capChartDomain p).mpr hp))
  exact hh.congr (fun p _ => conjugateFlow_chart Y p)

theorem conjugateFlow_displacement {Y : ℝ → ℝ → ℝ}
    (hY : ∀ p ∈ capChartDomain, |capFlowHeight Y p-p 1| ≤ (1 : ℝ)/50) :
    ∀ p ∈ capChartDomain, |capFlowHeight (conjugateFlow Y) p-p 1| ≤ (1 : ℝ)/50 := by
  intro p hp
  have hh := hY (reflectPoint p) ((reflectPoint_mem_capChartDomain p).mpr hp)
  change |-Y (-p 1) (p 0)-p 1| ≤ _
  have he : -Y (-p 1) (p 0)-p 1 = -(Y (-p 1) (p 0)-(-p 1)) := by ring
  rw [he,abs_neg]
  simpa only [capFlowHeight,reflectPoint_zero,reflectPoint_one] using hh

theorem conjugateFlow_ode
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
    (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    (hmap : MapsTo (capChart Y) capChartDomain (reflectPoint ⁻¹' U))
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s)
        (-hessianQuotient (reflectedMetric g) (reflectedScalar z) (coordinatePoint t (Y s t)))
        (Icc (-2 : ℝ) 2) t) :
    ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2,
      HasDerivWithinAt (conjugateFlow Y s)
        (-hessianQuotient g z (coordinatePoint t (conjugateFlow Y s t)))
        (Ioo (-2 : ℝ) 2) t := by
  intro s hs t ht
  have hsneg : -s ∈ Icc (-2 : ℝ) 2 := by constructor <;> linarith [hs.1,hs.2]
  have hp : coordinatePoint t (-s) ∈ capChartDomain := by
    change (coordinatePoint t (-s) 0 ∈ Ioo (-2 : ℝ) 2 ∧
      coordinatePoint t (-s) 1 ∈ Ioo (-2 : ℝ) 2)
    simp only [coordinatePoint,Pi.add_apply,Pi.smul_apply,Pi.single_apply]
    norm_num
    exact ⟨ht,by constructor <;> linarith [hs.1,hs.2]⟩
  have hmem : reflectPoint (coordinatePoint t (Y (-s) t)) ∈ U := by
    simpa [capChart,capFlowHeight,coordinatePoint] using hmap hp
  have hh := ((hode (-s) hsneg t ⟨ht.1.le,ht.2.le⟩).neg).mono Ioo_subset_Icc_self
  simp only [neg_neg,reflectedMetric_quotient hg hz hU hmem,
    reflectPoint_coordinatePoint] at hh
  exact hh

theorem rectangleIntegral_reflectedScalar (left right bottom top : ℝ) (f : Coord → ℝ) :
    rectangleIntegral left right bottom top (reflectedScalar f) =
      rectangleIntegral left right (-top) (-bottom) f := by
  unfold rectangleIntegral
  have he (t s : ℝ) : reflectedScalar f (boxPoint t s) = f (boxPoint t (-s)) := by
    exact congrArg f (reflectPoint_coordinatePoint t s)
  simp_rw [he]
  exact intervalIntegral.integral_comp_neg (fun s : ℝ => ∫ t in left..right, f (boxPoint t s))

theorem reflectedScalar_gradient_square {u : Coord → ℝ} {p : Coord}
    (hu : DifferentiableAt ℝ u (reflectPoint p)) :
    (coordPartial 0 (reflectedScalar u) p)^2 + (coordPartial 1 (reflectedScalar u) p)^2 =
      (coordPartial 0 u (reflectPoint p))^2 + (coordPartial 1 u (reflectPoint p))^2 := by
  simp only [coordPartial_reflectedScalar hu,ite_true,
    show (1 : Fin 2) ≠ 0 by decide,ite_false,neg_sq]

theorem rectangleGradient_reflectedScalar {u : Coord → ℝ} {U : Set Coord}
    (hu : ContDiffOn ℝ ∞ u U) (hU : IsOpen U)
    {left right bottom top : ℝ} (hlr : left ≤ right) (hbt : bottom ≤ top)
    (hmap : MapsTo reflectPoint (closedRectangle left right bottom top) U) :
    rectangleIntegral left right bottom top (fun p =>
      (coordPartial 0 (reflectedScalar u) p)^2 + (coordPartial 1 (reflectedScalar u) p)^2) =
    rectangleIntegral left right (-top) (-bottom) (fun p =>
      (coordPartial 0 u p)^2 + (coordPartial 1 u p)^2) := by
  calc
    _ = rectangleIntegral left right bottom top
        (reflectedScalar (fun p => (coordPartial 0 u p)^2+(coordPartial 1 u p)^2)) := by
      apply rectangleIntegral_congr hlr hbt
      intro p hp
      exact reflectedScalar_gradient_square
        ((hu.contDiffAt (hU.mem_nhds (hmap hp))).differentiableAt (by simp))
    _ = _ := rectangleIntegral_reflectedScalar _ _ _ _ _

end SmoothLocal.Flow.Reflection

end

end OAI
