import OAI.Geometry.IsometricImmersion.Volterra.VolterraJointSmooth
import OAI.Geometry.IsometricImmersion.Energy.WeightedMultiplier

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry SmoothLocal.ODE

def coordinateRectangle (R a b : ℝ) : Set Coord :=
  {p | p 0 ∈ Ioo (-R) R ∧ p 1 ∈ Ioo a b}

theorem coordinateRectangle_isOpen (R a b : ℝ) : IsOpen (coordinateRectangle R a b) := by
  change IsOpen (((fun p : Coord => p 0) ⁻¹' Ioo (-R) R) ∩
    ((fun p : Coord => p 1) ⁻¹' Ioo a b))
  exact (isOpen_Ioo.preimage (continuous_apply 0)).inter
    (isOpen_Ioo.preimage (continuous_apply 1))

theorem point_mem_rectangle {R a b x y : ℝ}
    (hx : x ∈ Ioo (-R) R) (hy : y ∈ Ioo a b) :
    coordinatePoint x y ∈ coordinateRectangle R a b := by
  simpa [coordinateRectangle, coordinatePoint] using And.intro hx hy

theorem point_eta (p : Coord) : coordinatePoint (p 0) (p 1) = p := by
  ext i
  fin_cases i <;> simp [coordinatePoint]

theorem point_hasDerivAt_t (x y : ℝ) :
    HasDerivAt (fun t => coordinatePoint t y) (Pi.single 0 (1 : ℝ) : Coord) x := by
  simpa [coordinatePoint] using
    ((hasDerivAt_id x).smul_const (Pi.single 0 (1 : ℝ) : Coord)).add_const
      (y • (Pi.single 1 (1 : ℝ) : Coord))

def coordinatePrimitive (B : Coord → ℝ) (p : Coord) : ℝ :=
  ∫ t in 0..p 0, B (coordinatePoint t (p 1))

variable {B : Coord → ℝ} {R a b : ℝ}

theorem parameterDerivative_smooth_on_rectangle
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b)) :
    ∀ n, ContDiffOn ℝ ∞ (curvatureYDerivative B n) (coordinateRectangle R a b) := by
  intro n
  induction n with
  | zero => exact hB
  | succ n hn => exact partial_contDiffOn hn (coordinateRectangle_isOpen R a b) 1

theorem compact_t_mem_rectangle_interval {r : ℝ} (hrR : r < R) (x : Icc (-r) r) :
    (x : ℝ) ∈ Ioo (-R) R :=
  ⟨(neg_lt_neg hrR).trans_le x.2.1, x.2.2.trans_lt hrR⟩

theorem coefficientFamily_apply_on_rectangle
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b))
    (r : ℝ) (hrR : r < R) {y : ℝ} (hy : y ∈ Ioo a b) (x : Icc (-r) r) :
    coordinateCurvatureFamily B r y x = B (coordinatePoint x y) := by
  have hc : Continuous (fun t : Icc (-r) r => B (coordinatePoint t y)) :=
    hB.continuousOn.comp_continuous (by unfold coordinatePoint; fun_prop)
      (fun t => point_mem_rectangle (compact_t_mem_rectangle_interval hrR t) hy)
  unfold coordinateCurvatureFamily
  rw [ContinuousMap.mkD_of_continuous hc]
  rfl

theorem coefficientFamily_contDiffOn_rectangle
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b))
    (r : ℝ) (hrR : r < R) :
    ContDiffOn ℝ ∞ (coordinateCurvatureFamily B r) (Ioo a b) := by
  let H : ℕ → ℝ → Icc (-r) r → ℝ :=
    fun n y x => curvatureYDerivative B n (coordinatePoint x y)
  have hmem (y : ℝ) (hy : y ∈ Ioo a b) (x : Icc (-r) r) :
      coordinatePoint x y ∈ coordinateRectangle R a b :=
    point_mem_rectangle (compact_t_mem_rectangle_interval hrR x) hy
  have hjoint (n : ℕ) : ContinuousOn (Function.uncurry (H n))
      (Ioo a b ×ˢ (Set.univ : Set (Icc (-r) r))) := by
    have hmap : Continuous (fun p : ℝ × Icc (-r) r => coordinatePoint p.2 p.1) := by
      unfold coordinatePoint
      fun_prop
    exact (parameterDerivative_smooth_on_rectangle hB n).continuousOn.comp
      hmap.continuousOn (fun p hp => hmem p.1 hp.1 p.2)
  have hderiv (n : ℕ) (y : ℝ) (hy : y ∈ Ioo a b) (x : Icc (-r) r) :
      HasDerivAt (fun t => H n t x) (H (n + 1) y x) y := by
    have hd : DifferentiableAt ℝ (curvatureYDerivative B n) (coordinatePoint x y) :=
      ((parameterDerivative_smooth_on_rectangle hB n).contDiffAt
        ((coordinateRectangle_isOpen R a b).mem_nhds (hmem y hy x))).differentiableAt
          (by simp)
    exact hd.hasFDerivAt.comp_hasDerivAt y (coordinatePoint_hasDerivAt_y x y)
  exact smooth_curry_of_joint_derivative_sequence H hjoint hderiv 0

theorem coefficientFamily_jet_apply_on_rectangle
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b))
    (r : ℝ) (hrR : r < R) (n : ℕ) (x : Icc (-r) r)
    {y : ℝ} (hy : y ∈ Ioo a b) :
    iteratedDeriv n (coordinateCurvatureFamily B r) y x =
      curvatureYDerivative B n (coordinatePoint x y) := by
  have heval := iteratedDeriv_clm_comp (ContinuousMap.evalCLM ℝ x) n
    ((coefficientFamily_contDiffOn_rectangle hB r hrR).contDiffAt
      (isOpen_Ioo.mem_nhds hy))
  have hev : (fun t => coordinateCurvatureFamily B r t x) =ᶠ[𝓝 y]
      (fun t => B (coordinatePoint x t)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hy] with t ht
    exact coefficientFamily_apply_on_rectangle hB r hrR ht x
  have hdseq (j : ℕ) (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt (fun v => curvatureYDerivative B j (coordinatePoint x v))
        (curvatureYDerivative B (j + 1) (coordinatePoint x t)) t := by
    have hmem : coordinatePoint x t ∈ coordinateRectangle R a b :=
      point_mem_rectangle (compact_t_mem_rectangle_interval hrR x) ht
    have hd : DifferentiableAt ℝ (curvatureYDerivative B j) (coordinatePoint x t) :=
      ((parameterDerivative_smooth_on_rectangle hB j).contDiffAt
        ((coordinateRectangle_isOpen R a b).mem_nhds hmem)).differentiableAt (by simp)
    exact hd.hasFDerivAt.comp_hasDerivAt t (coordinatePoint_hasDerivAt_y x t)
  have hseq := iteratedDeriv_eq_of_derivative_sequence isOpen_Ioo
    (fun j t => curvatureYDerivative B j (coordinatePoint x t)) hdseq n y hy
  calc
    iteratedDeriv n (coordinateCurvatureFamily B r) y x =
        iteratedDeriv n (fun t => coordinateCurvatureFamily B r t x) y := heval.symm
    _ = iteratedDeriv n (fun t => B (coordinatePoint x t)) y := hev.iteratedDeriv_eq n
    _ = curvatureYDerivative B n (coordinatePoint x y) := hseq

theorem coefficientFamily_jet_contDiffOn_rectangle
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b))
    (r : ℝ) (hr : 0 < r) (hrR : r < R) (n : ℕ) :
    ContDiffOn ℝ ∞ (intervalFamilyJet r hr (coordinateCurvatureFamily B r) n)
      (Ioo (-r) r ×ˢ Ioo a b) := by
  have hmap : ContDiff ℝ ∞ (fun p : ℝ × ℝ => coordinatePoint p.1 p.2) := by
    unfold coordinatePoint
    fun_prop
  have hmem : MapsTo (fun p : ℝ × ℝ => coordinatePoint p.1 p.2)
      (Ioo (-r) r ×ˢ Ioo a b) (coordinateRectangle R a b) := by
    intro p hp
    exact point_mem_rectangle
      ⟨(neg_lt_neg hrR).trans hp.1.1, hp.1.2.trans hrR⟩ hp.2
  have hc := (parameterDerivative_smooth_on_rectangle hB n).comp hmap.contDiffOn hmem
  apply hc.congr
  intro p hp
  unfold intervalFamilyJet
  rw [intervalExtension_apply_of_mem r hr _ ⟨hp.1.1.le, hp.1.2.le⟩]
  exact coefficientFamily_jet_apply_on_rectangle hB r hrR n _ hp.2

theorem primitiveFamily_joint_smooth
    (r : ℝ) (hr : 0 < r) {F : ℝ → IntervalFunctions r}
    (hF : ContDiffOn ℝ ∞ F (Ioo a b))
    (hFjets : ∀ j, ContDiffOn ℝ ∞ (intervalFamilyJet r hr F j)
      (Ioo (-r) r ×ˢ Ioo a b)) :
    ∀ j, ContDiffOn ℝ ∞
      (intervalFamilyJet r hr (fun y => primitiveCLM r hr (F y)) j)
      (Ioo (-r) r ×ˢ Ioo a b) := by
  let P : ℝ → IntervalFunctions r := fun y => primitiveCLM r hr (F y)
  let D : Set (ℝ × ℝ) := Ioo (-r) r ×ˢ Ioo a b
  have hD : IsOpen D := isOpen_Ioo.prod isOpen_Ioo
  have hP : ContDiffOn ℝ ∞ P (Ioo a b) := contDiffOn_const.clm_apply hF
  have hdx (j : ℕ) (p : ℝ × ℝ) (hp : p ∈ D) :
      HasDerivAt (fun x => intervalFamilyJet r hr P j (x, p.2))
        (intervalFamilyJet r hr F j p) p.1 := by
    apply intervalFamilyJet_hasDerivAt_x_of_primitive r hr isOpen_Ioo hF 0 _ j hp.1 hp.2
    intro y hy
    change primitiveCLM r hr (F y) = 0 + primitiveCLM r hr (F y)
    rw [zero_add]
  have hdy (j : ℕ) (p : ℝ × ℝ) (hp : p ∈ D) :
      HasDerivAt (fun y => intervalFamilyJet r hr P j (p.1, y))
        (intervalFamilyJet r hr P (j + 1) p) p.2 :=
    intervalFamilyJet_hasDerivAt_y r hr isOpen_Ioo hP j p.1 hp.2
  have hnat : ∀ n : ℕ, ∀ j,
      ContDiffOn ℝ n (intervalFamilyJet r hr P j) D := by
    intro n
    induction n with
    | zero =>
        intro j
        simpa only [Nat.cast_zero, contDiffOn_zero] using
          (intervalFamilyJet_continuousOn r hr isOpen_Ioo hP j).mono
            (fun p hp => ⟨mem_univ p.1, hp.2⟩)
    | succ n hn =>
        intro j
        exact contDiffOn_succ_of_continuous_partials hD n
          (contDiffOn_infty.mp (hFjets j) n) (hn (j + 1)) (hdx j) (hdy j)
  intro j
  exact contDiffOn_infty.mpr (fun n => hnat n j)

def clampedPrimitive (B : Coord → ℝ) (r : ℝ) (hr : 0 < r) (p : ℝ × ℝ) : ℝ :=
  intervalExtension r hr (primitiveCLM r hr (coordinateCurvatureFamily B r p.2)) p.1

theorem clampedPrimitive_contDiffOn
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b))
    (r : ℝ) (hr : 0 < r) (hrR : r < R) :
    ContDiffOn ℝ ∞ (clampedPrimitive B r hr) (Ioo (-r) r ×ˢ Ioo a b) := by
  have h := primitiveFamily_joint_smooth r hr
    (coefficientFamily_contDiffOn_rectangle hB r hrR)
    (coefficientFamily_jet_contDiffOn_rectangle hB r hr hrR) 0
  apply h.congr
  intro p hp
  simp only [intervalFamilyJet, iteratedDeriv_zero, clampedPrimitive]

theorem clampedPrimitive_eq_integral
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b))
    (r : ℝ) (hr : 0 < r) (hrR : r < R)
    {x y : ℝ} (hx : x ∈ Ioo (-r) r) (hy : y ∈ Ioo a b) :
    clampedPrimitive B r hr (x, y) = ∫ t in 0..x, B (coordinatePoint t y) := by
  unfold clampedPrimitive
  rw [intervalExtension_apply_of_mem r hr _ ⟨hx.1.le, hx.2.le⟩, primitiveCLM_apply]
  apply intervalIntegral.integral_congr
  intro t ht
  have hz : (0 : ℝ) ∈ Icc (-r) r := ⟨by linarith, hr.le⟩
  have htmem : t ∈ Icc (-r) r := uIcc_subset_Icc hz ⟨hx.1.le, hx.2.le⟩ ht
  rw [intervalExtension_apply_of_mem r hr _ htmem,
    coefficientFamily_apply_on_rectangle hB r hrR hy]

theorem coordinatePrimitive_contDiffOn_inner
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b))
    (r : ℝ) (hr : 0 < r) (hrR : r < R) :
    ContDiffOn ℝ ∞ (coordinatePrimitive B) (coordinateRectangle r a b) := by
  have hmap : ContDiff ℝ ∞ (fun p : Coord => (p 0, p 1)) := by fun_prop
  have hmem : MapsTo (fun p : Coord => (p 0, p 1)) (coordinateRectangle r a b)
      (Ioo (-r) r ×ˢ Ioo a b) := fun _ hp => hp
  have hc := (clampedPrimitive_contDiffOn hB r hr hrR).comp hmap.contDiffOn hmem
  apply hc.congr
  intro p hp
  exact (clampedPrimitive_eq_integral hB r hr hrR hp.1 hp.2).symm

theorem coordinatePrimitive_contDiffOn
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b)) :
    ContDiffOn ℝ ∞ (coordinatePrimitive B) (coordinateRectangle R a b) := by
  intro p hp
  obtain ⟨r, hpr, hrR⟩ := exists_between (abs_lt.mpr hp.1)
  have hr : 0 < r := (abs_nonneg (p 0)).trans_lt hpr
  have hpmem : p ∈ coordinateRectangle r a b := ⟨abs_lt.mp hpr, hp.2⟩
  exact ((coordinatePrimitive_contDiffOn_inner hB r hr hrR).contDiffAt
    ((coordinateRectangle_isOpen r a b).mem_nhds hpmem)).contDiffWithinAt

theorem coordinatePrimitive_initial (B : Coord → ℝ) (y : ℝ) :
    coordinatePrimitive B (coordinatePoint 0 y) = 0 := by
  simp [coordinatePrimitive, coordinatePoint]

theorem coordinatePrimitive_partial_t
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b))
    (hR : 0 < R) {p : Coord} (hp : p ∈ coordinateRectangle R a b) :
    coordPartial 0 (coordinatePrimitive B) p = B p := by
  have hslice : ContinuousOn (fun t => B (coordinatePoint t (p 1))) (Ioo (-R) R) :=
    hB.continuousOn.comp (by unfold coordinatePoint; fun_prop)
      (fun t ht => point_mem_rectangle ht hp.2)
  have hz : (0 : ℝ) ∈ Ioo (-R) R := ⟨by linarith, hR⟩
  have hseg : uIcc 0 (p 0) ⊆ Ioo (-R) R := by
    intro t ht
    exact ⟨lt_of_lt_of_le (lt_min hz.1 hp.1.1) ht.1,
      lt_of_le_of_lt ht.2 (max_lt hz.2 hp.1.2)⟩
  have hftc := intervalIntegral.integral_hasDerivAt_right
    (hslice.mono hseg).intervalIntegrable
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hslice (p 0) hp.1)
    (hslice.continuousAt (isOpen_Ioo.mem_nhds hp.1))
  have hftc' : HasDerivAt (fun t => coordinatePrimitive B (coordinatePoint t (p 1)))
      (B p) (p 0) := by
    rw [point_eta] at hftc
    simpa [coordinatePrimitive, coordinatePoint] using hftc
  have hd : DifferentiableAt ℝ (coordinatePrimitive B) (coordinatePoint (p 0) (p 1)) := by
    rw [point_eta]
    exact ((coordinatePrimitive_contDiffOn hB).contDiffAt
      ((coordinateRectangle_isOpen R a b).mem_nhds hp)).differentiableAt (by simp)
  have hchain := hd.hasFDerivAt.comp_hasDerivAt (p 0) (point_hasDerivAt_t (p 0) (p 1))
  have hcoord : HasDerivAt (fun t => coordinatePrimitive B (coordinatePoint t (p 1)))
      (coordPartial 0 (coordinatePrimitive B) p) (p 0) := by
    simpa only [point_eta, Function.comp_def, coordPartial] using hchain
  exact hcoord.unique hftc'

theorem primitive_directedM_partial_t
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b)) (hR : 0 < R)
    {p : Coord} (hp : p ∈ coordinateRectangle R a b) (edge lambda : ℝ) :
    coordPartial 0 (directedM edge lambda (coordinatePrimitive B)) p =
      B p * directedM edge lambda (coordinatePrimitive B) p := by
  have hI : DifferentiableAt ℝ (coordinatePrimitive B) p :=
    ((coordinatePrimitive_contDiffOn hB).contDiffAt
      ((coordinateRectangle_isOpen R a b).mem_nhds hp)).differentiableAt (by simp)
  rw [directedM_partial, directedWeight_partial_t edge lambda hI,
    coordinatePrimitive_partial_t hB hR hp]
  simp only [directedM]
  ring

theorem primitive_directedJ
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b)) (hR : 0 < R)
    {p : Coord} (hp : p ∈ coordinateRectangle R a b)
    (A C : Coord → ℝ) (hA : DifferentiableAt ℝ A p)
    (edge lambda epsilon : ℝ) (hd : edgeDistance edge p ≠ 0) :
    multiplierJ A B C (directedM edge lambda (coordinatePrimitive B))
      (directedN edge lambda epsilon (coordinatePrimitive B)) p =
      directedWeight edge lambda (coordinatePrimitive B) p *
        (epsilon * p 0 * (C p - coordPartial 1 A p +
          A p * (weightH0 edge lambda p - coordPartial 1 (coordinatePrimitive B) p))) := by
  have hI : DifferentiableAt ℝ (coordinatePrimitive B) p :=
    ((coordinatePrimitive_contDiffOn hB).contDiffAt
      ((coordinateRectangle_isOpen R a b).mem_nhds hp)).differentiableAt (by simp)
  have he := (directed_coefficients A B C edge lambda epsilon hA hI hd).2.2
  rw [coordinatePrimitive_partial_t hB hR hp] at he
  simpa only [sub_self, zero_add] using he

end SmoothLocal.Weighted

end

end OAI
