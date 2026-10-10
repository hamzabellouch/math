import OAI.Geometry.IsometricImmersion.Volterra.VolterraJointSmooth
import OAI.Geometry.IsometricImmersion.Volterra.VolterraPositive
import OAI.Geometry.IsometricImmersion.Flows.Existence
import Mathlib.Analysis.Calculus.Deriv.Prod

namespace OAI

noncomputable section
open Set Metric
open scoped ContDiff NNReal Topology

namespace SmoothLocal.ODE
open SmoothLocal.Geometry

def prescribedLocalState (K : Coord → ℝ) (r : ℝ) (hr : 0 < r)
    (y x : ℝ) : ℝ × ℝ :=
  (volterraScalar r hr (coordinateCurvatureFamily K r y) x,
    volterraVelocity r hr (coordinateCurvatureFamily K r y) x)

theorem prescribedLocalState_initial {K : Coord → ℝ}
    (hK : ContDiffOn ℝ ∞ K square)
    (hbound : ∀ p ∈ square, |K p| ≤ (1 : ℝ) / 1000)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    {y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) :
    prescribedLocalState K r hr y 0 = (1, 0) := by
  apply Prod.ext
  · exact volterraScalar_initial r hr hr1.le _
      (coordinateCurvatureFamily_norm_le hK hbound r hr1 hy)
  · exact volterraVelocity_initial r hr _

theorem prescribedLocalState_hasDerivAt {K : Coord → ℝ}
    (hK : ContDiffOn ℝ ∞ K square)
    (hbound : ∀ p ∈ square, |K p| ≤ (1 : ℝ) / 1000)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    {y x : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) (hx : x ∈ Ioo (-r) r) :
    HasDerivAt (prescribedLocalState K r hr y)
      (curvatureField (fun t => K (coordinatePoint t y)) x
        (prescribedLocalState K r hr y x)) x := by
  have hkx : intervalExtension r hr (coordinateCurvatureFamily K r y) x =
      K (coordinatePoint x y) := by
    rw [intervalExtension_apply_of_mem r hr _ ⟨hx.1.le, hx.2.le⟩]
    exact coordinateCurvatureFamily_apply hK r hr1 hy _
  have hf := volterraScalar_hasDerivAt r hr hr1.le (coordinateCurvatureFamily K r y)
    (coordinateCurvatureFamily_norm_le hK hbound r hr1 hy) hx
  have hp := volterraVelocity_hasDerivAt r hr (coordinateCurvatureFamily K r y) x
  rw [hkx] at hp
  exact hf.prodMk hp

theorem prescribedLocalState_agree {K : Coord → ℝ}
    (hK : ContDiffOn ℝ ∞ K square)
    (hbound : ∀ p ∈ square, |K p| ≤ (1 : ℝ) / 1000)
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s) (hr1 : r < 1) (hs1 : s < 1)
    {y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) :
    EqOn (prescribedLocalState K r hr y) (prescribedLocalState K s hs y)
      (Ioo (-(min r s)) (min r s)) := by
  have hsubr : Ioo (-(min r s)) (min r s) ⊆ Ioo (-r) r := by
    intro t ht
    constructor <;> linarith [min_le_left r s, ht.1, ht.2]
  have hsubs : Ioo (-(min r s)) (min r s) ⊆ Ioo (-s) s := by
    intro t ht
    constructor <;> linarith [min_le_right r s, ht.1, ht.2]
  apply ODE_solution_unique_of_mem_Ioo
    (v := curvatureField (fun t => K (coordinatePoint t y)))
    (s := fun _ => Set.univ) (K := 1) (t₀ := 0)
  · intro t ht
    have htr := hsubr ht
    have htbig : t ∈ Ioo (-1 : ℝ) 1 :=
      ⟨(neg_lt_neg hr1).trans htr.1, htr.2.trans hr1⟩
    apply LipschitzOnWith.of_dist_le_mul
    intro u _ v _
    exact (curvatureField_lipschitz
      (hbound _ (coordinatePoint_mem_square htbig hy))).dist_le_mul u v
  · have hm : 0 < min r s := lt_min hr hs
    exact ⟨by linarith, hm⟩
  · intro t ht
    exact ⟨prescribedLocalState_hasDerivAt hK hbound r hr hr1 hy (hsubr ht), mem_univ _⟩
  · intro t ht
    exact ⟨prescribedLocalState_hasDerivAt hK hbound s hs hs1 hy (hsubs ht), mem_univ _⟩
  · exact (prescribedLocalState_initial hK hbound r hr hr1 hy).trans
      (prescribedLocalState_initial hK hbound s hs hs1 hy).symm

def interiorRadius (x : ℝ) : ℝ := (|x| + 1) / 2

theorem interiorRadius_pos (x : ℝ) : 0 < interiorRadius x := by
  unfold interiorRadius
  linarith [abs_nonneg x]

theorem interiorRadius_lt_one {x : ℝ} (hx : |x| < 1) : interiorRadius x < 1 := by
  unfold interiorRadius
  linarith

theorem abs_lt_interiorRadius {x : ℝ} (hx : |x| < 1) : |x| < interiorRadius x := by
  unfold interiorRadius
  linarith

def globalPrescribedState (K : Coord → ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  prescribedLocalState K (interiorRadius p.1) (interiorRadius_pos p.1) p.2 p.1

def globalPrescribedScalar (K : Coord → ℝ) (p : ℝ × ℝ) : ℝ :=
  (globalPrescribedState K p).1

theorem globalPrescribedState_eq_local {K : Coord → ℝ}
    (hK : ContDiffOn ℝ ∞ K square)
    (hbound : ∀ p ∈ square, |K p| ≤ (1 : ℝ) / 1000)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) {p : ℝ × ℝ}
    (hp : p ∈ Ioo (-r) r ×ˢ Ioo (-1 : ℝ) 1) :
    globalPrescribedState K p = prescribedLocalState K r hr p.2 p.1 := by
  have hxr : |p.1| < r := abs_lt.mpr hp.1
  have hx1 : |p.1| < 1 := hxr.trans hr1
  exact prescribedLocalState_agree hK hbound (interiorRadius p.1) r
    (interiorRadius_pos p.1) hr (interiorRadius_lt_one hx1) hr1 hp.2
    (abs_lt.mp (lt_min (abs_lt_interiorRadius hx1) hxr))

theorem globalPrescribedScalar_contDiffOn {K : Coord → ℝ}
    (hK : ContDiffOn ℝ ∞ K square)
    (hbound : ∀ p ∈ square, |K p| ≤ (1 : ℝ) / 1000) :
    ContDiffOn ℝ ∞ (globalPrescribedScalar K)
      (Ioo (-1 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) := by
  intro p hp
  let r := interiorRadius p.1
  have hr : 0 < r := interiorRadius_pos p.1
  have hr1 : r < 1 := interiorRadius_lt_one (abs_lt.mpr hp.1)
  have hpr : p ∈ Ioo (-r) r ×ˢ Ioo (-1 : ℝ) 1 :=
    ⟨abs_lt.mp (abs_lt_interiorRadius (abs_lt.mpr hp.1)), hp.2⟩
  have hlocal : ContDiffOn ℝ ∞ (globalPrescribedScalar K)
      (Ioo (-r) r ×ˢ Ioo (-1 : ℝ) 1) := by
    apply (prescribedVolterraFamily_joint_contDiffOn hK hbound r hr hr1).congr
    intro q hq
    exact congrArg Prod.fst (globalPrescribedState_eq_local hK hbound r hr hr1 hq)
  exact (hlocal.contDiffAt ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds hpr)).contDiffWithinAt

theorem globalPrescribedScalar_bounds {K : Coord → ℝ}
    (hK : ContDiffOn ℝ ∞ K square)
    (hbound : ∀ p ∈ square, |K p| ≤ (1 : ℝ) / 1000)
    {p : ℝ × ℝ} (hp : p ∈ Ioo (-1 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) :
    (998 : ℝ) / 999 ≤ globalPrescribedScalar K p ∧
      globalPrescribedScalar K p ≤ (1000 : ℝ) / 999 ∧ 0 < globalPrescribedScalar K p := by
  exact volterraScalar_bounds (interiorRadius p.1) (interiorRadius_pos p.1)
    (interiorRadius_lt_one (abs_lt.mpr hp.1)).le _
    (coordinateCurvatureFamily_norm_le hK hbound (interiorRadius p.1)
      (interiorRadius_lt_one (abs_lt.mpr hp.1)) hp.2) p.1

def prescribedFactor (K : Coord → ℝ) (p : Coord) : ℝ :=
  globalPrescribedScalar K (p 0, p 1)

theorem prescribedFactor_contDiffOn {K : Coord → ℝ}
    (hK : ContDiffOn ℝ ∞ K square)
    (hbound : ∀ p ∈ square, |K p| ≤ (1 : ℝ) / 1000) :
    ContDiffOn ℝ ∞ (prescribedFactor K) square := by
  have hmap : ContDiff ℝ ∞ (fun p : Coord => (p 0, p 1)) := by fun_prop
  exact (globalPrescribedScalar_contDiffOn hK hbound).comp hmap.contDiffOn
    (fun p hp => ⟨hp 0, hp 1⟩)

theorem prescribedFactor_bounds {K : Coord → ℝ}
    (hK : ContDiffOn ℝ ∞ K square)
    (hbound : ∀ p ∈ square, |K p| ≤ (1 : ℝ) / 1000)
    {p : Coord} (hp : p ∈ square) :
    (998 : ℝ) / 999 ≤ prescribedFactor K p ∧
      prescribedFactor K p ≤ (1000 : ℝ) / 999 ∧ 0 < prescribedFactor K p :=
  globalPrescribedScalar_bounds hK hbound ⟨hp 0, hp 1⟩

end SmoothLocal.ODE

end

end OAI
