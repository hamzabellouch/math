import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.GaussTensorError

namespace OAI

/-! Local versions of tensor cubature: regularity is only needed on the
integration cube, which may be far from a Coulomb singularity. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def unitClamp (x : ℝ) : ℝ := max (-1) (min 1 x)

theorem unitClamp_mem (x : ℝ) : unitClamp x ∈ Set.Icc (-1:ℝ) 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem unitClamp_eq {x : ℝ} (hx : x ∈ Set.Icc (-1:ℝ) 1) : unitClamp x = x := by
  simp only [unitClamp,min_eq_right hx.2,max_eq_right hx.1]

theorem unitClamp_continuous : Continuous unitClamp :=
  continuous_const.max (continuous_const.min continuous_id)

def unitCube3 : Set (ℝ × ℝ × ℝ) :=
  {p | p.1 ∈ Set.Icc (-1:ℝ) 1 ∧ p.2.1 ∈ Set.Icc (-1:ℝ) 1 ∧ p.2.2 ∈ Set.Icc (-1:ℝ) 1}

theorem gaussTwoPoint_congr_on {f g : ℝ → ℝ}
    (h : Set.EqOn f g (Set.Icc (-1:ℝ) 1)) : gaussTwoPoint f = gaussTwoPoint g := by
  have ha : gaussAbscissa ≤ 1 := by nlinarith only [gaussAbscissa_sq,gaussAbscissa_pos]
  have hp := gaussAbscissa_pos.le
  unfold gaussTwoPoint
  rw [h (x := -gaussAbscissa) ⟨by linarith,by linarith⟩,
    h (x := gaussAbscissa) ⟨by linarith,ha⟩]

theorem unitInterval_integral_congr {f g : ℝ → ℝ}
    (h : Set.EqOn f g (Set.Icc (-1:ℝ) 1)) :
    (∫ x : ℝ in (-1)..1, f x) = ∫ x : ℝ in (-1)..1, g x := by
  apply intervalIntegral.integral_congr
  simpa only [Set.uIcc_of_le (by norm_num : (-1:ℝ) ≤ 1)] using h

theorem gaussTensor3_congr_on {f g : ℝ → ℝ → ℝ → ℝ}
    (h : ∀ x ∈ Set.Icc (-1:ℝ) 1, ∀ y ∈ Set.Icc (-1:ℝ) 1,
      ∀ z ∈ Set.Icc (-1:ℝ) 1, f x y z = g x y z) :
    gaussTwoPoint (fun x => gaussTwoPoint (fun y => gaussTwoPoint (f x y))) =
      gaussTwoPoint (fun x => gaussTwoPoint (fun y => gaussTwoPoint (g x y))) := by
  apply gaussTwoPoint_congr_on
  intro x hx
  apply gaussTwoPoint_congr_on
  intro y hy
  exact gaussTwoPoint_congr_on (h x hx y hy)

theorem unitCube_integral_congr {f g : ℝ → ℝ → ℝ → ℝ}
    (h : ∀ x ∈ Set.Icc (-1:ℝ) 1, ∀ y ∈ Set.Icc (-1:ℝ) 1,
      ∀ z ∈ Set.Icc (-1:ℝ) 1, f x y z = g x y z) :
    (∫ x : ℝ in (-1)..1, ∫ y : ℝ in (-1)..1, ∫ z : ℝ in (-1)..1, f x y z) =
      ∫ x : ℝ in (-1)..1, ∫ y : ℝ in (-1)..1, ∫ z : ℝ in (-1)..1, g x y z := by
  apply unitInterval_integral_congr
  intro x hx
  apply unitInterval_integral_congr
  intro y hy
  exact unitInterval_integral_congr (h x hx y hy)

theorem gaussTensor3_error_on_cube (f : ℝ → ℝ → ℝ → ℝ)
    (hf : ContinuousOn (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2) unitCube3) {E : ℝ}
    (hx : ∀ y ∈ Set.Icc (-1) 1, ∀ z ∈ Set.Icc (-1) 1,
      |gaussTwoPoint (fun x => f x y z)-(∫ x : ℝ in (-1)..1, f x y z)| ≤ E)
    (hy : ∀ x ∈ Set.Icc (-1) 1, ∀ z ∈ Set.Icc (-1) 1,
      |gaussTwoPoint (fun y => f x y z)-(∫ y : ℝ in (-1)..1, f x y z)| ≤ E)
    (hz : ∀ x ∈ Set.Icc (-1) 1, ∀ y ∈ Set.Icc (-1) 1,
      |gaussTwoPoint (f x y)-(∫ z : ℝ in (-1)..1, f x y z)| ≤ E) :
    |gaussTwoPoint (fun x => gaussTwoPoint (fun y => gaussTwoPoint (f x y)))-
      (∫ x : ℝ in (-1)..1, ∫ y : ℝ in (-1)..1, ∫ z : ℝ in (-1)..1, f x y z)| ≤ 12*E := by
  let g : ℝ → ℝ → ℝ → ℝ := fun x y z => f (unitClamp x) (unitClamp y) (unitClamp z)
  have hg : Continuous (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2) :=
    hf.comp_continuous
      ((unitClamp_continuous.comp continuous_fst).prodMk
        ((unitClamp_continuous.comp (continuous_fst.comp continuous_snd)).prodMk
          (unitClamp_continuous.comp (continuous_snd.comp continuous_snd))))
      (fun p => ⟨unitClamp_mem p.1,unitClamp_mem p.2.1,unitClamp_mem p.2.2⟩)
  have heq : ∀ x ∈ Set.Icc (-1:ℝ) 1, ∀ y ∈ Set.Icc (-1:ℝ) 1,
      ∀ z ∈ Set.Icc (-1:ℝ) 1, g x y z = f x y z := by
    intro x hx y hy z hz
    simp only [g,unitClamp_eq hx,unitClamp_eq hy,unitClamp_eq hz]
  have hxe : ∀ y ∈ Set.Icc (-1) 1, ∀ z ∈ Set.Icc (-1) 1,
      |gaussTwoPoint (fun x => g x y z)-(∫ x : ℝ in (-1)..1, g x y z)| ≤ E := by
    intro y hy z hz
    have he : Set.EqOn (fun x => g x y z) (fun x => f x y z) (Set.Icc (-1:ℝ) 1) :=
      fun x hx => heq x hx y hy z hz
    rw [gaussTwoPoint_congr_on he,unitInterval_integral_congr he]
    exact hx y hy z hz
  have hye : ∀ x ∈ Set.Icc (-1) 1, ∀ z ∈ Set.Icc (-1) 1,
      |gaussTwoPoint (fun y => g x y z)-(∫ y : ℝ in (-1)..1, g x y z)| ≤ E := by
    intro x hx z hz
    have he : Set.EqOn (fun y => g x y z) (fun y => f x y z) (Set.Icc (-1:ℝ) 1) :=
      fun y hy => heq x hx y hy z hz
    rw [gaussTwoPoint_congr_on he,unitInterval_integral_congr he]
    exact hy x hx z hz
  have hze : ∀ x ∈ Set.Icc (-1) 1, ∀ y ∈ Set.Icc (-1) 1,
      |gaussTwoPoint (g x y)-(∫ z : ℝ in (-1)..1, g x y z)| ≤ E := by
    intro x hx y hy
    have he : Set.EqOn (g x y) (f x y) (Set.Icc (-1:ℝ) 1) :=
      fun z hz => heq x hx y hy z hz
    rw [gaussTwoPoint_congr_on he,unitInterval_integral_congr he]
    exact hz x hx y hy
  have he := gaussTensor3_error g hg hxe hye hze
  rw [gaussTensor3_congr_on heq,unitCube_integral_congr heq] at he
  exact he

theorem gaussTensor3_C4_error_on_cube (f : ℝ → ℝ → ℝ → ℝ)
    (hf : ContinuousOn (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2) unitCube3) {C : ℝ} (hC : 0 ≤ C)
    (hfx : ∀ y ∈ Set.Icc (-1) 1, ∀ z ∈ Set.Icc (-1) 1,
      ContDiffOn ℝ 4 (fun x => f x y z) (Set.Icc (-1) 1))
    (hfy : ∀ x ∈ Set.Icc (-1) 1, ∀ z ∈ Set.Icc (-1) 1,
      ContDiffOn ℝ 4 (fun y => f x y z) (Set.Icc (-1) 1))
    (hfz : ∀ x ∈ Set.Icc (-1) 1, ∀ y ∈ Set.Icc (-1) 1,
      ContDiffOn ℝ 4 (f x y) (Set.Icc (-1) 1))
    (hCx : ∀ y ∈ Set.Icc (-1) 1, ∀ z ∈ Set.Icc (-1) 1, ∀ x ∈ Set.Icc (-1) 1,
      ‖iteratedDerivWithin 4 (fun x => f x y z) (Set.Icc (-1) 1) x‖ ≤ C)
    (hCy : ∀ x ∈ Set.Icc (-1) 1, ∀ z ∈ Set.Icc (-1) 1, ∀ y ∈ Set.Icc (-1) 1,
      ‖iteratedDerivWithin 4 (fun y => f x y z) (Set.Icc (-1) 1) y‖ ≤ C)
    (hCz : ∀ x ∈ Set.Icc (-1) 1, ∀ y ∈ Set.Icc (-1) 1, ∀ z ∈ Set.Icc (-1) 1,
      ‖iteratedDerivWithin 4 (f x y) (Set.Icc (-1) 1) z‖ ≤ C) :
    |gaussTwoPoint (fun x => gaussTwoPoint (fun y => gaussTwoPoint (f x y)))-
      (∫ x : ℝ in (-1)..1, ∫ y : ℝ in (-1)..1, ∫ z : ℝ in (-1)..1, f x y z)| ≤ 128*C := by
  have h := gaussTensor3_error_on_cube f hf
    (fun y hy z hz => gaussTwoPoint_C4_error _ hC (hfx y hy z hz) (hCx y hy z hz))
    (fun x hx z hz => gaussTwoPoint_C4_error _ hC (hfy x hx z hz) (hCy x hx z hz))
    (fun x hx y hy => gaussTwoPoint_C4_error _ hC (hfz x hx y hy) (hCz x hx y hy))
  convert h using 1
  ring


end ContinuumCoulomb

end

end OAI
