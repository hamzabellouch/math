import OAI.Analysis.SphereIsometry.Model
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Sphere maps and the maximal cross-radius defect

The sphere carries the ambient distance. All defects below use the actual sphere
isometry and ordinary real scalar multiplication; no extension law is assumed.
-/

noncomputable section

namespace Tingley

universe u v

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

omit [NormedSpace ℝ X] in
@[simp] theorem UnitSphere.norm_coe (x : UnitSphere X) : ‖(x : X)‖ = 1 := x.property

omit [NormedSpace ℝ X] in
theorem UnitSphere.coe_ne_zero (x : UnitSphere X) : (x : X) ≠ 0 := by
  intro h
  have hx := x.property
  simp [h] at hx

@[simp] theorem normalize_coe (x : X) (hx : x ≠ 0) :
    (normalize x hx : X) = ‖x‖⁻¹ • x := rfl

theorem norm_smul_normalize (x : X) (hx : x ≠ 0) :
    ‖x‖ • (normalize x hx : X) = x := by
  rw [normalize_coe, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]

instance UnitSphere.instNonempty [Nontrivial X] : Nonempty (UnitSphere X) := by
  obtain ⟨x, hx⟩ := exists_ne (0 : X)
  exact ⟨normalize x hx⟩

omit [NormedSpace ℝ X] [NormedSpace ℝ Y] in
theorem sphere_norm_sub (f : UnitSphere X ≃ᵢ UnitSphere Y) (x y : UnitSphere X) :
    ‖(f x : Y) - (f y : Y)‖ = ‖(x : X) - (y : X)‖ := by
  simpa only [Subtype.dist_eq, dist_eq_norm] using f.dist_eq x y

def signedDefect (f : UnitSphere X ≃ᵢ UnitSphere Y) (q : ℝ)
    (x y : UnitSphere X) : ℝ :=
  ‖(f x : Y) - q • (f y : Y)‖ - ‖(x : X) - q • (y : X)‖

def HasDefectBound (f : UnitSphere X ≃ᵢ UnitSphere Y) (M : ℝ) : Prop :=
  ∀ q ∈ Set.Icc (0 : ℝ) 1, ∀ x y : UnitSphere X, |signedDefect f q x y| ≤ M

def absoluteDefects (f : UnitSphere X ≃ᵢ UnitSphere Y) : Set ℝ :=
  {d | ∃ q ∈ Set.Icc (0 : ℝ) 1, ∃ x y : UnitSphere X, d = |signedDefect f q x y|}

def maxDefect (f : UnitSphere X ≃ᵢ UnitSphere Y) : ℝ := sSup (absoluteDefects f)

@[simp] theorem signedDefect_zero (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (x y : UnitSphere X) : signedDefect f 0 x y = 0 := by
  simp [signedDefect]

@[simp] theorem signedDefect_one (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (x y : UnitSphere X) : signedDefect f 1 x y = 0 := by
  simp [signedDefect, sphere_norm_sub]

theorem signedDefect_symm (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (q : ℝ) (x y : UnitSphere X) :
    signedDefect f.symm q (f x) (f y) = -signedDefect f q x y := by
  simp only [signedDefect, IsometryEquiv.symm_apply_apply]
  ring

theorem HasDefectBound.symm {f : UnitSphere X ≃ᵢ UnitSphere Y} {M : ℝ}
    (h : HasDefectBound f M) : HasDefectBound f.symm M := by
  intro q hq x y
  obtain ⟨a, rfl⟩ := f.surjective x
  obtain ⟨b, rfl⟩ := f.surjective y
  simpa only [signedDefect_symm, abs_neg] using h q hq a b

theorem norm_sub_smul_lipschitz (x : X) (y : UnitSphere X) (q r : ℝ) :
    |‖x - q • (y : X)‖ - ‖x - r • (y : X)‖| ≤ |q - r| := by
  calc
    |‖x - q • (y : X)‖ - ‖x - r • (y : X)‖| ≤
        ‖(x - q • (y : X)) - (x - r • (y : X))‖ := abs_norm_sub_norm_le _ _
    _ = ‖(r - q) • (y : X)‖ := by
      congr 1
      rw [sub_smul]
      abel
    _ = |q - r| := by simp [norm_smul, Real.norm_eq_abs, abs_sub_comm]

theorem signedDefect_lipschitz (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (q r : ℝ) (x y : UnitSphere X) :
    |signedDefect f q x y - signedDefect f r x y| ≤ 2 * |q - r| := by
  have hx := norm_sub_smul_lipschitz (x : X) y q r
  have hy := norm_sub_smul_lipschitz (f x : Y) (f y) q r
  have ht := abs_sub
    (‖(f x : Y) - q • (f y : Y)‖ - ‖(f x : Y) - r • (f y : Y)‖)
    (‖(x : X) - q • (y : X)‖ - ‖(x : X) - r • (y : X)‖)
  have he : signedDefect f q x y - signedDefect f r x y =
      (‖(f x : Y) - q • (f y : Y)‖ - ‖(f x : Y) - r • (f y : Y)‖) -
      (‖(x : X) - q • (y : X)‖ - ‖(x : X) - r • (y : X)‖) := by
    unfold signedDefect
    ring
  rw [he]
  linarith

theorem signedDefect_le_endpoints (f : UnitSphere X ≃ᵢ UnitSphere Y)
    {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) 1) (x y : UnitSphere X) :
    |signedDefect f q x y| ≤ 2 * q ∧
      |signedDefect f q x y| ≤ 2 * (1 - q) := by
  constructor
  · simpa [abs_of_nonneg hq.1] using signedDefect_lipschitz f q 0 x y
  · simpa [abs_of_nonpos (sub_nonpos.mpr hq.2)] using
      signedDefect_lipschitz f q 1 x y

theorem signedDefect_abs_le_one (f : UnitSphere X ≃ᵢ UnitSphere Y)
    {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) 1) (x y : UnitSphere X) :
    |signedDefect f q x y| ≤ 1 := by
  obtain ⟨h0, h1⟩ := signedDefect_le_endpoints f hq x y
  linarith

theorem absoluteDefects_bddAbove (f : UnitSphere X ≃ᵢ UnitSphere Y) :
    BddAbove (absoluteDefects f) := by
  refine ⟨1, ?_⟩
  rintro d ⟨q, hq, x, y, rfl⟩
  exact signedDefect_abs_le_one f hq x y

theorem zero_mem_absoluteDefects [Nonempty (UnitSphere X)]
    (f : UnitSphere X ≃ᵢ UnitSphere Y) : 0 ∈ absoluteDefects f := by
  let x : UnitSphere X := Classical.choice inferInstance
  exact ⟨0, ⟨le_rfl, zero_le_one⟩, x, x, by simp⟩

theorem hasDefectBound_maxDefect (f : UnitSphere X ≃ᵢ UnitSphere Y) :
    HasDefectBound f (maxDefect f) := by
  intro q hq x y
  exact le_csSup (absoluteDefects_bddAbove f) ⟨q, hq, x, y, rfl⟩

theorem maxDefect_nonneg [Nonempty (UnitSphere X)]
    (f : UnitSphere X ≃ᵢ UnitSphere Y) : 0 ≤ maxDefect f :=
  le_csSup (absoluteDefects_bddAbove f) (zero_mem_absoluteDefects f)

theorem maxDefect_le_one [Nonempty (UnitSphere X)]
    (f : UnitSphere X ≃ᵢ UnitSphere Y) : maxDefect f ≤ 1 := by
  apply csSup_le ⟨0, zero_mem_absoluteDefects f⟩
  rintro d ⟨q, hq, x, y, rfl⟩
  exact signedDefect_abs_le_one f hq x y

theorem absoluteDefects_symm (f : UnitSphere X ≃ᵢ UnitSphere Y) :
    absoluteDefects f.symm = absoluteDefects f := by
  ext d
  constructor
  · rintro ⟨q, hq, x, y, hd⟩
    obtain ⟨a, rfl⟩ := f.surjective x
    obtain ⟨b, rfl⟩ := f.surjective y
    exact ⟨q, hq, a, b, by simpa only [signedDefect_symm, abs_neg] using hd⟩
  · rintro ⟨q, hq, x, y, hd⟩
    exact ⟨q, hq, f x, f y, by simpa only [signedDefect_symm, abs_neg] using hd⟩

@[simp] theorem maxDefect_symm (f : UnitSphere X ≃ᵢ UnitSphere Y) :
    maxDefect f.symm = maxDefect f := by
  unfold maxDefect
  rw [absoluteDefects_symm]

theorem signedDefect_eq_zero_of_bound_zero {f : UnitSphere X ≃ᵢ UnitSphere Y}
    (h : HasDefectBound f 0) {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (x y : UnitSphere X) : signedDefect f q x y = 0 := by
  exact abs_nonpos_iff.mp (h q hq x y)

end Tingley

end

end OAI
