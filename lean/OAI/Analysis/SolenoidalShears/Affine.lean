import Mathlib

namespace OAI

/-! Four affine shears, intermediate excursion bounds and endpoint identities. -/

namespace Solenoidal
namespace Shear
abbrev Plane := ℝ × ℝ

def X (a : ℝ) (p : Plane) : Plane := (p.1 + a * p.2, p.2)
def Y (a : ℝ) (p : Plane) : Plane := (p.1, p.2 + a * p.1)

 
noncomputable def endpoint (lam : ℝ) (p : Plane) : Fin 5 → Plane :=
  ![p, Y (-lam) p, X (lam⁻¹ - 1) (Y (-lam) p),
    Y 1 (X (lam⁻¹ - 1) (Y (-lam) p)),
    X (lam - 1) (Y 1 (X (lam⁻¹ - 1) (Y (-lam) p)))]

 
noncomputable def partialStage (lam : ℝ) (j : Fin 4) (θ : ℝ) (p : Plane) : Plane :=
  let q := endpoint lam p j.castSucc
  match j with
  | 0 => Y (θ * (-lam)) q
  | 1 => X (θ * (lam⁻¹ - 1)) q
  | 2 => Y θ q
  | 3 => X (θ * (lam - 1)) q

def interpolate (p q : Plane) (θ : ℝ) : Plane :=
  ((1 - θ) * p.1 + θ * q.1, (1 - θ) * p.2 + θ * q.2)

 
theorem partialStage_interpolate (lam : ℝ) (j : Fin 4) (θ : ℝ) (p : Plane) :
    partialStage lam j θ p =
      interpolate (endpoint lam p j.castSucc) (endpoint lam p j.succ) θ := by
  fin_cases j <;> apply Prod.ext <;> dsimp [partialStage, endpoint, X, Y, interpolate] <;> ring

theorem endpoint_one (lam r s : ℝ) : endpoint lam (r, s) 1 = (r, s - lam * r) := by
  apply Prod.ext <;> dsimp [endpoint, X, Y]
  ring

theorem endpoint_two (lam r s : ℝ) (hlam : lam ≠ 0) :
    endpoint lam (r, s) 2 = (lam * r + (lam⁻¹ - 1) * s, s - lam * r) := by
  apply Prod.ext <;> dsimp [endpoint, X, Y] <;> field_simp <;> ring

theorem endpoint_three (lam r s : ℝ) (hlam : lam ≠ 0) :
    endpoint lam (r, s) 3 = (lam * r + (lam⁻¹ - 1) * s, s / lam) := by
  apply Prod.ext <;> dsimp [endpoint, X, Y] <;> field_simp <;> ring

 
theorem four_shears (lam r s : ℝ) (hlam : lam ≠ 0) :
    endpoint lam (r, s) 4 = (lam * r, s / lam) := by
  apply Prod.ext <;> dsimp [endpoint, X, Y] <;> field_simp <;> ring

 
theorem middle_term_bound {lam s h : ℝ} (hlam : 0 < lam)
    (hs : |s| ≤ h) (hslam : |s / lam| ≤ h) : |(lam⁻¹ - 1) * s| ≤ h := by
  have heq : (lam⁻¹ - 1) * s = s / lam - s := by ring
  rw [heq]
  rcases abs_le.mp hs with ⟨hs₀, hs₁⟩
  rcases abs_le.mp hslam with ⟨hdiv₀, hdiv₁⟩
  apply abs_le.mpr
  by_cases hsign : 0 ≤ s
  · have hdiv := div_nonneg hsign hlam.le
    constructor <;> linarith
  · have hneg : s ≤ 0 := le_of_not_ge hsign
    have hdiv : s / lam ≤ 0 := div_nonpos_of_nonpos_of_nonneg hneg hlam.le
    constructor <;> linarith

 
theorem endpoint_bound {lam r s h : ℝ} (hlam : 0 < lam) (hh : 0 < h)
    (hr : |r| ≤ h) (hs : |s| ≤ h) (hlamr : |lam * r| ≤ h) (hslam : |s / lam| ≤ h)
    (j : Fin 5) :
    |(endpoint lam (r, s) j).1| ≤ 2 * h ∧ |(endpoint lam (r, s) j).2| ≤ 2 * h := by
  have hsub : |s - lam * r| ≤ 2 * h := by
    calc
      |s - lam * r| ≤ |s| + |lam * r| := abs_sub _ _
      _ ≤ h + h := add_le_add hs hlamr
      _ = 2 * h := by ring
  have hmid : |lam * r + (lam⁻¹ - 1) * s| ≤ 2 * h := by
    calc
      |lam * r + (lam⁻¹ - 1) * s| ≤ |lam * r| + |(lam⁻¹ - 1) * s| := abs_add_le _ _
      _ ≤ h + h := add_le_add hlamr (middle_term_bound hlam hs hslam)
      _ = 2 * h := by ring
  have hle : h ≤ 2 * h := by linarith
  fin_cases j
  · exact ⟨hr.trans hle, hs.trans hle⟩
  · change |(endpoint lam (r, s) 1).1| ≤ 2 * h ∧
        |(endpoint lam (r, s) 1).2| ≤ 2 * h
    rw [endpoint_one]
    exact ⟨hr.trans hle, hsub⟩
  · change |(endpoint lam (r, s) 2).1| ≤ 2 * h ∧
        |(endpoint lam (r, s) 2).2| ≤ 2 * h
    rw [endpoint_two lam r s hlam.ne']
    exact ⟨hmid, hsub⟩
  · change |(endpoint lam (r, s) 3).1| ≤ 2 * h ∧
        |(endpoint lam (r, s) 3).2| ≤ 2 * h
    rw [endpoint_three lam r s hlam.ne']
    exact ⟨hmid, hslam.trans hle⟩
  · change |(endpoint lam (r, s) 4).1| ≤ 2 * h ∧
        |(endpoint lam (r, s) 4).2| ≤ 2 * h
    rw [four_shears lam r s hlam.ne']
    exact ⟨hlamr.trans hle, hslam.trans hle⟩

theorem abs_interpolate_le {a b C θ : ℝ} (ha : |a| ≤ C) (hb : |b| ≤ C)
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) : |(1 - θ) * a + θ * b| ≤ C := by
  calc
    |(1 - θ) * a + θ * b| ≤ |(1 - θ) * a| + |θ * b| := abs_add_le _ _
    _ = (1 - θ) * |a| + θ * |b| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hθ₁), abs_of_nonneg hθ₀]
    _ ≤ (1 - θ) * C + θ * C :=
      add_le_add (mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr hθ₁))
        (mul_le_mul_of_nonneg_left hb hθ₀)
    _ = C := by ring

 
theorem excursion {lam r s h : ℝ} (hlam : 0 < lam) (hh : 0 < h)
    (hr : |r| ≤ h) (hs : |s| ≤ h) (hlamr : |lam * r| ≤ h) (hslam : |s / lam| ≤ h) :
    endpoint lam (r, s) 4 = (lam * r, s / lam) ∧
    (∀ j : Fin 5, |(endpoint lam (r, s) j).1| ≤ 2 * h ∧
      |(endpoint lam (r, s) j).2| ≤ 2 * h) ∧
    (∀ (j : Fin 4) (θ : ℝ), θ ∈ Set.Icc 0 1 →
      |(partialStage lam j θ (r, s)).1| ≤ 2 * h ∧
      |(partialStage lam j θ (r, s)).2| ≤ 2 * h) := by
  have hb := endpoint_bound hlam hh hr hs hlamr hslam
  refine ⟨four_shears lam r s hlam.ne', hb, ?_⟩
  intro j θ hθ
  rw [partialStage_interpolate]
  exact ⟨abs_interpolate_le (hb j.castSucc).1 (hb j.succ).1 hθ.1 hθ.2,
    abs_interpolate_le (hb j.castSucc).2 (hb j.succ).2 hθ.1 hθ.2⟩

@[simp] theorem partialStage_zero (lam : ℝ) (j : Fin 4) (p : Plane) :
    partialStage lam j 0 p = endpoint lam p j.castSucc := by
  rw [partialStage_interpolate]
  apply Prod.ext <;> dsimp [interpolate] <;> ring

@[simp] theorem partialStage_one (lam : ℝ) (j : Fin 4) (p : Plane) :
    partialStage lam j 1 p = endpoint lam p j.succ := by
  rw [partialStage_interpolate]
  apply Prod.ext <;> dsimp [interpolate] <;> ring
end Shear
end Solenoidal

end OAI
