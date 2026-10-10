import Mathlib
import OAI.Geometry.RecorderBoxes.Bounds
import OAI.Analysis.SolenoidalShears.Affine

namespace OAI

/-! All-stage affine branch paths and nonterminal strip avoidance. -/

namespace Solenoidal
namespace Bridge
variable {M : Machine}
noncomputable def branchStage {m : ℕ} (e : Recorder.Letter M ≃ Fin (m + 1)) (i : Branch M)
    (j : Fin 7) (θ : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  let p := (sourceRectangle e i).center
  let q := (targetRectangle e i).center
  let delta := x - p
  let lam := Radix.scale m i.move
  match j with
  | 0 => x
  | 1 => p + Shear.partialStage lam 0 θ delta
  | 2 => p + Shear.partialStage lam 1 θ delta
  | 3 => p + Shear.partialStage lam 2 θ delta
  | 4 => p + Shear.partialStage lam 3 θ delta
  | 5 => Shear.interpolate p q θ + (lam * delta.1, delta.2 / lam)
  | 6 => affine e i x

 
theorem branchStage_join {m : ℕ} (e : Recorder.Letter M ≃ Fin (m + 1)) (i : Branch M)
    (x : ℝ × ℝ) (j : Fin 6) :
    branchStage e i j.castSucc 1 x = branchStage e i j.succ 0 x := by
  have hlam := Radix.scale_pos m i.move
  fin_cases j
  · simp [branchStage, Shear.endpoint]
  · simp [branchStage]
  · simp [branchStage]
  · simp [branchStage]
  · simp [branchStage, Shear.four_shears _ _ _ hlam.ne', Shear.interpolate]
  · simp [branchStage, Shear.interpolate, affine_centered]

 

theorem branchStage_x_bounds {m : ℕ} (e : Recorder.Letter M ≃ Fin (m + 1)) (i : Branch M)
    {x : ℝ × ℝ} (hx : x ∈ (sourceRectangle e i).carrier)
    {a b : ℝ} (hp : a ≤ (sourceRectangle e i).center.1 ∧ (sourceRectangle e i).center.1 ≤ b)
    (hq : a ≤ (targetRectangle e i).center.1 ∧ (targetRectangle e i).center.1 ≤ b)
    (j : Fin 7) {θ : ℝ} (hθ : θ ∈ Set.Icc 0 1) :
    a - kappa M ≤ (branchStage e i j θ x).1 ∧
      (branchStage e i j θ x).1 ≤ b + kappa M := by
  have hκ := kappa_pos M
  have ho := branch_offset_bounds e i hx
  have hpath := (Shear.excursion (Radix.scale_pos m i.move) (by linarith : 0 < kappa M / 2)
    ho.1 ho.2.1 ho.2.2.1 ho.2.2.2).2.2
  have hs : ∀ k : Fin 4,
      a - kappa M ≤ ((sourceRectangle e i).center +
        Shear.partialStage (Radix.scale m i.move) k θ (x - (sourceRectangle e i).center)).1 ∧
      ((sourceRectangle e i).center +
        Shear.partialStage (Radix.scale m i.move) k θ (x - (sourceRectangle e i).center)).1 ≤
          b + kappa M := by
    intro k
    have hm : -(2 * (kappa M / 2)) ≤
        (Shear.partialStage (Radix.scale m i.move) k θ (x - (sourceRectangle e i).center)).1 ∧
        (Shear.partialStage (Radix.scale m i.move) k θ (x - (sourceRectangle e i).center)).1 ≤
          2 * (kappa M / 2) := abs_le.mp (hpath k θ hθ).1
    change a - kappa M ≤ (sourceRectangle e i).center.1 + _ ∧
      (sourceRectangle e i).center.1 + _ ≤ b + kappa M
    constructor <;> linarith [hm.1, hm.2, hp.1, hp.2]
  have hi : a ≤ (Shear.interpolate (sourceRectangle e i).center
      (targetRectangle e i).center θ).1 ∧
      (Shear.interpolate (sourceRectangle e i).center (targetRectangle e i).center θ).1 ≤ b := by
    have hp₀ := mul_le_mul_of_nonneg_left hp.1 (show 0 ≤ 1 - θ by linarith [hθ.2])
    have hq₀ := mul_le_mul_of_nonneg_left hq.1 hθ.1
    have hp₁ := mul_le_mul_of_nonneg_left hp.2 (show 0 ≤ 1 - θ by linarith [hθ.2])
    have hq₁ := mul_le_mul_of_nonneg_left hq.2 hθ.1
    dsimp [Shear.interpolate]
    constructor <;> nlinarith
  fin_cases j
  · have hm := abs_le.mp ho.1
    change a - kappa M ≤ x.1 ∧ x.1 ≤ b + kappa M
    constructor <;> linarith [hm.1, hm.2, hp.1, hp.2]
  · exact hs 0
  · exact hs 1
  · exact hs 2
  · exact hs 3
  · have hm := abs_le.mp ho.2.2.1
    constructor <;> dsimp [branchStage] <;>
      linarith [hi.1, hi.2, hm.1, hm.2]
  · have hm := abs_le.mp ho.2.2.1
    change a - kappa M ≤ (affine e i x).1 ∧ (affine e i x).1 ≤ b + kappa M
    rw [affine_centered]
    constructor <;> dsimp only [Prod.fst_add] <;> linarith [hm.1, hm.2, hq.1, hq.2]

 

theorem nonterminal_stage_safe {m : ℕ} (e : Recorder.Letter M ≃ Fin (m + 1)) (i : Branch M)
    (hs : terminalControl i.src = false) (ht : terminalControl i.dst = false)
    {x : ℝ × ℝ} (hx : x ∈ (sourceRectangle e i).carrier)
    (j : Fin 7) {θ : ℝ} (hθ : θ ∈ Set.Icc 0 1) :
    (branchStage e i j θ x).1 ≤ 9 / 32 ∧ (branchStage e i j θ x).1 < 1 / 2 := by
  have hsp := physical_center_bounds i.src (source_in_unit (e i.read) (e i.left))
  have htp := physical_center_bounds i.dst (target_in_unit (e i.written) (e i.left) i.move)
  have hsx := state_extent i.src
  have htx := state_extent i.dst
  simp only [hs, Bool.false_eq_true, ↓reduceIte] at hsx
  simp only [ht, Bool.false_eq_true, ↓reduceIte] at htx
  have hsp' : (sourceRectangle e i).center.1 ≤ origin i.src + kappa M := hsp.2.1
  have htp' : (targetRectangle e i).center.1 ≤ origin i.dst + kappa M := htp.2.1
  have h₁ : (1 / 8 : ℝ) ≤ (sourceRectangle e i).center.1 ∧
      (sourceRectangle e i).center.1 ≤ 1 / 4 :=
    ⟨hsx.1.trans hsp.1, by linarith [hsp', hsx.2]⟩
  have h₂ : (1 / 8 : ℝ) ≤ (targetRectangle e i).center.1 ∧
      (targetRectangle e i).center.1 ≤ 1 / 4 :=
    ⟨htx.1.trans htp.1, by linarith [htp', htx.2]⟩
  have hbound := branchStage_x_bounds e i hx h₁ h₂ j hθ
  have hle : (branchStage e i j θ x).1 ≤ 9 / 32 := by
    linarith [hbound.2, kappa_le M]
  exact ⟨hle, lt_of_le_of_lt hle (by norm_num)⟩
end Bridge
end Solenoidal

end OAI
