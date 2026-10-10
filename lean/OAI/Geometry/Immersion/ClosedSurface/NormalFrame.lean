import Mathlib

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.NormalFrame
abbrev Vec := Fin 4 → ℝ

def minor3 (X Y B : Vec) (i j k : Fin 4) : ℝ :=
  X i * (Y j * B k - Y k * B j) - X j * (Y i * B k - Y k * B i) +
    X k * (Y i * B j - Y j * B i)



def perpProduct (X Y B : Vec) : Vec :=
  ![-minor3 X Y B 1 2 3, minor3 X Y B 0 2 3,
    -minor3 X Y B 0 1 3, minor3 X Y B 0 1 2]

def gramDet (X Y : Vec) : ℝ := (X ⬝ᵥ X) * (Y ⬝ᵥ Y) - (X ⬝ᵥ Y) ^ 2

def unitPerp (X Y B : Vec) : Vec :=
  (Real.sqrt (perpProduct X Y B ⬝ᵥ perpProduct X Y B))⁻¹ • perpProduct X Y B

lemma dot_perp_left (X Y B : Vec) : X ⬝ᵥ perpProduct X Y B = 0 := by
  simp [dotProduct, Fin.sum_univ_succ, perpProduct, minor3]
  ring

lemma dot_perp_middle (X Y B : Vec) : Y ⬝ᵥ perpProduct X Y B = 0 := by
  simp [dotProduct, Fin.sum_univ_succ, perpProduct, minor3]
  ring

lemma dot_perp_right (X Y B : Vec) : B ⬝ᵥ perpProduct X Y B = 0 := by
  simp [dotProduct, Fin.sum_univ_succ, perpProduct, minor3]
  ring

lemma perp_sq (X Y B : Vec) :
    perpProduct X Y B ⬝ᵥ perpProduct X Y B =
      gramDet X Y * (B ⬝ᵥ B) - (X ⬝ᵥ X) * (Y ⬝ᵥ B) ^ 2 -
        (Y ⬝ᵥ Y) * (X ⬝ᵥ B) ^ 2 + 2 * (X ⬝ᵥ Y) * (X ⬝ᵥ B) * (Y ⬝ᵥ B) := by
  simp [dotProduct, Fin.sum_univ_succ, perpProduct, minor3, gramDet]
  ring

lemma gramDet_sum_sq (X Y : Vec) : gramDet X Y =
    (X 0 * Y 1 - X 1 * Y 0) ^ 2 + (X 0 * Y 2 - X 2 * Y 0) ^ 2 +
    (X 0 * Y 3 - X 3 * Y 0) ^ 2 + (X 1 * Y 2 - X 2 * Y 1) ^ 2 +
    (X 1 * Y 3 - X 3 * Y 1) ^ 2 + (X 2 * Y 3 - X 3 * Y 2) ^ 2 := by
  simp [gramDet, dotProduct, Fin.sum_univ_succ]
  ring

lemma gramDet_nonneg (X Y : Vec) : 0 ≤ gramDet X Y := by
  rw [gramDet_sum_sq]
  positivity

lemma gramDet_pos {X Y : Vec} (h : gramDet X Y ≠ 0) : 0 < gramDet X Y :=
  (gramDet_nonneg X Y).lt_of_ne' h

lemma perp_sq_pos {X Y B : Vec} (hD : gramDet X Y ≠ 0) (hB : B ≠ 0)
    (hX : X ⬝ᵥ B = 0) (hY : Y ⬝ᵥ B = 0) :
    0 < perpProduct X Y B ⬝ᵥ perpProduct X Y B := by
  rw [perp_sq, hX, hY]
  simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero, add_zero]
  have hb : 0 < B ⬝ᵥ B := by
    have hbb : 0 ≤ B ⬝ᵥ B := Finset.sum_nonneg (fun i _ => mul_self_nonneg (B i))
    exact hbb.lt_of_ne' ((dotProduct_self_eq_zero).not.mpr hB)
  exact mul_pos (gramDet_pos hD) hb

lemma unitPerp_orthogonal (X Y B : Vec) :
    X ⬝ᵥ unitPerp X Y B = 0 ∧ Y ⬝ᵥ unitPerp X Y B = 0 ∧ B ⬝ᵥ unitPerp X Y B = 0 := by
  simp only [unitPerp, dotProduct_smul, smul_eq_mul, dot_perp_left, dot_perp_middle,
    dot_perp_right, mul_zero, and_self]

lemma unitPerp_unit {X Y B : Vec} (hD : gramDet X Y ≠ 0) (hB : B ≠ 0)
    (hX : X ⬝ᵥ B = 0) (hY : Y ⬝ᵥ B = 0) : unitPerp X Y B ⬝ᵥ unitPerp X Y B = 1 := by
  have hp := perp_sq_pos hD hB hX hY
  have hs : Real.sqrt (perpProduct X Y B ⬝ᵥ perpProduct X Y B) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hp)
  have he := Real.sq_sqrt hp.le
  simp only [unitPerp, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  field_simp
  nlinarith [he]

section Smoothness
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {X Y B : E → Vec} {p : E}

lemma contDiffAt_minor3 (hX : ContDiffAt ℝ ∞ X p) (hY : ContDiffAt ℝ ∞ Y p)
    (hB : ContDiffAt ℝ ∞ B p) (i j k : Fin 4) :
    ContDiffAt ℝ ∞ (fun q => minor3 (X q) (Y q) (B q) i j k) p := by
  have hx := contDiffAt_pi.mp hX
  have hy := contDiffAt_pi.mp hY
  have hb := contDiffAt_pi.mp hB
  exact ((hx i).mul (((hy j).mul (hb k)).sub ((hy k).mul (hb j)))).sub
    ((hx j).mul (((hy i).mul (hb k)).sub ((hy k).mul (hb i)))) |>.add
    ((hx k).mul (((hy i).mul (hb j)).sub ((hy j).mul (hb i))))

lemma contDiffAt_perpProduct (hX : ContDiffAt ℝ ∞ X p) (hY : ContDiffAt ℝ ∞ Y p)
    (hB : ContDiffAt ℝ ∞ B p) : ContDiffAt ℝ ∞ (fun q => perpProduct (X q) (Y q) (B q)) p := by
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact (contDiffAt_minor3 hX hY hB 1 2 3).neg
  · exact contDiffAt_minor3 hX hY hB 0 2 3
  · exact (contDiffAt_minor3 hX hY hB 0 1 3).neg
  · exact contDiffAt_minor3 hX hY hB 0 1 2

lemma contDiffAt_unitPerp (hX : ContDiffAt ℝ ∞ X p) (hY : ContDiffAt ℝ ∞ Y p)
    (hB : ContDiffAt ℝ ∞ B p) (hD : gramDet (X p) (Y p) ≠ 0) (hb : B p ≠ 0)
    (hXB : X p ⬝ᵥ B p = 0) (hYB : Y p ⬝ᵥ B p = 0) :
    ContDiffAt ℝ ∞ (fun q => unitPerp (X q) (Y q) (B q)) p := by
  have hv := contDiffAt_perpProduct hX hY hB
  have hs : ContDiffAt ℝ ∞ (fun q => perpProduct (X q) (Y q) (B q) ⬝ᵥ
      perpProduct (X q) (Y q) (B q)) p :=
    ContDiffAt.sum (fun i _ => (contDiffAt_pi.mp hv i).mul (contDiffAt_pi.mp hv i))
  have hp := perp_sq_pos hD hb hXB hYB
  exact ((hs.sqrt (ne_of_gt hp)).inv (ne_of_gt (Real.sqrt_pos.2 hp))).smul hv

end Smoothness
end ClosedSurfaceR4.NormalFrame

end

end OAI
