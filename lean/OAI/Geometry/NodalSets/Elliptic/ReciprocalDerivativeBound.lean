import Mathlib.Analysis.Calculus.ContDiff.Bounds

namespace OAI

namespace Yau.Geometry
open Set Filter
open scoped ContDiff Topology
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem reciprocal_derivative_bound (r : ℕ) :
    ∃ C > 0, ∀ (f : E → ℝ), ContDiff ℝ ∞ f → ∀ (x : E), f x ≠ 0 →
      ∀ (B : ℝ), 0 ≤ B →
      (∀ i, 1 ≤ i → i ≤ r → ‖iteratedFDeriv ℝ i f x‖ ≤ |f x| *B^i) →
      ‖iteratedFDeriv ℝ r (fun y ↦ (f y)⁻¹) x‖ ≤ C*|f x|⁻¹*B^r := by
  let C : ℝ := 1 + ∑ i ∈ Finset.range (r+1), ‖iteratedFDeriv ℝ i (fun t : ℝ ↦ t⁻¹) 1‖
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨(r.factorial:ℝ)*C, mul_pos (by positivity) hC, ?_⟩
  intro f hf x hx B hB hb
  let F : E → ℝ := fun y ↦ (f x)⁻¹ * f y
  have hF : ContDiff ℝ ∞ F := contDiff_const.mul hf
  have hFx : F x = 1 := by simp [F,hx]
  let s : Set E := F ⁻¹' Ioi 0
  have hs : IsOpen s := isOpen_Ioi.preimage hF.continuous
  have hxs : x ∈ s := by simp [s,hFx]
  have hinv : ContDiffOn ℝ ∞ (fun t : ℝ ↦ t⁻¹) (Ioi 0) :=
    contDiffOn_id.inv (fun t ht ↦ ne_of_gt ht)
  have hi (i : ℕ) : iteratedFDerivWithin ℝ i (fun t : ℝ ↦ t⁻¹) (Ioi 0) (F x) =
      iteratedFDeriv ℝ i (fun t : ℝ ↦ t⁻¹) 1 := by
    rw [hFx, iteratedFDerivWithin_of_isOpen i isOpen_Ioi (by norm_num : (1:ℝ) ∈ Ioi 0)]
  have hbF (i : ℕ) (hi1 : 1 ≤ i) (hir : i ≤ r) :
      ‖iteratedFDerivWithin ℝ i F s x‖ ≤ B^i := by
    rw [iteratedFDerivWithin_of_isOpen i hs hxs]
    change ‖iteratedFDeriv ℝ i ((f x)⁻¹ • f) x‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply (hf.of_le (by exact_mod_cast (show (i:ℕ∞) ≤ ⊤ from le_top))).contDiffAt, norm_smul,
      Real.norm_eq_abs, abs_inv]
    calc
      |f x|⁻¹ * ‖iteratedFDeriv ℝ i f x‖ ≤ |f x|⁻¹ * (|f x| *B^i) :=
        mul_le_mul_of_nonneg_left (hb i hi1 hir) (by positivity)
      _ = B^i := by rw [← mul_assoc, inv_mul_cancel₀ (abs_ne_zero.mpr hx), one_mul]
  have hcF (i : ℕ) (hir : i ≤ r) :
      ‖iteratedFDerivWithin ℝ i (fun t : ℝ ↦ t⁻¹) (Ioi 0) (F x)‖ ≤ C := by
    rw [hi]
    have h := Finset.single_le_sum (fun j _ ↦ norm_nonneg
      (iteratedFDeriv ℝ j (fun t : ℝ ↦ t⁻¹) 1))
      (Finset.mem_range.mpr (show i < r+1 by omega))
    dsimp [C]
    linarith
  have hcomp := norm_iteratedFDerivWithin_comp_le hinv hF.contDiffOn (by exact_mod_cast (show (r:ℕ∞) ≤ ⊤ from le_top)) isOpen_Ioi.uniqueDiffOn hs.uniqueDiffOn
    (show MapsTo F s (Ioi 0) from fun _ hy ↦ hy) hxs hcF hbF
  rw [iteratedFDerivWithin_of_isOpen r hs hxs] at hcomp
  have hg : (fun y ↦ (f y)⁻¹) = (f x)⁻¹ • ((fun t : ℝ ↦ t⁻¹) ∘ F) := by
    funext y
    simp [F,mul_inv_rev,hx,mul_comm]
  have hlocal : ContDiffAt ℝ (r:ℕ∞ω) ((fun t : ℝ ↦ t⁻¹) ∘ F) x :=
    ((hinv.contDiffAt (isOpen_Ioi.mem_nhds (by rw [hFx]; norm_num))).comp x
      hF.contDiffAt).of_le (by exact_mod_cast (show (r:ℕ∞) ≤ ⊤ from le_top))
  rw [hg,iteratedFDeriv_const_smul_apply hlocal,norm_smul,Real.norm_eq_abs,abs_inv]
  calc
    _ ≤ |f x|⁻¹ * ((r.factorial:ℝ)*C*B^r) :=
      mul_le_mul_of_nonneg_left hcomp (by positivity)
    _ = _ := by ring

end
end Yau.Geometry

end OAI
