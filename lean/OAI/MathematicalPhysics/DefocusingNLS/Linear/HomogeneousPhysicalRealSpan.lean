import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalSpan

namespace OAI

/-! # Real and imaginary coordinates of the complex physical symmetry span -/

namespace DefocusingNLS

section
variable (a k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
local notation "H" => HomogeneousY a k
local notation "ι" => homogeneousComplexEmbed a k ha ha1 hk
local notation "X" => homogeneousComplexReal a k ha ha1 hk
local notation "Y" => homogeneousComplexImag a k ha ha1 hk

theorem homogeneousComplexReal_smul (c : ℂ) (z : H × H) :
    X (c • z) = c.re • X z - c.im • Y z := by
  have he : c • z = c.re • z + c.im • (Complex.I • z) := by
    conv_lhs => rw [← c.re_add_im]
    simp only [add_smul, mul_smul, Complex.coe_smul]
    rfl
  rw [he, map_add, map_smul, map_smul, homogeneousComplexReal_I, smul_neg, sub_eq_add_neg]

theorem homogeneousComplexImag_smul (c : ℂ) (z : H × H) :
    Y (c • z) = c.im • X z + c.re • Y z := by
  have he : c • z = c.re • z + c.im • (Complex.I • z) := by
    conv_lhs => rw [← c.re_add_im]
    simp only [add_smul, mul_smul, Complex.coe_smul]
    rfl
  rw [he, map_add, map_smul, map_smul, homogeneousComplexImag_I, add_comm]

theorem homogeneousComplexEmbed_coordinates (z : H × H) :
    ι (X z) + Complex.I • ι (Y z) = z := by
  apply Prod.ext
  · exact homogeneousComplexCoordinates_first a k ha ha1 hk z
  · exact homogeneousComplexCoordinates_second a k ha ha1 hk z

theorem homogeneous_frame_real_coordinates
    (F : ProfileSymmetryParameters →L[ℝ] H) (z : H × H)
    (hz : z ∈ Submodule.span ℂ (Set.range (fun p => ι (F p)))) :
    X z ∈ F.range ∧ Y z ∈ F.range := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    rcases hz with ⟨p, rfl⟩
    simp only [homogeneousComplexReal_embed, homogeneousComplexImag_embed]
    exact ⟨⟨p, rfl⟩, F.range.zero_mem⟩
  | zero => simp only [map_zero]; exact ⟨F.range.zero_mem, F.range.zero_mem⟩
  | add x y _ _ hx hy =>
    simp only [map_add]
    exact ⟨F.range.add_mem hx.1 hy.1, F.range.add_mem hx.2 hy.2⟩
  | smul c z _ hz =>
    rw [homogeneousComplexReal_smul, homogeneousComplexImag_smul]
    exact ⟨F.range.sub_mem (F.range.smul_mem _ hz.1) (F.range.smul_mem _ hz.2),
      F.range.add_mem (F.range.smul_mem _ hz.1) (F.range.smul_mem _ hz.2)⟩

end
end DefocusingNLS

end OAI
