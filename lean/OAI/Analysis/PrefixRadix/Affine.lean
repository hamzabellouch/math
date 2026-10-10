import Mathlib
import OAI.Analysis.PrefixRadix.Intervals

namespace OAI

/-! Positive affine prefix replacements and disjoint full rectangles. -/

noncomputable section
open scoped ContDiff
namespace PrefixFlows
namespace Radix
namespace System
variable {A : Type*} (C : System A)
def prefixMap (v w : List A) (x : ℝ) : ℝ :=
  C.finiteCode w + (C.rate ^ w.length / C.rate ^ v.length) * (x - C.finiteCode v)

theorem prefixMap_scale_pos (v w : List A) : 0 < C.rate ^ w.length / C.rate ^ v.length :=
  div_pos (pow_pos C.rate_pos _) (pow_pos C.rate_pos _)

theorem prefixMap_on_codes (v w : List A) (L : Interspersed.Stack A) :
    C.prefixMap v w (C.code (Interspersed.prepend v L)) =
      C.code (Interspersed.prepend w L) := by
  rw [C.code_prepend, C.code_prepend]
  dsimp [prefixMap]
  have hne : C.rate ^ v.length ≠ 0 := ne_of_gt (pow_pos C.rate_pos _)
  field_simp
  ring

 
theorem prefixMap_inverse (v w : List A) (x : ℝ) :
    C.prefixMap w v (C.prefixMap v w x) = x := by
  dsimp only [prefixMap]
  have hv := ne_of_gt (pow_pos C.rate_pos v.length)
  have hw := ne_of_gt (pow_pos C.rate_pos w.length)
  field_simp
  ring

 

theorem prefixMap_mem_interval (v w : List A) {x : ℝ} (hx : x ∈ C.interval v) :
    C.prefixMap v w x ∈ C.interval w := by
  have hp := (C.prefixMap_scale_pos v w).le
  have hne := ne_of_gt (pow_pos C.rate_pos v.length)
  have hc : C.rate ^ w.length / C.rate ^ v.length * C.rate ^ v.length =
      C.rate ^ w.length := by field_simp
  have hm := mul_le_mul_of_nonneg_left
    (show x - C.finiteCode v ≤ C.rate ^ v.length by linarith [hx.2]) hp
  rw [hc] at hm
  exact ⟨le_add_of_nonneg_right (mul_nonneg hp (sub_nonneg.mpr hx.1)),
    add_le_add_right hm _⟩

 
theorem prefixMap_image_interval (v w : List A) :
    C.prefixMap v w '' C.interval v = C.interval w := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact C.prefixMap_mem_interval v w hx
  · intro y hy
    exact ⟨C.prefixMap w v y, C.prefixMap_mem_interval w v hy, C.prefixMap_inverse w v y⟩

 
def stackCylinder (v : List A) : Set (Interspersed.Stack A) :=
  Set.range (Interspersed.prepend v)

theorem prefix_has_common_extension (blank : A) {v w : List A} (h : v <+: w) :
    ∃ L, L ∈ stackCylinder v ∧ L ∈ stackCylinder w := by
  rcases h with ⟨u, hu⟩
  refine ⟨Interspersed.prepend w (fun _ => blank), ?_, ⟨(fun _ => blank), rfl⟩⟩
  refine ⟨Interspersed.prepend u (fun _ => blank), ?_⟩
  rw [← hu, Interspersed.prepend_append]

theorem compatible_has_common_extension (blank : A) {v w : List A}
    (h : v <+: w ∨ w <+: v) :
    ∃ L, L ∈ stackCylinder v ∧ L ∈ stackCylinder w := by
  rcases h with h | h
  · exact prefix_has_common_extension blank h
  · rcases prefix_has_common_extension blank h with ⟨L, hL, hL'⟩
    exact ⟨L, hL', hL⟩

 

theorem overlapping_intervals_compatible {v w : List A} {x : ℝ}
    (hx : x ∈ C.interval v) (hy : x ∈ C.interval w) : v <+: w ∨ w <+: v := by
  classical
  by_cases h : v <+: w
  · exact Or.inl h
  by_cases h' : w <+: v
  · exact Or.inr h'
  exact ((Set.disjoint_left.mp (C.incompatible_intervals_disjoint v w h h')) hx hy).elim

 

theorem product_rectangles_disjoint (blank : A) (v₁ v₂ w₁ w₂ : List A)
    (h : Disjoint ((stackCylinder v₁).prod (stackCylinder v₂))
      ((stackCylinder w₁).prod (stackCylinder w₂))) :
    Disjoint ((C.interval v₁).prod (C.interval v₂))
      ((C.interval w₁).prod (C.interval w₂)) := by
  rw [Set.disjoint_left]
  intro x hx hy
  rcases compatible_has_common_extension blank (C.overlapping_intervals_compatible hx.1 hy.1)
    with ⟨L, hvL, hwL⟩
  rcases compatible_has_common_extension blank (C.overlapping_intervals_compatible hx.2 hy.2)
    with ⟨R, hvR, hwR⟩
  have hL : (L, R) ∈ (stackCylinder v₁).prod (stackCylinder v₂) := ⟨hvL, hvR⟩
  have hR : (L, R) ∈ (stackCylinder w₁).prod (stackCylinder w₂) := ⟨hwL, hwR⟩
  exact Set.disjoint_left.mp h hL hR
end System
end Radix
end PrefixFlows
end

end OAI
