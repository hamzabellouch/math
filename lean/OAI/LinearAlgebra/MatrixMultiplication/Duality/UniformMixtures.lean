import OAI.LinearAlgebra.MatrixMultiplication.Completion.ColorLaws
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.UniformCoordinate
import OAI.LinearAlgebra.MatrixMultiplication.Duality.EntropyHelpers

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

universe uCoord

namespace MatrixMultiplication.DualUniformMixtures

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels CompletionColorLaws
open CompletionLaws DualEntropyHelpers
open scoped BigOperators
attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

variable {X Y Z : Type uCoord} {U A : Type*} [Fintype X] [Fintype Y] [Fintype Z]
  [Fintype U] [Fintype A]

theorem uniform_coordinate_card_pos (p : FiniteLaw A) (f : A → U)
    (P : U → Prop) (h : UniformCoordinate p f P) :
    0 < Fintype.card {x // P x} := by
  by_contra hn
  have hz : Fintype.card {x // P x} = 0 := Nat.eq_zero_of_not_pos hn
  have ht := (p.map f).total
  have hmass : ∀ x, (p.map f).mass x =
      if P x then (Fintype.card {x // P x} : ℝ)⁻¹ else 0 := h
  simp_rw [hmass] at ht
  simp [hz] at ht

theorem colorMix_map_comp_mass (S : FlaggedTensor X Y Z) (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1) (f : Leaf S → U) (x : U) :
    ((colorMix S center output pc po α hα hα').map f).mass x =
      α * (pc.map (fun a => f a.val)).mass x +
        (1 - α) * (po.map (fun a => f a.val)).mass x := by
  rw [colorMix_map_mass, map_comp_mass, map_comp_mass]

theorem colorMix_map_of_common (S : FlaggedTensor X Y Z) (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1) (f : Leaf S → U)
    (hcommon : ∀ x, (pc.map (fun a => f a.val)).mass x =
      (po.map (fun a => f a.val)).mass x) (x : U) :
    ((colorMix S center output pc po α hα hα').map f).mass x =
      (pc.map (fun a => f a.val)).mass x := by
  rw [colorMix_map_comp_mass, ← hcommon x]
  ring

theorem colorMix_uniform_common (S : FlaggedTensor X Y Z) (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1) (P : X → Prop)
    (hc : UniformCoordinate pc (fun a => a.val.val.1) P)
    (ho : UniformCoordinate po (fun a => a.val.val.1) P) :
    UniformCoordinate (colorMix S center output pc po α hα hα')
      (fun a => a.val.1) P := by
  intro x
  rw [colorMix_map_of_common S center output pc po α hα hα' (fun a => a.val.1)
    (fun x => (hc x).trans (ho x).symm)]
  exact hc x

theorem colorMix_uniform_complement (S : FlaggedTensor X Y Z) (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1) (P : X → Prop)
    (hc : UniformCoordinate pc (fun a => a.val.val.1) P)
    (ho : UniformCoordinate po (fun a => a.val.val.1) (fun x => ¬ P x))
    (hweight : α = (Fintype.card {x // P x} : ℝ) / Fintype.card X) :
    UniformCoordinate (colorMix S center output pc po α hα hα')
      (fun a => a.val.1) (fun _ => True) := by
  have hp : (Fintype.card {x // P x} : ℝ) ≠ 0 :=
    (Nat.cast_pos.mpr (uniform_coordinate_card_pos pc _ P hc)).ne'
  have hn : (Fintype.card {x // ¬ P x} : ℝ) ≠ 0 :=
    (Nat.cast_pos.mpr (uniform_coordinate_card_pos po _ _ ho)).ne'
  have hsumNat : Fintype.card {x // P x} + Fintype.card {x // ¬ P x} =
      Fintype.card X := by
    rw [Fintype.card_subtype_compl]
    exact Nat.add_sub_of_le (Fintype.card_subtype_le P)
  have hsum : (Fintype.card {x // P x} : ℝ) + Fintype.card {x // ¬ P x} =
      Fintype.card X := by exact_mod_cast hsumNat
  have hX : (Fintype.card X : ℝ) ≠ 0 := by
    have : 0 < Fintype.card X := lt_of_lt_of_le
      (uniform_coordinate_card_pos pc _ P hc) (Fintype.card_subtype_le P)
    exact (Nat.cast_pos.mpr this).ne'
  have hrest : 1 - α =
      (Fintype.card {x // ¬ P x} : ℝ) / Fintype.card X := by
    rw [hweight, one_sub_div hX, show (Fintype.card X : ℝ) -
      Fintype.card {x // P x} = Fintype.card {x // ¬ P x} by linarith]
  intro x
  rw [colorMix_map_comp_mass, hc x, ho x, hrest, hweight]
  simp only [ite_true, Fintype.card_subtype_true]
  by_cases hx : P x <;> simp only [hx, not_true_eq_false, not_false_eq_true,
    ite_true, ite_false, mul_zero, zero_add, add_zero]
  · rw [div_eq_mul_inv, mul_right_comm, mul_inv_cancel₀ hp, one_mul]
  · rw [div_eq_mul_inv, mul_right_comm, mul_inv_cancel₀ hn, one_mul]

theorem colorMix_uniform_complement_reverse
    (S : FlaggedTensor X Y Z) (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (rho : ℝ) (hα : 0 ≤ 1 - rho) (hα' : 1 - rho ≤ 1) (P : X → Prop)
    (hc : UniformCoordinate pc (fun a => a.val.val.1) (fun x => ¬ P x))
    (ho : UniformCoordinate po (fun a => a.val.val.1) P)
    (hweight : rho = (Fintype.card {x // P x} : ℝ) / Fintype.card X) :
    UniformCoordinate (colorMix S center output pc po (1 - rho) hα hα')
      (fun a => a.val.1) (fun _ => True) := by
  apply colorMix_uniform_complement S center output pc po (1 - rho) hα hα'
    (fun x => ¬ P x) hc
  · simpa only [not_not] using ho
  · have hsumNat : Fintype.card {x // P x} + Fintype.card {x // ¬ P x} =
        Fintype.card X := by
      rw [Fintype.card_subtype_compl]
      exact Nat.add_sub_of_le (Fintype.card_subtype_le P)
    have hsum : (Fintype.card {x // P x} : ℝ) + Fintype.card {x // ¬ P x} =
        Fintype.card X := by exact_mod_cast hsumNat
    have hX : (Fintype.card X : ℝ) ≠ 0 := by
      have : 0 < Fintype.card X := lt_of_lt_of_le
        (uniform_coordinate_card_pos po _ P ho) (Fintype.card_subtype_le P)
      exact (Nat.cast_pos.mpr this).ne'
    rw [hweight, one_sub_div hX, show (Fintype.card X : ℝ) -
      Fintype.card {x // P x} = Fintype.card {x // ¬ P x} by linarith]

theorem colorSlice_color_mass (S : FlaggedTensor X Y Z) (c : Color)
    (p : FiniteLaw (ColorSlice S c)) (b : Color) :
    ((p.map Subtype.val).map (leafColor S)).mass b = if c = b then 1 else 0 := by
  rw [map_comp_mass, FiniteLaw.map_mass]
  have hc : ∀ a : ColorSlice S c, leafColor S a.val = c := fun a => a.property
  simp_rw [hc]
  by_cases h : c = b <;> simp [h, p.total]

theorem colorSlice_pair_mass (S : FlaggedTensor X Y Z) (c : Color)
    (p : FiniteLaw (ColorSlice S c)) (f : Leaf S → U) (x : U) (b : Color) :
    ((p.map Subtype.val).map (fun a => (f a, leafColor S a))).mass (x, b) =
      if c = b then (p.map (fun a => f a.val)).mass x else 0 := by
  rw [map_comp_mass, FiniteLaw.map_mass]
  have hc : ∀ a : ColorSlice S c, leafColor S a.val = c := fun a => a.property
  simp_rw [hc]
  by_cases h : c = b <;> simp [h, FiniteLaw.map_mass]

theorem colorMix_independent_common (S : FlaggedTensor X Y Z) (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1) (f : Leaf S → U)
    (hcommon : ∀ x, (pc.map (fun a => f a.val)).mass x =
      (po.map (fun a => f a.val)).mass x) (x : U) (b : Color) :
    ((colorMix S center output pc po α hα hα').map
      (fun a => (f a, leafColor S a))).mass (x, b) =
      ((colorMix S center output pc po α hα hα').map f).mass x *
        ((colorMix S center output pc po α hα hα').map (leafColor S)).mass b := by
  rw [colorMix_map_of_common S center output pc po α hα hα' f hcommon x]
  rw [colorMix_map_mass, colorMix_map_mass,
    colorSlice_pair_mass, colorSlice_pair_mass,
    colorSlice_color_mass, colorSlice_color_mass, ← hcommon x]
  by_cases hc : center = b <;> by_cases ho : output = b <;> simp [hc, ho] <;> ring

theorem colorMix_independent_uniform (S : FlaggedTensor X Y Z) (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1) (P : X → Prop)
    (hc : UniformCoordinate pc (fun a => a.val.val.1) P)
    (ho : UniformCoordinate po (fun a => a.val.val.1) P) (x : X) (b : Color) :
    ((colorMix S center output pc po α hα hα').map
      (fun a => (a.val.1, leafColor S a))).mass (x, b) =
      ((colorMix S center output pc po α hα hα').map (fun a => a.val.1)).mass x *
        ((colorMix S center output pc po α hα hα').map (leafColor S)).mass b :=
  colorMix_independent_common S center output pc po α hα hα' (fun a => a.val.1)
    (fun x => (hc x).trans (ho x).symm) x b

theorem colorMix_independent_same (S : FlaggedTensor X Y Z) (c : Color)
    (pc po : FiniteLaw (ColorSlice S c))
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1) (f : Leaf S → U) (x : U) (b : Color) :
    ((colorMix S c c pc po α hα hα').map
      (fun a => (f a, leafColor S a))).mass (x, b) =
      ((colorMix S c c pc po α hα hα').map f).mass x *
        ((colorMix S c c pc po α hα hα').map (leafColor S)).mass b := by
  rw [colorMix_map_comp_mass S c c pc po α hα hα' f x]
  rw [colorMix_map_mass, colorMix_map_mass,
    colorSlice_pair_mass, colorSlice_pair_mass,
    colorSlice_color_mass, colorSlice_color_mass]
  by_cases hc : c = b <;> simp [hc]

end MatrixMultiplication.DualUniformMixtures

end

end OAI
