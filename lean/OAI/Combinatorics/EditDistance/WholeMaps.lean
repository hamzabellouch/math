import OAI.Combinatorics.EditDistance.UpperBound
import OAI.Combinatorics.EditDistance.AlphabetLower

namespace OAI

/-!
# Simultaneous whole-domain maps and fixed-length binary upper bounds
-/

namespace EditUpper
open EditDistortion EditCutModel Filter
universe u

lemma coarse_whole_map (A : Type u) [Fintype A] (d : ℕ) :
    ∃ f : Words A d → L1, ∀ x y,
      (edit x.val y.val : ℝ) ≤ ‖f x-f y‖ ∧
      ‖f x-f y‖ ≤ (2*(d : ℝ))*(edit x.val y.val : ℝ) := by
  classical
  let : Finite (Words A d) := finite_words A d
  let : Fintype (Words A d) := Fintype.ofFinite _
  let f := fun x : Words A d => (d : ℝ) • coordinateEmbedding (Words A d) x
  have hn (x y : Words A d) : ‖f x-f y‖ = (d : ℝ)*
      ‖coordinateEmbedding (Words A d) x-coordinateEmbedding (Words A d) y‖ := by
    dsimp [f]
    rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg d)]
  refine ⟨f,?_⟩
  intro x y
  by_cases hxy : x = y
  · subst y
    simp only [sub_self,norm_zero,edit_real_diag,mul_zero,le_refl,and_self]
  · have hlo := coordinate_separation x y hxy
    have hu := norm_sub_le (coordinateEmbedding (Words A d) x) (coordinateEmbedding (Words A d) y)
    rw [coordinate_norm,coordinate_norm] at hu
    have he : (edit x.val y.val : ℝ) ≤ d := by
      exact_mod_cast (edit_le_max_length x.val y.val).trans (max_le x.property y.property)
    have hep : (1 : ℝ) ≤ edit x.val y.val := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (mt (cost_eq_zero_iff (s := true)).mp (fun hh => hxy (Subtype.ext hh)))
    rw [hn]
    have hd := Nat.cast_nonneg (α := ℝ) d
    constructor <;> nlinarith

theorem eventual_whole_maps : ∀ᶠ d : ℕ in atTop,
    ∀ (A : Type u) [Fintype A], ∃ f : Words A d → L1, ∀ x y,
      (edit x.val y.val : ℝ) ≤ ‖f x-f y‖ ∧
      ‖f x-f y‖ ≤ exponentScale 32 d*(edit x.val y.val : ℝ) := by
  filter_upwards [EditUpperParameters.eventual_choice] with d hc
  rcases hc with ⟨hN,hb,hcap,hbound⟩
  intro A inst
  let N := EditUpperParameters.level (Real.log (d : ℝ))
  let b := EditUpperParameters.branching (Real.log (d : ℝ))
  obtain ⟨M,hlo,hup⟩ := exists_level b N (by omega) N le_rfl A
  let D := ((b : ℝ)+2)*(growth b N)^N
  have hD : 0 ≤ D := by
    have hh := growth_ge (N := N) (show 1 ≤ b by omega)
    dsimp [D]
    positivity
  have hnum : 2*D ≤ exponentScale 32 d := by
    simpa [D,growth,exponentScale,b,N,mul_assoc] using hbound
  refine ⟨fun x => M.vector x.val,?_⟩
  intro x y
  rw [M.vector_distance]
  constructor
  · exact (show (edit x.val y.val : ℝ) ≤ indel x.val y.val by
      exact_mod_cast edit_le_indel x.val y.val).trans
        (hlo _ _ (x.property.trans hcap) (y.property.trans hcap))
  · have hi : (indel x.val y.val : ℝ) ≤ 2*(edit x.val y.val : ℝ) := by
      exact_mod_cast indel_le_two_edit x.val y.val
    calc
      _ ≤ D*(indel x.val y.val : ℝ) := hup _ _
      _ ≤ D*(2*(edit x.val y.val : ℝ)) := mul_le_mul_of_nonneg_left hi hD
      _ = (2*D)*(edit x.val y.val : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hnum (Nat.cast_nonneg _)

theorem whole_maps_all_lengths : ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 3 ≤ d →
    ∀ (A : Type u) [Fintype A], ∃ f : Words A d → L1, ∀ x y,
      (edit x.val y.val : ℝ) ≤ ‖f x-f y‖ ∧
      ‖f x-f y‖ ≤ exponentScale C d*(edit x.val y.val : ℝ) := by
  obtain ⟨D,hD⟩ := eventually_atTop.mp eventual_whole_maps.{u}
  let S := Real.sqrt (Real.log 3*Real.log (Real.log 3))
  have hl3 : 1 < Real.log 3 := by linarith [Real.log_three_gt_d9]
  have hll3 : 0 < Real.log (Real.log 3) := Real.log_pos hl3
  have hS : 0 < S := Real.sqrt_pos.mpr (mul_pos (by linarith) hll3)
  let C := 32+2*(D : ℝ)/S
  have hDC : 0 ≤ 2*(D : ℝ)/S := by positivity
  have hC : 0 < C := by dsimp [C]; linarith
  have h32 : 32 ≤ C := by dsimp [C]; linarith
  refine ⟨C,hC,?_⟩
  intro d hd A inst
  have hm : 0 ≤ Real.sqrt (Real.log (d : ℝ)*Real.log (Real.log (d : ℝ))) := Real.sqrt_nonneg _
  by_cases hDd : D ≤ d
  · obtain ⟨f,hf⟩ := hD d hDd A
    refine ⟨f,fun x y => ⟨(hf x y).1,?_⟩⟩
    apply (hf x y).2.trans
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right h32 hm
  · obtain ⟨f,hf⟩ := coarse_whole_map A d
    have hl : Real.log 3 ≤ Real.log (d : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hd)
    have hll : Real.log (Real.log 3) ≤ Real.log (Real.log (d : ℝ)) :=
      Real.log_le_log (by linarith) hl
    have hST : S ≤ Real.sqrt (Real.log (d : ℝ)*Real.log (Real.log (d : ℝ))) := by
      apply Real.sqrt_le_sqrt
      exact mul_le_mul hl hll hll3.le (by linarith)
    have hCS : 2*(D : ℝ) ≤ C*S := by
      have he : (2*(D : ℝ)/S)*S = 2*(D : ℝ) := div_mul_cancel₀ _ hS.ne'
      dsimp [C]
      nlinarith
    have h2 : 2*(d : ℝ) ≤ exponentScale C d := by
      have hdD : (d : ℝ) ≤ D := by exact_mod_cast (show d ≤ D by omega)
      have hmC := mul_le_mul_of_nonneg_left hST hC.le
      have hexp := Real.add_one_le_exp (C*Real.sqrt (Real.log (d : ℝ)*Real.log (Real.log (d : ℝ))))
      unfold exponentScale
      linarith
    exact ⟨f,fun x y => ⟨(hf x y).1,(hf x y).2.trans
      (mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg _))⟩⟩

theorem fixed_length_binary_upper : ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ m : ℕ, 3 ≤ m →
    ∃ g : (Fin m → Bool) → L1, ∀ x y : Fin m → Bool,
      (edit (List.ofFn x) (List.ofFn y) : ℝ) ≤ ‖g x-g y‖ ∧
      ‖g x-g y‖ ≤ exponentScale C₀ m*(edit (List.ofFn x) (List.ofFn y) : ℝ) := by
  obtain ⟨C,hC,h⟩ := whole_maps_all_lengths.{0}
  refine ⟨C,hC,?_⟩
  intro m hm
  obtain ⟨f,hf⟩ := h m hm Bool
  let word : (Fin m → Bool) → Words Bool m := fun x => ⟨List.ofFn x,by simp⟩
  exact ⟨fun x => f (word x),fun x y => hf (word x) (word y)⟩

end EditUpper

end OAI
