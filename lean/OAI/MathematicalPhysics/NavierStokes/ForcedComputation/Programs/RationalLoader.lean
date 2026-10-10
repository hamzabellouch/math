import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.RectangleAffine
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.IntermediateObservation

namespace OAI

/-! One rational translation supplies the entire input-dependent loading period. -/

noncomputable section
open Set

namespace ForcedComputation

open ShearFlows

def centeredBox (p : Fin 2 → ℚ) (r : ℚ) : RationalBox 2 :=
  ⟨fun j => p j - r, fun j => p j + r⟩

theorem centeredBox_center (p : Fin 2 → ℚ) (r : ℚ) (j : Fin 2) :
    (centeredBox p r).center j = (p j : ℝ) := by
  simp only [centeredBox, RationalBox.center, Rat.cast_sub, Rat.cast_add]
  ring

theorem centeredBox_halfWidth (p : Fin 2 → ℚ) (r : ℚ) (j : Fin 2) :
    (centeredBox p r).halfWidth j = (r : ℝ) := by
  simp only [centeredBox, RationalBox.halfWidth, Rat.cast_sub, Rat.cast_add]
  ring

def loaderInstruction (p q : Fin 2 → ℚ) : Instruction :=
  ⟨centeredBox p (1 / 512), centeredBox q (1 / 512), 1⟩

def loaderInput (p q : Fin 2 → ℚ) (z : ℚ) : Input where
  period := 1
  chart := ⟨fun _ => 1 / 32, fun _ => 31 / 32⟩
  h := 1 / 512
  codingHeight := z
  centers := ⟨fun _ => 1 / 8, fun _ => 7 / 8⟩
  instructions := [loaderInstruction p q]

theorem loaderInstruction_image (p q : Fin 2 → ℚ) :
    (loaderInstruction p q).affine '' (loaderInstruction p q).source.carrier =
      (loaderInstruction p q).target.carrier := by
  apply Instruction.image_eq_of_halfWidths _ (by norm_num [loaderInstruction])
  · simp only [loaderInstruction, centeredBox_halfWidth, Rat.cast_one, one_mul]
  · simp only [loaderInstruction, centeredBox_halfWidth, Rat.cast_one, div_one]

theorem loaderInput_valid (p q : Fin 2 → ℚ) (z : ℚ)
    (hp : ∀ j, 1 / 8 ≤ p j ∧ p j ≤ 7 / 8)
    (hq : ∀ j, 1 / 8 ≤ q j ∧ q j ≤ 7 / 8)
    (hz : 1 / 32 < z ∧ z < 31 / 32) : ValidInput (loaderInput p q z) := by
  have hpos (a : Fin 2 → ℚ) : (centeredBox a (1 / 512)).positive := by
    intro j
    change a j - 1 / 512 < a j + 1 / 512
    linarith
  have hin (a : Fin 2 → ℚ) (ha : ∀ j, 1 / 8 ≤ a j ∧ a j ≤ 7 / 8) :
      (centeredBox a (1 / 512)).carrier ⊆ (loaderInput p q z).inPlanarChart := by
    intro x hx j
    have hj := hx j
    have haj : (1 / 8 : ℝ) ≤ (a j : ℝ) ∧ (a j : ℝ) ≤ 7 / 8 := by
      have h : (((1 / 8 : ℚ) : ℝ) ≤ (a j : ℝ) ∧ (a j : ℝ) ≤ ((7 / 8 : ℚ) : ℝ)) :=
        ⟨Rat.cast_le.mpr (ha j).1, Rat.cast_le.mpr (ha j).2⟩
      norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
      exact h
    change ((a j - 1 / 512 : ℚ) : ℝ) ≤ x j ∧ x j ≤ ((a j + 1 / 512 : ℚ) : ℝ) at hj
    simp only [Rat.cast_sub, Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hj
    change ((1 / 32 : ℚ) : ℝ) < x j ∧ x j < ((31 / 32 : ℚ) : ℝ)
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    constructor <;> linarith [haj.1, haj.2]
  have hcenter (a : Fin 2 → ℚ) (ha : ∀ j, 1 / 8 ≤ a j ∧ a j ≤ 7 / 8) :
      (centeredBox a (1 / 512)).center ∈ (loaderInput p q z).centers.carrier := by
    intro j
    rw [centeredBox_center]
    exact_mod_cast ha j
  refine {
    period_pos := by norm_num [loaderInput]
    chart_positive := by intro j; norm_num [loaderInput, RationalBox.positive]
    chart_length := by intro j; norm_num [loaderInput]
    h_pos := by norm_num [loaderInput]
    centers_nonempty := by intro j; norm_num [loaderInput]
    chartMargin := by intro j; norm_num [loaderInput]
    height_inside := by exact_mod_cast hz
    source_positive := ?_
    target_positive := ?_
    source_in_chart := ?_
    target_in_chart := ?_
    factor_pos := ?_
    image_eq := ?_
    source_separation := ?_
    target_separation := ?_
    halfWidths := ?_
    source_centers := ?_
    target_centers := ?_ }
  · intro b hb
    have he : b = loaderInstruction p q := by simpa only [loaderInput, List.mem_singleton] using hb
    subst b
    exact hpos p
  · intro b hb
    have he : b = loaderInstruction p q := by simpa only [loaderInput, List.mem_singleton] using hb
    subst b
    exact hpos q
  · intro b hb
    have he : b = loaderInstruction p q := by simpa only [loaderInput, List.mem_singleton] using hb
    subst b
    exact hin p hp
  · intro b hb
    have he : b = loaderInstruction p q := by simpa only [loaderInput, List.mem_singleton] using hb
    subst b
    exact hin q hq
  · intro b hb
    have he : b = loaderInstruction p q := by simpa only [loaderInput, List.mem_singleton] using hb
    subst b
    norm_num [loaderInstruction]
  · intro b hb
    have he : b = loaderInstruction p q := by simpa only [loaderInput, List.mem_singleton] using hb
    subst b
    exact loaderInstruction_image p q
  · intro i j hij
    apply False.elim ∘ hij
    apply Fin.ext
    have hi : i.val < 1 := by simpa only [loaderInput, List.length_singleton] using i.isLt
    have hj : j.val < 1 := by simpa only [loaderInput, List.length_singleton] using j.isLt
    omega
  · intro i j hij
    apply False.elim ∘ hij
    apply Fin.ext
    have hi : i.val < 1 := by simpa only [loaderInput, List.length_singleton] using i.isLt
    have hj : j.val < 1 := by simpa only [loaderInput, List.length_singleton] using j.isLt
    omega
  · intro b hb j
    have he : b = loaderInstruction p q := by simpa only [loaderInput, List.mem_singleton] using hb
    subst b
    simp only [loaderInstruction, centeredBox_halfWidth, loaderInput, le_refl, and_self]
  · intro b hb
    have he : b = loaderInstruction p q := by simpa only [loaderInput, List.mem_singleton] using hb
    subst b
    exact hcenter p hp
  · intro b hb
    have he : b = loaderInstruction p q := by simpa only [loaderInput, List.mem_singleton] using hb
    subst b
    exact hcenter q hq

theorem loaderInstruction_center (p q : Fin 2 → ℚ) :
    (loaderInstruction p q).affine (fun j => (p j : ℝ)) = fun j => (q j : ℝ) := by
  funext j
  fin_cases j <;> simp [loaderInstruction, Instruction.affine, centeredBox_center]

theorem loaderInstruction_contains_center (p q : Fin 2 → ℚ) :
    (fun j => (p j : ℝ)) ∈ (loaderInstruction p q).source.carrier := by
  intro j
  change ((p j - 1 / 512 : ℚ) : ℝ) ≤ (p j : ℝ) ∧
    (p j : ℝ) ≤ ((p j + 1 / 512 : ℚ) : ℝ)
  simp only [Rat.cast_sub, Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  constructor <;> linarith

theorem loaderFlow_endpoint {p q : Fin 2 → ℚ} {z : ℚ}
    (hd : ValidInput (loaderInput p q z)) {Φ : ℝ → Space → Space}
    (hΦ : IsMaterialFlow 1 (loaderInput p q z).realizingVelocity Φ) :
    Φ 1 (atHeight (fun j => (p j : ℝ)) z) = atHeight (fun j => (q j : ℝ)) z := by
  have hΦ' : IsMaterialFlow (loaderInput p q z).period (loaderInput p q z).realizingVelocity Φ := by
    simpa only [loaderInput, Rat.cast_one] using hΦ
  have hδ : (0 : ℝ) < (loaderInput p q z).tubeRadius := by
    exact_mod_cast tubeRadius_pos hd
  have hx : atHeight (fun j => (p j : ℝ)) z ∈
      sourceTube (loaderInstruction p q) z (loaderInput p q z).tubeRadius := by
    refine ⟨_, loaderInstruction_contains_center p q, ?_, ?_⟩
    · simpa only [atHeight_horizontal, sub_self, norm_zero] using hδ
    · simpa [atHeight] using hδ
  have he := realizingVelocity_periodMap hd hΦ' (b := loaderInstruction p q)
    (by simp [loaderInput]) hx
  rw [atHeight_horizontal, loaderInstruction_center] at he
  exact he

theorem loaderFlow_first_le {p q : Fin 2 → ℚ} {z : ℚ}
    (hd : ValidInput (loaderInput p q z)) {Φ : ℝ → Space → Space}
    (hΦ : IsMaterialFlow 1 (loaderInput p q z).realizingVelocity Φ)
    {a t : ℝ} (hp : (p 0 : ℝ) ≤ a) (hq : (q 0 : ℝ) ≤ a) (ht : t ∈ Icc (0 : ℝ) 1) :
    Φ t (atHeight (fun j => (p j : ℝ)) z) 0 ≤ a + 1 / 256 := by
  have hΦ' : IsMaterialFlow (loaderInput p q z).period (loaderInput p q z).realizingVelocity Φ := by
    simpa only [loaderInput, Rat.cast_one] using hΦ
  have he := materialFlow_first_le hd hΦ' ⟨0, by simp [loaderInput]⟩
    (loaderInstruction_contains_center p q)
    (by simpa [loaderInput, loaderInstruction, centeredBox_center] using hp)
    (by simpa [loaderInput, loaderInstruction, centeredBox_center] using hq) ht
  norm_num [loaderInput] at he ⊢
  exact he

theorem loaderFlow_first_ge {p q : Fin 2 → ℚ} {z : ℚ}
    (hd : ValidInput (loaderInput p q z)) {Φ : ℝ → Space → Space}
    (hΦ : IsMaterialFlow 1 (loaderInput p q z).realizingVelocity Φ)
    {a t : ℝ} (hp : a ≤ (p 0 : ℝ)) (hq : a ≤ (q 0 : ℝ)) (ht : t ∈ Icc (0 : ℝ) 1) :
    a - 1 / 256 ≤ Φ t (atHeight (fun j => (p j : ℝ)) z) 0 := by
  have hΦ' : IsMaterialFlow (loaderInput p q z).period (loaderInput p q z).realizingVelocity Φ := by
    simpa only [loaderInput, Rat.cast_one] using hΦ
  have he := materialFlow_first_ge hd hΦ' ⟨0, by simp [loaderInput]⟩
    (loaderInstruction_contains_center p q)
    (by simpa [loaderInput, loaderInstruction, centeredBox_center] using hp)
    (by simpa [loaderInput, loaderInstruction, centeredBox_center] using hq) ht
  norm_num [loaderInput] at he ⊢
  exact he

end ForcedComputation

end

end OAI
