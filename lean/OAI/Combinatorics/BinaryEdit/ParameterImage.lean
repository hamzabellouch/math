import OAI.Combinatorics.BinaryEdit.Distortion
import OAI.Combinatorics.BinaryEdit.EditMetric

namespace OAI

/-! Lower distortion bounds on the finite image of a parameter space. -/

noncomputable section
namespace TreeEdit.BinaryLower.ParameterImage

variable {A X : Type*} [Fintype A]

/-- The actual finite image of a finite parameter space. -/
def image (G : A → X) : Finset X := by
  classical
  exact Finset.univ.image G

lemma mem_image (G : A → X) (x : X) : x ∈ image G ↔ ∃ a, G a = x := by
  classical
  simp [image]

/-- The canonical map onto the finite image, allowing state-to-word collisions. -/
def toImage (G : A → X) (a : A) : {x : X // x ∈ image G} :=
  ⟨G a, (mem_image G (G a)).2 ⟨a, rfl⟩⟩

lemma image_card_two (G : A → X) (hG : ∃ a b, G a ≠ G b) : 2 ≤ (image G).card := by
  classical
  obtain ⟨a, b, hab⟩ := hG
  apply Finset.one_lt_card.mpr
  exact ⟨G a, (mem_image G _).2 ⟨a, rfl⟩,
    G b, (mem_image G _).2 ⟨b, rfl⟩, hab⟩

/-- An obstruction for every normalized map on parameter states gives the
claimed distortion lower bound on the finite image, even when `G` is not
injective. All metric hypotheses are the ordinary ones needed to normalize. -/
theorem image_lower_of_nonexpanding_obstruction
    (G : A → X) (hG : ∃ a b, G a ≠ G b)
    (ρ : X → X → ℝ) (hρ : ∀ x y, 0 ≤ ρ x y)
    (hdiag : ∀ x, ρ x x = 0) (hpos : ∀ x y, x ≠ y → 0 < ρ x y)
    (D : ℝ)
    (hobstruction : ∀ (F : A → RealL1) (C : ℝ), 0 < C →
      (∀ a b, ρ (G a) (G b) / C ≤ ‖F a - F b‖ ∧
        ‖F a - F b‖ ≤ ρ (G a) (G b)) → D ≤ C) :
    2 ≤ (image G).card ∧
      D ≤ c1 {x : X // x ∈ image G} (fun x y => ρ x.val y.val) := by
  classical
  refine ⟨image_card_two G hG, ?_⟩
  obtain ⟨a, b, hab⟩ := hG
  let : Nontrivial {x : X // x ∈ image G} :=
    nontrivial_of_ne (toImage G a) (toImage G b)
      (fun h => hab (congrArg Subtype.val h))
  apply le_c1_of_nonexpanding (fun x y : {x : X // x ∈ image G} => ρ x.val y.val)
    (fun x y => hρ _ _) (fun x => hdiag _)
    (fun x y hxy => hpos _ _ (fun h => hxy (Subtype.ext h))) D
  intro f C hC hf
  exact hobstruction (fun a => f (toImage G a)) C hC
    (fun a b => hf (toImage G a) (toImage G b))

/-- The finite-image obstruction for ordinary edit distance on fixed-length words. -/
theorem exists_word_image_lower {Γ : Type*} {n : ℕ}
    (G : A → Word Γ n)
    (hsep : ∃ a b, 0 < ed (G a).val (G b).val)
    (D : ℝ)
    (hobstruction : ∀ (F : A → RealL1) (C : ℝ), 0 < C →
      (∀ a b, (ed (G a).val (G b).val : ℝ) / C ≤ ‖F a - F b‖ ∧
        ‖F a - F b‖ ≤ (ed (G a).val (G b).val : ℝ)) → D ≤ C) :
    ∃ W : Finset (Word Γ n),
      (∀ w, w ∈ W ↔ ∃ a, G a = w) ∧ 2 ≤ W.card ∧
      D ≤ c1 {w : Word Γ n // w ∈ W}
        (fun x y => (ed x.val.val y.val.val : ℝ)) := by
  have hG : ∃ a b, G a ≠ G b := by
    obtain ⟨a, b, hab⟩ := hsep
    refine ⟨a, b, ?_⟩
    intro h
    rw [h, ed_self] at hab
    omega
  have h := image_lower_of_nonexpanding_obstruction G hG
    (fun x y : Word Γ n => (ed x.val y.val : ℝ))
    (fun _ _ => Nat.cast_nonneg _) (fun _ => by simp)
    (fun x y hxy => by
      exact_mod_cast (editDistance_pos_iff.mpr (fun h => hxy (Subtype.ext h))))
    D hobstruction
  exact ⟨image G, mem_image G, h.1, h.2⟩

/-- The binary image has exactly the `binarySetDistortion` of the binary word metric. -/
theorem exists_binary_image_lower {n : ℕ}
    (G : A → Word Bool n)
    (hsep : ∃ a b, 0 < ed (G a).val (G b).val)
    (D : ℝ)
    (hobstruction : ∀ (F : A → RealL1) (C : ℝ), 0 < C →
      (∀ a b, (ed (G a).val (G b).val : ℝ) / C ≤ ‖F a - F b‖ ∧
        ‖F a - F b‖ ≤ (ed (G a).val (G b).val : ℝ)) → D ≤ C) :
    ∃ W : Finset (Word Bool n),
      (∀ w, w ∈ W ↔ ∃ a, G a = w) ∧ 2 ≤ W.card ∧ D ≤ binarySetDistortion W := by
  simpa only [binarySetDistortion] using exists_word_image_lower G hsep D hobstruction

/-- Final finite-tree passage: the distinguished root displacement is far
in every state, but every nonexpanding ℓ₁ map has a small average root
 displacement. The resulting lower bound concerns the actual word image. -/
theorem exists_word_image_lower_of_root_bound {Γ : Type*} {n : ℕ}
    [AddCommGroup A] (G : A → Word Γ n) (z : A)
    (lower upper : ℝ) (hlower : 0 < lower) (hupper : 0 < upper)
    (hsep : ∀ x, lower ≤ (ed (G x).val (G (x + z)).val : ℝ))
    (hroot : ∀ F : A → RealL1,
      (∀ x y, ‖F x - F y‖ ≤ (ed (G x).val (G y).val : ℝ)) →
      (∑ x : A, ‖F (x + z) - F x‖) / Fintype.card A ≤ upper) :
    ∃ W : Finset (Word Γ n),
      (∀ w, w ∈ W ↔ ∃ a, G a = w) ∧ 2 ≤ W.card ∧
      lower / upper ≤ c1 {w : Word Γ n // w ∈ W}
        (fun x y => (ed x.val.val y.val.val : ℝ)) := by
  apply exists_word_image_lower G
  · refine ⟨0, z, ?_⟩
    have h := hlower.trans_le (hsep 0)
    simp only [zero_add] at h
    exact_mod_cast h
  · intro F C hC hF
    have hcard : (0 : ℝ) < Fintype.card A := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card A)
    have hl : ∀ x, lower / C ≤ ‖F (x + z) - F x‖ := by
      intro x
      calc
        lower / C ≤ (ed (G x).val (G (x + z)).val : ℝ) / C :=
          div_le_div_of_nonneg_right (hsep x) hC.le
        _ ≤ ‖F x - F (x + z)‖ := (hF x (x + z)).1
        _ = ‖F (x + z) - F x‖ := norm_sub_rev _ _
    have havg : lower / C ≤
        (∑ x : A, ‖F (x + z) - F x‖) / Fintype.card A := by
      apply (le_div_iff₀ hcard).2
      calc
        lower / C * (Fintype.card A : ℝ) = ∑ _x : A, lower / C := by
          simp [mul_comm]
        _ ≤ ∑ x : A, ‖F (x + z) - F x‖ := Finset.sum_le_sum (fun x _ => hl x)
    have hb : lower / C ≤ upper := havg.trans (hroot F (fun x y => (hF x y).2))
    apply (div_le_iff₀ hupper).2
    simpa only [mul_comm] using (div_le_iff₀ hC).1 hb

end TreeEdit.BinaryLower.ParameterImage

end

end OAI
