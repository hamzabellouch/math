import OAI.Combinatorics.BinaryEdit.FiniteSpectralTree
import OAI.Combinatorics.BinaryEdit.FiniteDisplacement
import OAI.Combinatorics.BinaryEdit.FiniteNumeric

namespace OAI

/-!
# Actual ℓ₁ maps and the finite-tree obstruction

The finite-group displacement identity yields the finite-tree root estimate
from geometric bounds on the concrete translations.
-/

noncomputable section

namespace TreeEdit.BinaryLower.FiniteActivity

open Classical
open scoped BigOperators

/-- Leaf periods, sparse-character detection and translation-cost bounds
imply the root averaged-distance estimate for arbitrary maps into ℓ₁. -/
theorem finite_tree_l1_mean_bound {A σ : Type*}
    [AddCommGroup A] [Fintype A] [Fintype σ] [Nonempty σ]
    (m b h : ℕ) (hm : m ≠ 0) (hb : 0 < b)
    (w : List (Fin m) → A)
    (Q : (Fin h → Fin m) → ℕ) [∀ f, NeZero (Q f)]
    (φ : ∀ f, ZMod (Q f) →+ A)
    (hgen : ∀ f : Fin h → Fin m, w (List.ofFn f) = φ f 1)
    (F : A → RealL1)
    (shift : InternalNode (Fin m) h → σ → A) (M C : ℝ)
    (hleaf : ∀ f (z : ZMod (Q f)) x,
      ‖F (x + φ f z) - F x‖ ≤ M / (m : ℝ) ^ h)
    (hdetect : ∀ v χ, characterSparse w b v χ →
      (Fintype.card σ : ℝ) ≤ ∑ s, ‖1 - χ (shift v s)‖ ^ 2)
    (hcost : ∀ v s x,
      ‖F (x + shift v s) - F x‖ ≤ C / (m : ℝ) ^ (v.1 : ℕ)) :
    (𝔼 x : A, ‖F (x + w []) - F x‖) ≤
      4 * ((h : ℝ) * C + M / (2 * (b : ℝ) ^ h)) := by
  classical
  obtain ⟨H, hH, hFourier⟩ := finite_group_displacement F
  rw [hFourier]
  apply finite_tree_spectral_bound m b h hm hb w Q φ hgen H hH shift M C
  · intro f z
    rw [← hFourier]
    exact Finset.expect_le Finset.univ_nonempty (fun x _ => hleaf f z x)
  · exact hdetect
  · intro v s
    rw [← hFourier]
    exact Finset.expect_le Finset.univ_nonempty (fun x _ => hcost v s x)

/-- Parameter normalization gives the root estimate with the absolute
constant 34. -/
theorem source_mean_bound34 {A : Type*} [AddCommGroup A] [Fintype A]
    (F : A → RealL1) (root : A) {k : ℕ} {M : ℝ}
    (hk : 1 ≤ k) (hM : 0 ≤ M)
    (hroot : (𝔼 x : A, ‖F (x + root) - F x‖) ≤
      4 * ((k : ℝ) * ((2 * (4 * (k : ℝ) ^ (10 * k)) /
        (k : ℝ) ^ (20 * k)) * M) + M / (2 * (k : ℝ) ^ k))) :
    (𝔼 x : A, ‖F (x + root) - F x‖) ≤ 34 * M / (k : ℝ) ^ k := by
  apply TreeEdit.BinaryLower.FiniteNumeric.finite_root_bound hk hM
  convert hroot using 1
  ring

end TreeEdit.BinaryLower.FiniteActivity

end

end OAI
