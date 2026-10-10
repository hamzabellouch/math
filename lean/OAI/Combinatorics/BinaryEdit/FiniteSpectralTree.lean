import OAI.Combinatorics.BinaryEdit.SparseActivity
import OAI.Combinatorics.BinaryEdit.FiniteActivityBridge

namespace OAI

/-!
# Finite-tree spectral obstruction

The sparse/dense counting and Fourier-mass estimates give the spectral
bound used in `prop:finite-lower` for the cyclic leaf coordinates and
cheap translations.
-/

noncomputable section

namespace TreeEdit.BinaryLower.FiniteActivity

open Classical
open scoped BigOperators

/-- The complete sparse/dense spectral estimate on a finite tree. For the
manuscript instantiate `h=b=k`, `m=20*k`, and `C=(2*J/T)*M`. The conclusion
then reproduces `eq:finite-root-upper` before the final numerical estimate. -/
theorem finite_tree_spectral_bound {A σ : Type*}
    [AddCommGroup A] [Fintype A] [Fintype σ] [Nonempty σ]
    (m b h : ℕ) (hm : m ≠ 0) (hb : 0 < b)
    (w : List (Fin m) → A)
    (Q : (Fin h → Fin m) → ℕ) [∀ f, NeZero (Q f)]
    (φ : ∀ f, ZMod (Q f) →+ A)
    (hgen : ∀ f : Fin h → Fin m, w (List.ofFn f) = φ f 1)
    (H : AddChar A ℂ → ℝ) (hH : ∀ χ, 0 ≤ H χ)
    (shift : InternalNode (Fin m) h → σ → A) (M C : ℝ)
    (hleaf : ∀ f (z : ZMod (Q f)),
      (∑ χ, ‖1 - χ (φ f z)‖ ^ 2 * H χ) ≤ M / (m : ℝ) ^ h)
    (hdetect : ∀ v χ, characterSparse w b v χ →
      (Fintype.card σ : ℝ) ≤ ∑ s, ‖1 - χ (shift v s)‖ ^ 2)
    (hcost : ∀ v s,
      (∑ χ, ‖1 - χ (shift v s)‖ ^ 2 * H χ) ≤ C / (m : ℝ) ^ (v.1 : ℕ)) :
    (∑ χ : AddChar A ℂ, ‖1 - χ (w [])‖ ^ 2 * H χ) ≤
      4 * ((h : ℝ) * C + M / (2 * (b : ℝ) ^ h)) := by
  classical
  apply TreeEdit.BinaryLower.TreeDistortion.FiniteMass.finite_spectral_root_bound Q φ H (w [])
    (characterSparse w b) shift
    (fun v => C / (m : ℝ) ^ (v.1 : ℕ))
    (fun _f => M / (m : ℝ) ^ h) M ((h : ℝ) * C) ((b : ℝ) ^ h)
  · exact pow_pos (Nat.cast_pos.mpr hb) _
  · exact hH
  · intro χ hr hn
    exact character_dense_of_leaf_generators w b h (fun f => φ f 1) χ hgen hr hn
  · exact hleaf
  · exact le_of_eq (leaf_budget m h hm M)
  · exact hdetect
  · exact hcost
  · exact le_of_eq (internal_node_budget m h hm C)

end TreeEdit.BinaryLower.FiniteActivity

end

end OAI
