import OAI.Combinatorics.BinaryEdit.FiniteTreeGeometry
import OAI.Combinatorics.BinaryEdit.FiniteTreeCosts

namespace OAI

/-!
Concrete tagged cyclic-state versions of `lem:finite-cost`. The only input
about a translated vector is its actual coordinate support. In particular no
injectivity of the word map, period identity, or distortion hypothesis is used.
-/

namespace TreeEdit.BinaryLower.FiniteTree

theorem root_leaf_supported_script {m k : ℕ} (T : ℕ)
    (Q : Leaf m k → ℕ) (base ell : Leaf m k)
    (u : List (Fin m) → State Q) (z x : State Q)
    (hsupport : ∀ l : Leaf m k, l ≠ ell → z l = 0) :
    EditScript (nodeWord T (leafDecoder Q base) u k [] x)
      (nodeWord T (leafDecoder Q base) u k [] (x + z)) (T ^ k) := by
  have hout : ∀ r : List (Fin m), r.length = ell.val.length → r ≠ ell.val →
      ∀ y, leafDecoder Q base ([] ++ r) (y + z) = leafDecoder Q base ([] ++ r) y := by
    intro r hr hn y
    have hlen : r.length = k := hr.trans ell.property
    have hne : (⟨r, hlen⟩ : Leaf m k) ≠ ell := by
      intro he
      exact hn (congrArg Subtype.val he)
    apply (leafDecoder_eq_iff Q base r hlen (y + z) y).2
    simp only [Pi.add_apply, hsupport _ hne, add_zero]
  simpa only [ell.property] using
    nodeWord_leaf_script T (leafDecoder Q base) u ell.val [] z hout x

/-- The pointwise single-coordinate cost, for any value of the translation in
that cyclic coordinate and at every state. -/
theorem root_leaf_supported_cost {m k : ℕ} (T : ℕ)
    (Q : Leaf m k → ℕ) (base ell : Leaf m k)
    (u : List (Fin m) → State Q) (z x : State Q)
    (hsupport : ∀ l : Leaf m k, l ≠ ell → z l = 0) :
    ed (nodeWord T (leafDecoder Q base) u k [] x)
      (nodeWord T (leafDecoder Q base) u k [] (x + z)) ≤ T ^ k :=
  CheapTranslations.editDistance_le_script
    (root_leaf_supported_script T Q base ell u z x hsupport)

theorem root_leaf_supported_normalized_cost {m k : ℕ} (T : ℕ) (hm : 0 < m)
    (Q : Leaf m k → ℕ) (base ell : Leaf m k)
    (u : List (Fin m) → State Q) (z x : State Q)
    (hsupport : ∀ l : Leaf m k, l ≠ ell → z l = 0) :
    (ed (nodeWord T (leafDecoder Q base) u k [] x)
      (nodeWord T (leafDecoder Q base) u k [] (x + z)) : ℝ) ≤
      ((m * T : ℕ) : ℝ) ^ k / (m : ℝ) ^ k := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hb := root_leaf_supported_cost T Q base ell u z x hsupport
  have hn : (ed (nodeWord T (leafDecoder Q base) u k [] x)
      (nodeWord T (leafDecoder Q base) u k [] (x + z)) : ℝ) ≤ (T : ℝ) ^ k := by
    exact_mod_cast hb
  simpa only [Nat.cast_mul, mul_pow, mul_div_cancel_left₀ _ (pow_ne_zero _ hm0)]
    using hn

theorem root_internal_supported_script {m k : ℕ} (T : ℕ)
    (Q : Leaf m k → ℕ) (base : Leaf m k)
    (u : List (Fin m) → State Q) (h : ℕ) (q : List (Fin m))
    (hlen : h + 1 + q.length = k) (s : ℕ) (hs : s ≤ T)
    (hsupport : ∀ l : Leaf m k, ¬ q.IsPrefix l.val → u q l = 0)
    (x : State Q) :
    EditScript (nodeWord T (leafDecoder Q base) u k [] x)
      (nodeWord T (leafDecoder Q base) u k [] (x + s • u q))
      (T ^ q.length * (2 * s * m * (m * T) ^ h)) := by
  have hout : ∀ r : List (Fin m), r.length = h + 1 + q.length →
      ¬ q.IsPrefix r → ∀ y,
        leafDecoder Q base ([] ++ r) (y + s • u ([] ++ q)) =
          leafDecoder Q base ([] ++ r) y := by
    intro r hr hn y
    have hrk : r.length = k := hr.trans hlen
    apply (leafDecoder_eq_iff Q base r hrk (y + s • u ([] ++ q)) y).2
    simp only [List.nil_append, Pi.add_apply, Pi.smul_apply,
      hsupport ⟨r, hrk⟩ hn, smul_zero, add_zero]
  simpa only [hlen, List.nil_append] using
    nodeWord_descendant_cheap_script T (leafDecoder Q base) u h q [] s hs hout x

theorem root_internal_supported_cost {m k : ℕ} (T : ℕ)
    (Q : Leaf m k → ℕ) (base : Leaf m k)
    (u : List (Fin m) → State Q) (h : ℕ) (q : List (Fin m))
    (hlen : h + 1 + q.length = k) (s : ℕ) (hs : s ≤ T)
    (hsupport : ∀ l : Leaf m k, ¬ q.IsPrefix l.val → u q l = 0)
    (x : State Q) :
    ed (nodeWord T (leafDecoder Q base) u k [] x)
      (nodeWord T (leafDecoder Q base) u k [] (x + s • u q)) ≤
      T ^ q.length * (2 * s * m * (m * T) ^ h) :=
  CheapTranslations.editDistance_le_script
    (root_internal_supported_script T Q base u h q hlen s hs hsupport x)

/-- Exactly the root-word normalized row-translation estimate, for the tagged
cyclic-state decoder and a subtree-supported cheap vector. -/
theorem root_internal_supported_normalized_cost {m k : ℕ} (T : ℕ)
    (hm : 0 < m) (hT : 0 < T)
    (Q : Leaf m k → ℕ) (base : Leaf m k)
    (u : List (Fin m) → State Q) (h : ℕ) (q : List (Fin m))
    (hlen : h + 1 + q.length = k) (s : ℕ) (hs : s ≤ T)
    (hsupport : ∀ l : Leaf m k, ¬ q.IsPrefix l.val → u q l = 0)
    (x : State Q) :
    (ed (nodeWord T (leafDecoder Q base) u k [] x)
      (nodeWord T (leafDecoder Q base) u k [] (x + s • u q)) : ℝ) ≤
      (2 * (s : ℝ) / T) * (((m * T : ℕ) : ℝ) ^ k / (m : ℝ) ^ q.length) := by
  have hout : ∀ r : List (Fin m), r.length = h + 1 + q.length →
      ¬ q.IsPrefix r → ∀ y,
        leafDecoder Q base ([] ++ r) (y + s • u ([] ++ q)) =
          leafDecoder Q base ([] ++ r) y := by
    intro r hr hn y
    have hrk : r.length = k := hr.trans hlen
    apply (leafDecoder_eq_iff Q base r hrk (y + s • u ([] ++ q)) y).2
    simp only [List.nil_append, Pi.add_apply, Pi.smul_apply,
      hsupport ⟨r, hrk⟩ hn, smul_zero, add_zero]
  simpa only [hlen, List.nil_append] using
    nodeWord_descendant_normalized_bound T hm hT (leafDecoder Q base) u h q [] s hs hout x

end TreeEdit.BinaryLower.FiniteTree

end OAI
