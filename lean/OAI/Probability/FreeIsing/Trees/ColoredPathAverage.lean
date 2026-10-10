import OAI.Probability.FreeIsing.Trees.ColoredEdgeLifts

namespace OAI

noncomputable section
open scoped BigOperators InnerProductSpace

namespace Problem367.ColoredPathAverage

def Path (d : ℕ) : ℕ → Fin d → Type
  | 0, _ => PUnit
  | n + 1, i => Σ j : {j : Fin d // j ≠ i}, Path d n j.1

instance pathFintype (d : ℕ) : (n : ℕ) → (i : Fin d) → Fintype (Path d n i)
  | 0, _ => inferInstanceAs (Fintype PUnit)
  | n + 1, i => by
      letI : ∀ j : {j : Fin d // j ≠ i}, Fintype (Path d n j.1) :=
        fun j => pathFintype d n j.1
      exact inferInstanceAs (Fintype (Σ j : {j : Fin d // j ≠ i}, Path d n j.1))

def colors {d : ℕ} : {n : ℕ} → {i : Fin d} → Path d n i → List (Fin d)
  | 0, i, _ => [i]
  | _ + 1, i, p => i :: colors p.2

@[simp] theorem colors_length {d n : ℕ} {i : Fin d} (p : Path d n i) :
    (colors p).length = n + 1 := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp [colors, ih]

@[simp] theorem colors_head? {d n : ℕ} {i : Fin d} (p : Path d n i) :
    (colors p).head? = some i := by
  cases n <;> rfl

theorem colors_isChain {d n : ℕ} {i : Fin d} (p : Path d n i) :
    List.IsChain (fun a b : Fin d => a ≠ b) (colors p) := by
  induction n generalizing i with
  | zero => simp [colors]
  | succ n ih =>
      rw [colors, List.isChain_cons]
      refine ⟨?_, ih p.2⟩
      intro j hj
      have hji : p.1.1 = j := by simpa using hj
      subst j
      exact Ne.symm p.1.2

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {d : ℕ}

def pathValue (S : Fin d → E ≃ₗᵢ[𝕜] E) (y : ColoredEdgeLifts.EdgeSpace d E) :
    {n : ℕ} → {i : Fin d} → Path d n i → E
  | 0, i, _ => y i
  | _ + 1, i, p => S i (pathValue S y p.2)

@[simp] theorem pathValue_zero (S : Fin d → E ≃ₗᵢ[𝕜] E)
    (y : ColoredEdgeLifts.EdgeSpace d E) (i : Fin d) (p : Path d 0 i) :
    pathValue S y p = y i := rfl

@[simp] theorem pathValue_succ (S : Fin d → E ≃ₗᵢ[𝕜] E)
    (y : ColoredEdgeLifts.EdgeSpace d E) {n : ℕ} {i : Fin d}
    (p : Path d (n + 1) i) : pathValue S y p = S i (pathValue S y p.2) := rfl

theorem forwardOperator_pow_apply [CompleteSpace E]
    (hd : 0 < d) (S : Fin d → E ≃ₗᵢ[𝕜] E) (r : ℝ)
    (n : ℕ) (y : ColoredEdgeLifts.EdgeSpace d E) (i : Fin d) :
    (ColoredEdgeLifts.forwardOperator hd S r ^ n) y i =
      (r : 𝕜) ^ n • ∑ p : Path d n i, pathValue S y p := by
  induction n generalizing i with
  | zero =>
      change y i = (r : 𝕜) ^ 0 • ∑ _ : PUnit, y i
      simp
  | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp,
        ColoredEdgeLifts.forwardOperator_apply]
      simp_rw [ih, map_smul, map_sum]
      rw [← Finset.smul_sum, smul_smul, ← pow_succ']
      congr 1
      rw [show (∑ p : Path d (n + 1) i, pathValue S y p) =
          ∑ j : {j : Fin d // j ≠ i}, ∑ p : Path d n j.1, S i (pathValue S y p) from
        Fintype.sum_sigma _]
      exact Finset.sum_subtype (Finset.univ.erase i) (by simp) _

end Problem367.ColoredPathAverage

end

end OAI
