import OAI.Combinatorics.BinaryEdit.SegmentCode
import OAI.Combinatorics.BinaryEdit.LCS

namespace OAI

namespace TreeEdit.BinaryLower.SegmentCode
open RandomMatching

/-- Array windows coincide with actual contiguous list segments. -/
theorem ofFn_window {α : Type*} {P : ℕ} (b : Fin P → α)
    (a i : ℕ) (hi : i+a ≤ P) :
    List.ofFn (fun t : Fin a => b (window a i hi t)) =
      ((List.ofFn b).drop i).take a := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_take, List.length_drop]
    omega
  · intro j hj hj'
    simp only [List.getElem_ofFn, List.getElem_take, List.getElem_drop]
    rfl

/-- The simultaneous increasing-matching property bounds the actual LCS of
contiguous codeword segments. -/
theorem SegmentSeparated.lcs_le {K P a₀ : ℕ} {c : Fin K → Fin P → Bool}
    (hc : SegmentSeparated c a₀) (k l : Fin K) (hkl : k ≠ l)
    (a i j : ℕ) (ha : a₀ ≤ a) (hi : i+a ≤ P) (hj : j+a ≤ P) :
    100 * lcs (((List.ofFn (c k)).drop i).take a)
      (((List.ofFn (c l)).drop j).take a) ≤ 99*a := by
  rw [← ofFn_window (c k) a i hi, ← ofFn_window (c l) a j hj]
  let x := List.ofFn (fun t : Fin a => c k (window a i hi t))
  let y := List.ofFn (fun t : Fin a => c l (window a j hj t))
  have hx : x.length = a := by simp [x]
  have hy : y.length = a := by simp [y]
  obtain ⟨⟨f, g, hfg⟩⟩ := exists_lcs_alignment x y
  let f' : IncreasingPositions a (lcs x y) :=
    ⟨fun t => Fin.cast hx (f t), (Fin.cast_strictMono hx).comp f.strictMono⟩
  let g' : IncreasingPositions a (lcs x y) :=
    ⟨fun t => Fin.cast hy (g t), (Fin.cast_strictMono hy).comp g.strictMono⟩
  apply hc k l hkl a i j ha hi hj (lcs x y) f' g'
  intro t
  simpa [x, y, f', g', Fin.cast] using hfg t

/-- The codebook construction for an arbitrary finite alphabet, using the
canonical concrete word type and the actual longest common subsequence. -/
theorem exists_lcs_separated_code (Γ : Type*) [Fintype Γ] (P a₀ : ℕ)
    (hprob : (Fintype.card Γ : ℝ)^2 * ((P+1 : ℕ) : ℝ)^3 *
      (9/10 : ℝ)^a₀ < 1) :
    ∃ c : Γ → Word Bool P,
      ∀ (k l : Γ), k ≠ l → ∀ (a i j : ℕ), a₀ ≤ a →
        i+a ≤ P → j+a ≤ P →
          100 * lcs (((c k).val.drop i).take a) (((c l).val.drop j).take a) ≤ 99*a := by
  classical
  obtain ⟨c, hc⟩ := exists_segmentSeparated (Fintype.card Γ) P a₀ hprob
  let e := Fintype.equivFin Γ
  let c' : Γ → Word Bool P := fun k => ⟨List.ofFn (c (e k)), by simp⟩
  refine ⟨c', ?_⟩
  intro k l hkl a i j ha hi hj
  exact hc.lcs_le (e k) (e l) (fun h => hkl (e.injective h)) a i j ha hi hj

/-- Real-valued separation convention `LCS ≤ 0.99 a` used in the manuscript. -/
theorem exists_lcs_separated_code_real (Γ : Type*) [Fintype Γ] (P a₀ : ℕ)
    (hprob : (Fintype.card Γ : ℝ)^2 * ((P+1 : ℕ) : ℝ)^3 *
      (9/10 : ℝ)^a₀ < 1) :
    ∃ c : Γ → Word Bool P,
      ∀ (k l : Γ), k ≠ l → ∀ (a i j : ℕ), a₀ ≤ a →
        i+a ≤ P → j+a ≤ P →
          (lcs (((c k).val.drop i).take a) (((c l).val.drop j).take a) : ℝ) ≤
            (99/100 : ℝ) * a := by
  obtain ⟨c, hc⟩ := exists_lcs_separated_code Γ P a₀ hprob
  refine ⟨c, ?_⟩
  intro k l hkl a i j ha hi hj
  have h := hc k l hkl a i j ha hi hj
  have h' : (100 : ℝ) * lcs (((c k).val.drop i).take a)
      (((c l).val.drop j).take a) ≤ 99 * a := by exact_mod_cast h
  linarith

end TreeEdit.BinaryLower.SegmentCode

end OAI
