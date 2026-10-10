import OAI.NumberTheory.Ostmann.Characters.CharacterWordGeometry
import OAI.NumberTheory.Ostmann.Arithmetic.FiniteAtomIntervalIteration
import OAI.NumberTheory.Ostmann.ZeroDensity.InitialIntervalZero
import OAI.NumberTheory.Ostmann.Construction.InitialGapRate
import OAI.NumberTheory.Ostmann.Characters.PivotLossBudget

namespace OAI

/-! # Iteration with the selected word bin and actual character cell products -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

noncomputable def characterPivotRole (k n : ℕ) : CharacterRole k :=
  if h : n < k then characterPivotAtom ⟨n, h⟩ else (true, none)

@[simp] theorem characterPivotRole_eq {k n : ℕ} (hn : n < k) :
    characterPivotRole k n = characterPivotAtom ⟨n, hn⟩ := by
  simp only [characterPivotRole, dite_eq_left hn]

noncomputable def characterPivotCap {k : ℕ} (T : Fin k → ℝ) (C : ℝ) (n : ℕ) : ℕ :=
  if h : n < k then naturalProductCap (T ⟨n, h⟩ + C) else 0

@[simp] theorem characterPivotCap_eq {k n : ℕ} (hn : n < k) (T : Fin k → ℝ) (C : ℝ) :
    characterPivotCap T C n = naturalProductCap (T ⟨n, hn⟩ + C) := by
  simp only [characterPivotCap, dite_eq_left hn]

/-- The transfer geometry and all pivot losses are derived from the chosen
cell endpoints. The remaining diagonal premise is the literal matching sum
estimated separately by the selected-bulk energy and cancellation theorems. -/
theorem eventual_character_atom_iteration (k : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (hr : ∀ j, 0 < r j) (B B₀ z c Cmass : ℝ)
    (hB : 0 ≤ B) (hz : 1 ≤ z) (hc : 1 ≤ c) (hCmass : 0 ≤ Cmass)
    (hbudget : Cmass * (∑ j, (r j : ℝ)) ≤ z / 4) :
    ∀ᶠ L : ℝ in atTop,
    let m := ⌊z * L⌋₊
    ∀ (J : ℕ), 0 < J → ∀ (a : Fin k → Bool → ℝ) (F : ℝ),
    let T := characterPivotTarget k J (fun j => a j false + a j true)
      (fun j => characterPivotGap B z m j.val)
    let V := naturalTransferCutoff (characterBaseGap B z m) m
    let cap := characterPivotCap T (characterRangeError k c)
    ∀ (cellLo cellHi : (Σ v, Fin (characterSize m r f v)) → ℕ),
    let lo := initialWordAtomLower J (fun v => ∏ i, cellLo ⟨(true, some v), i⟩)
    let hi := initialWordAtomUpper J (fun v => ∏ i, cellHi ⟨(true, some v), i⟩)
    ∀ (χ : (Σ v, Fin (characterSize m r f v)) → ∀ p : ℕ, DirichletCharacter ℂ p)
      (κ : (Σ v, Fin (characterSize m r f v)) → ℕ → ℂ)
      (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
      (Q : (Σ v, Fin (characterSize m r f v)) → Finset ℕ)
      (leaf : ScheduleAtomState (characterRole k) → ℤ → ℂ) (center : ∀ p : ℕ, ZMod p),
    (∀ i q, q ∈ P → ‖κ i q‖ ≤ 1) →
    (∀ i, Q i ⊆ P) → (∀ i, (∑ q ∈ Q i, (q : ℝ)⁻¹) ≠ 0) →
    (∀ i q, q ∈ Q i → cellLo i ≤ q ∧ q ≤ cellHi i) →
    (∀ v, Real.exp (characterLogCenter J T a F (true, some v) - c) ≤
      ∏ i, cellLo ⟨(true, some v), i⟩) →
    (∀ v, (∏ i, cellHi ⟨(true, some v), i⟩ : ℕ) ≤
      Real.exp (characterLogCenter J T a F (true, some v) + c)) →
    (∀ j : Fin k, ∀ i : Fin (r j),
      (∑ q ∈ Q ⟨characterPivotAtom j, i⟩, (q : ℝ)⁻¹)⁻¹ ≤ Real.exp (Cmass * L)) →
    (∀ q ∈ P, V k < q) →
    (Real.exp (-B₀ * m) ≤ ‖scheduledConstituentAmplitude (characterRole k)
      (characterSize m r f) χ κ (characterPivot m r f hr) P hP Q lo hi V cap leaf center 0‖) →
    (∀ j < k, scheduledConstituentDiagonal (characterRole k) (characterSize m r f) χ κ
      (characterPivot m r f hr) P hP Q lo hi V cap leaf center (characterPivotRole k j) j ≤
        Real.exp (-(2 * (B₀ + 1) + 3) * (2 : ℝ) ^ j * m)) →
    Real.exp (-(B₀ + 1) * (2 : ℝ) ^ k * m) ≤
      ‖scheduledConstituentAmplitude (characterRole k) (characterSize m r f) χ κ
        (characterPivot m r f hr) P hP Q lo hi V cap leaf center k‖ := by
  have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz
  have hg := eventually_bulkCount z hz0 _
    ((tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (eventual_character_word_geometry k B z c hB hz hc))
  filter_upwards [hg, eventual_pivot_loss_budget k r Cmass z hCmass hz0 hbudget,
    eventually_bulkCount_bounds z hz0] with L hgeom hloss hmbounds
  intro m J hJ a F T V cap cellLo cellHi lo hi χ κ P hP Q leaf center
    hκ hQP hQ hcell hlo hhi hmass hlarge hinit hdiag
  have hgeometry := hgeom J a F
    (fun v => ∏ i, cellLo ⟨(true, some v), i⟩)
    (fun v => ∏ i, cellHi ⟨(true, some v), i⟩) hlo hhi
  have hnonneg : 0 ≤ characterBaseGap B z m :=
    mul_nonneg (add_nonneg hB (mul_nonneg (by norm_num) (Real.log_nonneg hz)))
      (Nat.cast_nonneg m)
  have hV : Monotone V := naturalTransferCutoff_monotone _ _ hnonneg
  let loss : ℕ → ℝ := fun j => if h : j < k then pivotLogLoss (r ⟨j, h⟩) Cmass L else 0
  have hloss_eq (j : ℕ) (hj : j < k) : loss j = pivotLogLoss (r ⟨j, hj⟩) Cmass L := by
    simp only [loss, dite_eq_left hj]
  apply scheduled_constituent_atom_interval_iteration (loss := loss) (B₀ := B₀) (m := (m : ℝ)) (characterRole k) (characterSize m r f)
    χ κ (characterPivot m r f hr) k (characterPivot_role m r f hr) (characterPivotRole k)
    (fun j hj => by simp [hj]) (fun j hj v hv => by
      rw [characterPivotRole_eq hj]
      exact characterPivotAtom_unique ⟨j, hj⟩ v hv)
    P hP Q hκ hQP hQ lo hi cellLo cellHi hcell V cap hV leaf center
  · intro j hj
    simpa only [characterPivotRole_eq hj] using (hgeometry j hj).1
  · intro j hj
    simpa only [cap, T, characterPivotRole_eq hj, characterPivotCap_eq hj] using (hgeometry j hj).2.1
  · intro j hj
    rw [characterPivotRole_eq hj]
    exact le_rfl
  · intro j hj
    rw [characterPivotRole_eq hj]
    exact le_rfl
  · exact fullAtomTransferWeight_zero_of_interval (characterRole k) lo hi V cap leaf
      (true, none) (initialWordAtomLower_word_gt_one J hJ _ true)
  · intro j hj
    simpa only [cap, T, V, characterPivotCap_eq hj] using (hgeometry j hj).2.2.1
  · intro j hj
    simpa only [characterPivotRole_eq hj] using (hgeometry j hj).2.2.2.1
  · exact hlarge
  · intro j hj
    rw [hloss_eq j hj]
    exact hloss.1 ⟨j, hj⟩
  · intro j hj
    rw [hloss_eq j hj, characterPivotRole_eq hj]
    exact harmonic_pivot_loss_le (fun i => Q ⟨characterPivotAtom ⟨j, hj⟩, i⟩)
      Cmass L (hmass ⟨j, hj⟩)
  · exact Nat.cast_nonneg m
  · have he : (∑ j ∈ Finset.range k, (loss j + Real.log 2)) =
        ∑ j : Fin k, (pivotLogLoss (r j) Cmass L + Real.log 2) := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j _
      rw [hloss_eq j.val j.isLt]
    rw [he]
    exact hloss.2
  · exact hinit
  · exact hdiag

end Ostmann

end OAI
