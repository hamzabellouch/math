import OAI.MeasureTheory.Falconer.Estimates.RegularizationCardinality
import OAI.MeasureTheory.Falconer.Recursion.LeafMassBins

namespace OAI

namespace PlanarFalconer

abbrev blockDepth (N B i : ℕ) : ℕ := N-i*B

noncomputable def blockLabel (L : Finset CellPath) (N B : ℕ)
    (f : CellPath → List ℕ) : ℕ → CellPath → List ℕ
  | 0 => f
  | i+1 => extendLabel L (blockDepth N B (i+1)) (blockDepth N B i) (blockLabel L N B f i)

theorem blockDepth_antitone (N B : ℕ) : Antitone (blockDepth N B) := by
  intro i j hij
  exact Nat.sub_le_sub_left (Nat.mul_le_mul_right B hij) N

theorem blockDepth_gap (N B i : ℕ) : blockDepth N B i - blockDepth N B (i+1) ≤ B := by
  dsimp only [blockDepth]
  rw [Nat.add_mul, one_mul]
  omega

theorem blockDepth_terminal (N : ℕ) {B : ℕ} (hB : 0 < B) :
    blockDepth N B (N/B+1) = 0 := by
  have h := Nat.lt_mul_div_succ N hB
  simp only [blockDepth]
  rw [Nat.mul_comm] at h
  omega

theorem blockLabel_old (L : Finset CellPath) (N B : ℕ) (f : CellPath → List ℕ)
    {i j : ℕ} (hij : i ≤ j) {p q : CellPath}
    (he : blockLabel L N B f j p = blockLabel L N B f j q) :
    blockLabel L N B f i p = blockLabel L N B f i q := by
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst i
    exact he
  | succ j ih =>
    by_cases heq : i = j+1
    · simpa only [heq] using he
    · exact ih (by omega) (extendLabel_old he)

theorem blockLabel_local (L : Finset CellPath) (N B : ℕ) (f : CellPath → List ℕ)
    {i j a : ℕ} (hij : i ≤ j) (ha : blockDepth N B i ≤ a)
    {p q : CellPath} (hpq : p.take a = q.take a) :
    blockLabel L N B f j p = blockLabel L N B f j q ↔
      blockLabel L N B f i p = blockLabel L N B f i q := by
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst i
    rfl
  | succ j ih =>
    by_cases heq : i = j+1
    · subst i; rfl
    · have hji : i ≤ j := by omega
      rw [blockLabel, extendLabel_local (take_eq_of_take_eq
        ((blockDepth_antitone N B (by omega : i ≤ j+1)).trans ha) hpq)]
      exact ih hji

theorem block_final_children (L : Finset CellPath) (N B : ℕ) (f : CellPath → List ℕ)
    {i K : ℕ} (hi : i < K) (p : CellPath) :
    labeledChildren L (blockLabel L N B f K)
      (blockDepth N B (i+1)) (blockDepth N B i) p =
    labeledChildren L (blockLabel L N B f i)
      (blockDepth N B (i+1)) (blockDepth N B i) p := by
  classical
  apply congrArg (Finset.image (List.take (blockDepth N B i)))
  apply Finset.filter_congr
  intro q _
  constructor
  · rintro ⟨ha,hf⟩
    exact ⟨ha,blockLabel_old L N B f (by omega) hf⟩
  · rintro ⟨ha,hf⟩
    refine ⟨ha,(blockLabel_local L N B f (by omega : i+1 ≤ K) le_rfl ha).mpr ?_⟩
    exact (extendLabel_local ha).mpr hf

theorem block_final_bin_eq (L : Finset CellPath) (N B : ℕ) (f : CellPath → List ℕ)
    {i K : ℕ} (hi : i < K) {p q : CellPath}
    (hclass : blockLabel L N B f K p = blockLabel L N B f K q) :
    Nat.log 2 (labeledChildren L (blockLabel L N B f K)
      (blockDepth N B (i+1)) (blockDepth N B i) p).card =
    Nat.log 2 (labeledChildren L (blockLabel L N B f K)
      (blockDepth N B (i+1)) (blockDepth N B i) q).card := by
  rw [block_final_children L N B f hi,block_final_children L N B f hi]
  exact (List.cons.inj (blockLabel_old L N B f (by omega : i+1 ≤ K) hclass)).1

theorem blockLabel_card_le {L : Finset CellPath} {N : ℕ} (hL : L ⊆ dyadicPaths N)
    (B : ℕ) (f : CellPath → List ℕ) (K : ℕ) :
    (L.image (blockLabel L N B f K)).card ≤ (2*N+1)^K * (L.image f).card := by
  classical
  induction K with
  | zero => simp [blockLabel]
  | succ K ih =>
    have hs := extendLabel_card_le (blockDepth_antitone N B (Nat.le_succ K))
      (Nat.sub_le N (K*B)) hL (blockLabel L N B f K)
    have hb : 2*(blockDepth N B K-blockDepth N B (K+1))+1 ≤ 2*N+1 := by
      have : blockDepth N B K ≤ N := Nat.sub_le _ _
      omega
    calc
      _ ≤ (2*N+1) * (L.image (blockLabel L N B f K)).card :=
        hs.trans (Nat.mul_le_mul_right _ hb)
      _ ≤ (2*N+1)*((2*N+1)^K*(L.image f).card) := Nat.mul_le_mul_left _ ih
      _ = _ := by rw [pow_succ]; ac_rfl

noncomputable def regularizationLeaves (Q : DyadicSquare) (μ : MeasureTheory.Measure Plane)
    (N : ℕ) : Finset CellPath := retainedLeaves Q μ N ((2:ENNReal)^(4*N))⁻¹

noncomputable def regularizationLabel (Q : DyadicSquare) (μ : MeasureTheory.Measure Plane)
    (N B : ℕ) : CellPath → List ℕ :=
  blockLabel (regularizationLeaves Q μ N) N B (sourceLeafLabel Q μ N) (N/B+1)

theorem regularization_label_count (Q : DyadicSquare) (μ : MeasureTheory.Measure Plane)
    (N B : ℕ) :
    ((regularizationLeaves Q μ N).image (regularizationLabel Q μ N B)).card ≤
      (2*N+1)^(N/B+1) * (4*N+1) := by
  classical
  exact (blockLabel_card_le (Finset.filter_subset _ _) B (sourceLeafLabel Q μ N) _).trans
    (Nat.mul_le_mul_left _ (sourceLeafLabel_card_le Q μ N _))

theorem regularization_label_mass_bin (Q : DyadicSquare) (μ : MeasureTheory.Measure Plane)
    (N B : ℕ) {p q : CellPath}
    (h : regularizationLabel Q μ N B p = regularizationLabel Q μ N B q) :
    leafMassBin N (μ (Q.descendant p).carrier).toReal =
      leafMassBin N (μ (Q.descendant q).carrier).toReal := by
  have := blockLabel_old (regularizationLeaves Q μ N) N B (sourceLeafLabel Q μ N)
    (Nat.zero_le (N/B+1)) h
  exact List.singleton_inj.mp this

end PlanarFalconer

end OAI
