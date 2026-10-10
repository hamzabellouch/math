import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionWeightCells
import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionPairCells
import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionStorageBounds

namespace OAI

/-! # Constructing compression arrays with an explicit live-cell trace

All seven compact lists are produced before the capacity test. Only its
successful branch allocates the three raw lists and the two pair lists.
The completed arrays are shared by subsequent residue passes.
-/

namespace LowSpaceSubsetSum.CompressionArrayCells

open scoped BigOperators
variable {n : ℕ}

def compactLists (a : Fin n → ℤ) (V : CompressionArrayBuild.Blocks n) :
    Vector (List ℤ × ℕ) 7 × ℕ :=
  let rows := Vector.ofFn (fun i => CompressionWeightCells.compact a (V.compact i))
  (rows.map Prod.fst, (∑ i : Fin 7, rows[i.val].2)+
    4*(∑ i : Fin 7, rows[i.val].1.1.length)+64)

theorem compactLists_value (a : Fin n → ℤ) (V : CompressionArrayBuild.Blocks n) :
    (compactLists a V).1 = CompressionArrayBuild.compactLists a V := by
  apply Vector.ext
  intro i hi
  simp only [compactLists, CompressionArrayBuild.compactLists, Vector.getElem_map,
    Vector.getElem_ofFn, CompressionWeightCells.compact_value]

private theorem compact_length (a : Fin n → ℤ) (xs : List (Fin n)) :
    (CompressionWeightCells.compact a xs).1.1.length ≤ 2^xs.length := by
  rw [CompressionWeightCells.compact_value]
  simp only [CompressionWeights.compact]
  rw [CountedDedup.run_value]
  have h := (List.destutter_sublist (R := (· ≠ ·))
    (MeasuredSort.sort (fun x y : ℤ => (decide (x ≤ y), 1))
      (CompressionWeights.raw a xs).1).1).length_le
  simpa only [MeasuredSort.sort_value, List.length_mergeSort, CompressionWeights.raw_length] using h

theorem compactLists_cells (a : Fin n → ℤ) (V : CompressionArrayBuild.Blocks n) (C : ℕ)
    (hl : ∀ i, (V.compact i).length ≤ n)
    (hc : ∀ i, 2^(V.compact i).length ≤ C) :
    (compactLists a V).2 ≤ 4096*(n+2)^2*(C+1) := by
  have hp (i : Fin 7) := (CompressionWeightCells.compact_cells a (V.compact i) (hl i)).trans
    (Nat.mul_le_mul_left (512*(n+2)^2) (Nat.add_le_add_right (hc i) 1))
  have hlen (i : Fin 7) := (compact_length a (V.compact i)).trans (hc i)
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 7))) => hp i)
  have ht := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 7))) => hlen i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hs ht
  simp only [compactLists, Vector.getElem_ofFn, Fin.eta]
  have hbase : 1 ≤ (n+2)^2 := Nat.one_le_pow _ _ (by omega)
  have hmul := Nat.mul_le_mul_right (C+1) hbase
  nlinarith only [hs, ht, hmul]

def assemble (lists : Vector (List ℤ × ℕ) 7) (l r₀ r₁ : List ℤ) :
    (PreparedCompressionPass.Arrays × ℕ) × ℕ :=
  let p₀ := CompressionPairCells.run lists[1].1 r₀
  let p₁ := CompressionPairCells.run lists[3].1 r₁
  let A : PreparedCompressionPass.Arrays :=
    ⟨![lists[4].1.toArray, lists[6].1.toArray, lists[0].1.toArray, lists[2].1.toArray],
      ![lists[5].1.toArray, l.toArray, p₀.1.1.toArray, p₁.1.1.toArray]⟩
  ((A,p₀.1.2+p₁.1.2+PreparedCompressionPass.size A+10),
    p₀.2+p₁.2+4*PreparedCompressionPass.size A+
      4*((∑ i : Fin 7, lists[i.val].1.length)+l.length+r₀.length+r₁.length)+64)

theorem assemble_value (lists : Vector (List ℤ × ℕ) 7) (l r₀ r₁ : List ℤ) :
    (assemble lists l r₀ r₁).1 = CompressionArrayBuild.assemble lists l r₀ r₁ := by
  simp only [assemble, CompressionArrayBuild.assemble, CompressionPairCells.value]

theorem assemble_cells (lists : Vector (List ℤ × ℕ) 7) (l r₀ r₁ : List ℤ) (C : ℕ)
    (hlist : ∀ i : Fin 7, lists[i.val].1.length ≤ C)
    (hl : l.length ≤ C) (hr₀ : r₀.length ≤ C) (hr₁ : r₁.length ≤ C)
    (hp₀ : lists[1].1.length*r₀.length ≤ C)
    (hp₁ : lists[3].1.length*r₁.length ≤ C) :
    (assemble lists l r₀ r₁).2 ≤ 512*(C+1) := by
  have ha (i : Fin 4) :
      ((assemble lists l r₀ r₁).1.1.first i).size ≤ C ∧
      ((assemble lists l r₀ r₁).1.1.second i).size ≤ C := by
    fin_cases i
    · exact ⟨hlist 4, hlist 5⟩
    · exact ⟨hlist 6, hl⟩
    · simpa [assemble, CompressionPairCells.length] using
        And.intro (hlist 0) hp₀
    · simpa [assemble, CompressionPairCells.length] using
        And.intro (hlist 2) hp₁
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) =>
    Nat.add_le_add (ha i).1 (ha i).2)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hs
  have hsize : PreparedCompressionPass.size (assemble lists l r₀ r₁).1.1 ≤ 8*C+1 := by
    unfold PreparedCompressionPass.size
    omega
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 7))) => hlist i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  have h₀ := CompressionPairCells.cells lists[1].1 r₀
  have h₁ := CompressionPairCells.cells lists[3].1 r₁
  have hc₀ := hlist 1
  have hc₁ := hlist 3
  norm_num at hc₀ hc₁
  change _+_+4*PreparedCompressionPass.size (assemble lists l r₀ r₁).1.1+_+64 ≤ _
  nlinarith only [h₀, h₁, hc₀, hc₁, hl, hr₀, hr₁, hp₀, hp₁, hsize, hsum]

def run (a : Fin n → ℤ) (V : CompressionArrayBuild.Blocks n) (cap : ℕ) :
    (Option PreparedCompressionPass.Arrays × ℕ) × ℕ :=
  let compact := compactLists a V
  let lists := compact.1
  let cw := ∑ i : Fin 7, (lists[i.val].2+lists[i.val].1.length)
  if CompressionArrayBuild.passed lists cap then
    let l := MixerWeightCells.raw a V.left
    let r₀ := MixerWeightCells.raw a (V.right 0)
    let r₁ := MixerWeightCells.raw a (V.right 1)
    let out := assemble lists l.1.1 r₀.1.1 r₁.1.1
    ((some out.1.1,cw+l.1.2+r₀.1.2+r₁.1.2+out.1.2+30),
      compact.2+l.2+r₀.2+r₁.2+out.2+
        4*((∑ i : Fin 7, lists[i.val].1.length)+l.1.1.length+r₀.1.1.length+r₁.1.1.length)+64)
  else ((none,cw+30),compact.2+64)

theorem value (a : Fin n → ℤ) (V : CompressionArrayBuild.Blocks n) (cap : ℕ) :
    (run a V cap).1 = CompressionArrayBuild.run a V cap := by
  simp only [run, compactLists_value, CompressionArrayBuild.run]
  split
  · simp only [MixerWeightCells.raw_value, assemble_value]
  · rfl

private theorem source_pair_bounds (D : CompressionData n) (e : Equiv.Perm (Fin n))
    (hn : 10000 ≤ n) (he : D.compactTests e = true) :
    ((compactLists D.weights (CompressionArrayBuild.source D e)).1[1].1).length *
        (MixerWeightCells.raw D.weights ((CompressionArrayBuild.source D e).right 0)).1.1.length ≤
          compressionDictionaryCapacity n ∧
    ((compactLists D.weights (CompressionArrayBuild.source D e)).1[3].1).length *
        (MixerWeightCells.raw D.weights ((CompressionArrayBuild.source D e).right 1)).1.1.length ≤
          compressionDictionaryCapacity n := by
  have h₀ := (D.stored_lists_capacity e he (by omega) 2).2
  have h₁ := (D.stored_lists_capacity e he (by omega) 3).2
  change (pairSumList (compactWeightList D.weights (D.block e 1))
    (rawWeightList D.weights (D.rightRaw e 0))).length ≤ _ at h₀
  change (pairSumList (compactWeightList D.weights (D.block e 3))
    (rawWeightList D.weights (D.rightRaw e 1))).length ≤ _ at h₁
  simp only [pairSumList_length] at h₀ h₁
  have hc₀ : ((CompressionArrayBuild.compactLists D.weights
      (CompressionArrayBuild.source D e))[1]).1 = compactWeightList D.weights (D.block e 1) :=
    CompressionArrayBuild.compactLists_source D e 1
  have hc₁ : ((CompressionArrayBuild.compactLists D.weights
      (CompressionArrayBuild.source D e))[3]).1 = compactWeightList D.weights (D.block e 3) :=
    CompressionArrayBuild.compactLists_source D e 3
  simp only [compactLists_value, hc₀, hc₁]
  simpa only [MixerWeightCells.raw_value, CompressionArrayBuild.source,
    CompressionWeights.raw_source] using And.intro h₀ h₁

theorem cells (D : CompressionData n) (e : Equiv.Perm (Fin n)) (hn : 10000 ≤ n) :
    (run D.weights (CompressionArrayBuild.source D e)
      (2^CompressionSetup.executableCapExponent n)).2 ≤
        8192*(n+2)^2*(compressionDictionaryCapacity n+1) := by
  let V := CompressionArrayBuild.source D e
  let C := compressionDictionaryCapacity n
  have hl := CompressionStorageBounds.source_lengths D e hn
  have hexp : 199*n/1000 ≤ n := by omega
  have hcompact (i : Fin 7) : (V.compact i).length ≤ n := (hl.1 i).trans hexp
  have hpow (i : Fin 7) : 2^(V.compact i).length ≤ C :=
    Nat.pow_le_pow_right (by decide) (hl.1 i)
  have hrawL := CompressionStorageBounds.raw_bound D.weights V.left hl.2.1
  have hraw₀ := CompressionStorageBounds.raw_bound D.weights (V.right 0) (hl.2.2 0)
  have hraw₁ := CompressionStorageBounds.raw_bound D.weights (V.right 1) (hl.2.2 1)
  have hlist (i : Fin 7) : ((compactLists D.weights V).1[i.val].1).length ≤ C := by
    rw [compactLists_value]
    simpa only [CompressionArrayBuild.compactLists, Vector.getElem_ofFn,
      CompressionWeightCells.compact_value] using
      ((compact_length D.weights (V.compact i)).trans (hpow i))
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 7))) => hlist i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  have hc := compactLists_cells D.weights V C hcompact hpow
  have rawCells (xs : List (Fin n)) (hx : xs.length ≤ 199*n/1000) :
      (MixerWeightCells.raw D.weights xs).2 ≤ 64*(n+2)*(C+1) :=
    (MixerWeightCells.raw_cells D.weights xs (hx.trans hexp)).trans
      (Nat.mul_le_mul_left (64*(n+2))
        (Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hx) 1))
  have hL := rawCells V.left hl.2.1
  have h₀ := rawCells (V.right 0) (hl.2.2 0)
  have h₁ := rawCells (V.right 1) (hl.2.2 1)
  have hdegree : n+2 ≤ (n+2)^2 := by nlinarith
  have hbase : 1 ≤ (n+2)^2 := Nat.one_le_pow _ _ (by omega)
  have hm := Nat.mul_le_mul_right (C+1) hdegree
  have hb := Nat.mul_le_mul_right (C+1) hbase
  change (run D.weights V _).2 ≤ 8192*(n+2)^2*(C+1)
  unfold run
  dsimp only
  split
  next hp =>
    have he : D.compactTests e = true := by
      simpa only [V, compactLists_value, CompressionArrayBuild.passed_source] using hp
    have hpairs := source_pair_bounds D e hn he
    have ha := assemble_cells (compactLists D.weights V).1
      (MixerWeightCells.raw D.weights V.left).1.1
      (MixerWeightCells.raw D.weights (V.right 0)).1.1
      (MixerWeightCells.raw D.weights (V.right 1)).1.1 C hlist
      (by simpa only [MixerWeightCells.raw_value] using hrawL)
      (by simpa only [MixerWeightCells.raw_value] using hraw₀)
      (by simpa only [MixerWeightCells.raw_value] using hraw₁) hpairs.1 hpairs.2
    have hlenL : (MixerWeightCells.raw D.weights V.left).1.1.length ≤ C := by
      simpa only [MixerWeightCells.raw_value] using hrawL
    have hlen₀ : (MixerWeightCells.raw D.weights (V.right 0)).1.1.length ≤ C := by
      simpa only [MixerWeightCells.raw_value] using hraw₀
    have hlen₁ : (MixerWeightCells.raw D.weights (V.right 1)).1.1.length ≤ C := by
      simpa only [MixerWeightCells.raw_value] using hraw₁
    change _+_+_+_+_+4*(_+_+_+_)+64 ≤ _
    simp only [Nat.mul_assoc] at hc hL h₀ h₁ hm hb ⊢
    nlinarith only [hc, hL, h₀, h₁, hm, hb, ha, hsum, hlenL, hlen₀, hlen₁]
  · change _+64 ≤ _
    simp only [Nat.mul_assoc] at hc hb ⊢
    nlinarith only [hc, hb]

theorem cells_scale (D : CompressionData n) (e : Equiv.Perm (Fin n)) (hn : 10000 ≤ n) :
    (run D.weights (CompressionArrayBuild.source D e)
      (2^CompressionSetup.executableCapExponent n)).2 ≤
        inputScale D.input^4*(compressionDictionaryCapacity n+1) := by
  have hu : n+2 ≤ inputScale D.input := by unfold inputScale; omega
  have hu0 : 10000 ≤ inputScale D.input := by omega
  have hs := Nat.pow_le_pow_left hu 2
  have hc : 8192 ≤ inputScale D.input^2 := by nlinarith only [hu0]
  have hm := Nat.mul_le_mul hc hs
  have he : 8192*(n+2)^2 ≤ inputScale D.input^4 := by
    simpa only [← pow_add] using hm
  exact (cells D e hn).trans (Nat.mul_le_mul_right _ he)

end LowSpaceSubsetSum.CompressionArrayCells

end OAI
