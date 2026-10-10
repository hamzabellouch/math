import OAI.Algebra.DepthFive.MatrixPaths
import OAI.Algebra.DepthFive.UpperGateCounting

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335.BlockData

variable {n : ℕ}

/-- Block-entry gates: block number and two matrix indices. -/
abbrev Middle (blocks : List (List (Fin n))) :=
  Fin blocks.length × Fin n × Fin n

def paths (blocks : List (List (Fin n))) (m : Middle blocks) :=
  matrixEntryPaths (blocks.get m.1) m.2.1 m.2.2

/-- Each lower gate is an enumerated path for one block entry. -/
abbrev Lower (blocks : List (List (Fin n))) :=
  Σ m : Middle blocks, Fin (paths blocks m).length

def lowerInputs (blocks : List (List (Fin n))) (p : Lower blocks) :
    List (Fin n × Fin n × Fin n) :=
  (paths blocks p.1).get p.2

def middleInputs (K : Type*) [One K] (blocks : List (List (Fin n)))
    (m : Middle blocks) : List (K × Lower blocks) :=
  List.ofFn fun p : Fin (paths blocks m).length => (1, ⟨m, p⟩)

def middleDegree (blocks : List (List (Fin n))) (m : Middle blocks) : ℕ :=
  (blocks.get m.1).length

def upperPaths (blocks : List (List (Fin n))) (z : Fin n) :
    List (List (Middle blocks)) :=
  matrixEntryPaths (List.finRange blocks.length) z z

abbrev Upper (blocks : List (List (Fin n))) (z : Fin n) :=
  Fin (upperPaths blocks z).length

def upperInputs (blocks : List (List (Fin n))) (z : Fin n)
    (p : Upper blocks z) : List (Middle blocks) :=
  (upperPaths blocks z).get p

def outputInputs (K : Type*) [One K] (blocks : List (List (Fin n)))
    (z : Fin n) : List (K × Upper blocks z) :=
  List.ofFn fun p : Upper blocks z => (1, p)

theorem lowerInputs_labels (blocks : List (List (Fin n))) (p : Lower blocks) :
    (lowerInputs blocks p).map Prod.fst = blocks.get p.1.1 := by
  exact matrixEntryPaths_labels _ _ _ _ (List.get_mem _ _)

theorem lowerInputs_length (blocks : List (List (Fin n))) (p : Lower blocks) :
    (lowerInputs blocks p).length = middleDegree blocks p.1 := by
  exact matrixEntryPaths_path_length _ _ _ _ (List.get_mem _ _)

theorem middleInputs_homogeneous (K : Type*) [One K]
    (blocks : List (List (Fin n))) (m : Middle blocks)
    (entry : K × Lower blocks) (h : entry ∈ middleInputs K blocks m) :
    (lowerInputs blocks entry.2).length = middleDegree blocks m := by
  obtain ⟨p, rfl⟩ := List.mem_ofFn.mp h
  exact lowerInputs_length blocks ⟨m, p⟩

theorem upperInputs_labels (blocks : List (List (Fin n))) (z : Fin n)
    (p : Upper blocks z) :
    (upperInputs blocks z p).map Prod.fst = List.finRange blocks.length := by
  exact matrixEntryPaths_labels _ _ _ _ (List.get_mem _ _)

theorem upperInputs_degree (blocks : List (List (Fin n))) (z : Fin n)
    (p : Upper blocks z) :
    ((upperInputs blocks z p).map (middleDegree blocks)).sum =
      (blocks.map List.length).sum := by
  change ((upperInputs blocks z p).map (fun m => (blocks.get m.1).length)).sum = _
  have h := congrArg (fun l : List (Fin blocks.length) =>
    (l.map (fun b => (blocks.get b).length)).sum) (upperInputs_labels blocks z p)
  have hg := congrArg (List.map List.length) (List.map_get_finRange blocks)
  simp only [List.map_map, Function.comp_def] at hg
  simpa only [List.map_map, Function.comp_def, middleDegree, hg] using h

theorem paths_length (blocks : List (List (Fin n)))
    (hne : ∀ b : Fin blocks.length, blocks.get b ≠ []) (m : Middle blocks) :
    (paths blocks m).length = n ^ ((blocks.get m.1).length - 1) := by
  simpa [paths] using matrixEntryPaths_length (blocks.get m.1) (hne m.1) m.2.1 m.2.2

theorem middleInputs_ne_nil (K : Type*) [One K]
    (blocks : List (List (Fin n))) (hn : 0 < n)
    (hne : ∀ b : Fin blocks.length, blocks.get b ≠ []) (m : Middle blocks) :
    middleInputs K blocks m ≠ [] := by
  apply List.ne_nil_of_length_pos
  simpa [middleInputs, paths_length blocks hne] using
    (Nat.pow_pos hn : 0 < n ^ ((blocks.get m.1).length - 1))

theorem upperPaths_length (blocks : List (List (Fin n))) (hb : blocks ≠ []) (z : Fin n) :
    (upperPaths blocks z).length = n ^ (blocks.length - 1) := by
  have h : List.finRange blocks.length ≠ [] := by
    simpa using hb
  simpa [upperPaths] using matrixEntryPaths_length (List.finRange blocks.length) h z z

theorem outputInputs_ne_nil (K : Type*) [One K]
    (blocks : List (List (Fin n))) (hb : blocks ≠ []) (z : Fin n) :
    outputInputs K blocks z ≠ [] := by
  apply List.ne_nil_of_length_pos
  have hn : 0 < n := Nat.zero_lt_of_lt z.isLt
  simpa [outputInputs, upperPaths_length blocks hb z] using
    (Nat.pow_pos hn : 0 < n ^ (blocks.length - 1))

@[simp] theorem card_middle (blocks : List (List (Fin n))) :
    Fintype.card (Middle blocks) = blocks.length * n ^ 2 := by
  simp [Middle, pow_two]

theorem card_upper (blocks : List (List (Fin n))) (hb : blocks ≠ []) (z : Fin n) :
    Fintype.card (Upper blocks z) = n ^ (blocks.length - 1) := by
  simpa only [Fintype.card_fin] using upperPaths_length blocks hb z

theorem card_lower (blocks : List (List (Fin n)))
    (hne : ∀ b : Fin blocks.length, blocks.get b ≠ []) :
    Fintype.card (Lower blocks) =
      ∑ b : Fin blocks.length, n ^ ((blocks.get b).length + 1) := by
  simp only [Lower, Fintype.card_sigma, Fintype.card_fin]
  simp_rw [paths_length blocks hne]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  have hd : 1 ≤ (blocks.get b).length := List.length_pos_iff.mpr (hne b)
  have hcount := block_entry_monomial_count n (blocks.get b).length hd
  simpa only [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun,
    Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul, Nat.cast_id, Nat.mul_assoc] using hcount

theorem card_lower_le (blocks : List (List (Fin n))) (t : ℕ)
    (hn : 1 ≤ n) (hne : ∀ b : Fin blocks.length, blocks.get b ≠ [])
    (hlen : ∀ b : Fin blocks.length, (blocks.get b).length ≤ t) :
    Fintype.card (Lower blocks) ≤ blocks.length * n ^ (t + 1) := by
  rw [card_lower blocks hne]
  calc
    ∑ b : Fin blocks.length, n ^ ((blocks.get b).length + 1) ≤
        ∑ _b : Fin blocks.length, n ^ (t + 1) := by
      exact Finset.sum_le_sum (fun b _ =>
        pow_le_pow_right₀ hn (Nat.add_le_add_right (hlen b) 1))
    _ = blocks.length * n ^ (t + 1) := by simp

end Problem335.BlockData

end

end OAI
