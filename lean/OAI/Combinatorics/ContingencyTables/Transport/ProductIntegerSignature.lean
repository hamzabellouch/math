import OAI.Combinatorics.ContingencyTables.Transport.LineUnarySignature
import OAI.Combinatorics.ContingencyTables.Transport.FactorialSignatures

namespace OAI

/-!
# Raw integer signatures of the actual line and unary product

The line groups are disjoint. Integer counts at zero are masked; a repeated
removal from a count below two uses a zero second-update factor. This
identifies the actual integer matrix, including its box boundaries, with a
congruence of the proved line/unary update matrix.
-/

namespace ContingencyTables.ProductIntegerSignature

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS FactorialSignatures

variable {I G : Type*} [Fintype I] [Fintype G]

noncomputable def lineTotal (line : I → G) (z : I → ℕ) (g : G) : ℕ :=
  ∑ i, if line i = g then z i else 0

noncomputable def productWeight (line : I → G) (a : G → ℕ → ℝ) (b : I → ℕ → ℝ)
    (z : I → ℕ) : ℝ := (∏ g, a g (lineTotal line z g)) * ∏ i, b i (z i)

omit [Fintype G] in
lemma lineTotal_removeOne (line : I → G) (z : I → ℕ) (i : I) (hi : 0 < z i) (g : G) :
    lineTotal line (removeOne z i) g + (if line i = g then 1 else 0) = lineTotal line z g := by
  have h1 := Finset.sum_erase_add (s := Finset.univ) (a := i)
    (fun k => if line k = g then z k else 0) (Finset.mem_univ i)
  have h2 := Finset.sum_erase_add (s := Finset.univ) (a := i)
    (fun k => if line k = g then removeOne z i k else 0) (Finset.mem_univ i)
  have he : (∑ k ∈ Finset.univ.erase i, if line k = g then removeOne z i k else 0) =
      ∑ k ∈ Finset.univ.erase i, if line k = g then z k else 0 := by
    apply Finset.sum_congr rfl
    intro k hk
    simp [removeOne,(Finset.mem_erase.mp hk).1]
  rw [he] at h2
  have hepi : removeOne z i i = z i-1 := by simp [removeOne]
  rw [hepi] at h2
  unfold lineTotal
  by_cases hg : line i = g <;> simp only [hg,ite_true,ite_false] at h1 h2 ⊢ <;> omega

omit [Fintype G] in
lemma lineTotal_removeTwo (line : I → G) (z : I → ℕ) (i j : I)
    (hvalid : ValidPair z i j) (g : G) :
    lineTotal line (removeTwo z i j) g + (if line i = g then 1 else 0) +
      (if line j = g then 1 else 0) = lineTotal line z g := by
  have hj : 0 < removeOne z i j := hvalid.2
  have h1 := lineTotal_removeOne line z i hvalid.1 g
  have h2 := lineTotal_removeOne line (removeOne z i) j hj g
  change lineTotal line (removeOne (removeOne z i) j) g + _ + _ = _
  omega

/-- Literal product values after a valid integer removal coincide with
all line and unary update products. -/
theorem productWeight_removeTwo (line : I → G) (a : G → ℕ → ℝ) (b : I → ℕ → ℝ)
    (z : I → ℕ) (i j : I) (hvalid : ValidPair z i j) :
    productWeight line a b (removeTwo z i j) =
      lineUnaryRemoval line
        (fun g => a g (lineTotal line z g))
        (fun g => a g (lineTotal line z g-1))
        (fun g => if 2 ≤ lineTotal line z g then a g (lineTotal line z g-2) else 0)
        (fun k => b k (z k)) (fun k => b k (z k-1))
        (fun k => if 2 ≤ z k then b k (z k-2) else 0) i j := by
  unfold productWeight lineUnaryRemoval productTwoUpdates
  congr 1
  · apply Finset.prod_congr rfl
    intro g _
    have ht := lineTotal_removeTwo line z i j hvalid g
    by_cases hi : g = line i
    · by_cases hj : g = line j
      · have hn : 2 ≤ lineTotal line z g := by simp only [hi.symm,hj.symm,ite_true] at ht; omega
        have he : lineTotal line (removeTwo z i j) g = lineTotal line z g-2 := by
          simp only [hi.symm,hj.symm,ite_true] at ht; omega
        simp only [ite_eq_left hi,ite_eq_left hj,ite_eq_left hn,he]
      · have he : lineTotal line (removeTwo z i j) g = lineTotal line z g-1 := by
          simp only [hi.symm,ite_true,Ne.symm hj,ite_false] at ht; omega
        simp only [ite_eq_left hi,ite_eq_right hj,he]
    · by_cases hj : g = line j
      · have he : lineTotal line (removeTwo z i j) g = lineTotal line z g-1 := by
          simp only [Ne.symm hi,ite_false,hj.symm,ite_true] at ht; omega
        simp only [ite_eq_right hi,ite_eq_left hj,he]
      · have he : lineTotal line (removeTwo z i j) g = lineTotal line z g := by
          simp only [Ne.symm hi,Ne.symm hj,ite_false,add_zero] at ht; exact ht
        simp only [ite_eq_right hi,ite_eq_right hj,he]
  · apply Finset.prod_congr rfl
    intro k _
    by_cases hi : k = i
    · by_cases hj : k = j
      · have hn : 2 ≤ z k := by subst i; subst j; simp [ValidPair] at hvalid; omega
        have he : removeTwo z i j k = z k-2 := by simp [removeTwo,removeOne,hi.symm.trans hj,hi,Nat.sub_sub]
        simp only [ite_eq_left hi,ite_eq_left hj,ite_eq_left hn,he]
      · have he : removeTwo z i j k = z k-1 := by
          simp only [removeTwo,removeOne,ite_eq_left hi,ite_eq_right hj,Nat.sub_zero]
        simp only [ite_eq_left hi,ite_eq_right hj,he]
    · by_cases hj : k = j
      · have he : removeTwo z i j k = z k-1 := by
          simp only [removeTwo,removeOne,ite_eq_right hi,ite_eq_left hj,Nat.sub_zero]
        simp only [ite_eq_right hi,ite_eq_left hj,he]
      · simp only [removeTwo,removeOne,ite_eq_right hi,ite_eq_right hj,Nat.sub_zero]

noncomputable def activeMask (z : I → ℕ) : I → ℝ := fun i => if 0 < z i then 1 else 0

/-- The raw matrix is exactly the line/unary matrix with inactive integer
coordinates set to zero. Invalid repeated removals are also zero. -/
theorem integerRemoval_product_matrix (line : I → G) (a : G → ℕ → ℝ) (b : I → ℕ → ℝ)
    (z : I → ℕ) :
    integerRemovalMatrix (productWeight line a b) z =
      scaledMatrix (lineUnaryRemoval line
        (fun g => a g (lineTotal line z g))
        (fun g => a g (lineTotal line z g-1))
        (fun g => if 2 ≤ lineTotal line z g then a g (lineTotal line z g-2) else 0)
        (fun k => b k (z k)) (fun k => b k (z k-1))
        (fun k => if 2 ≤ z k then b k (z k-2) else 0)) (activeMask z) := by
  ext i j
  unfold integerRemovalMatrix scaledMatrix activeMask
  by_cases hv : ValidPair z i j
  · have hi : 0 < z i := hv.1
    have hj : 0 < z j := by dsimp [ValidPair] at hv; omega
    simp only [hv,ite_true,hi,hj,one_mul,mul_one]
    exact productWeight_removeTwo line a b z i j hv
  · rw [ite_eq_right hv]
    by_cases hi : 0 < z i
    · by_cases hj : 0 < z j
      · have hij : i = j := by by_contra h; exact hv ⟨hi,by simp [Ne.symm h,hj]⟩
        subst j
        have hn : ¬2 ≤ z i := by simp [ValidPair] at hv; omega
        simp only [hi,ite_true,one_mul,mul_one,lineUnaryRemoval]
        have hz : productTwoUpdates (fun k => b k (z k)) (fun k => b k (z k-1))
            (fun k => if 2 ≤ z k then b k (z k-2) else 0) i i = 0 := by
          apply Finset.prod_eq_zero (Finset.mem_univ i)
          simp [hn]
        rw [hz,mul_zero]
      · simp [hj]
    · simp [hi]

/-- Log-concavity of the actual scalar sequences gives the integer
signature required by factorial lifting and balanced marginalization. -/
theorem product_removal_onePositive (line : I → G) (a : G → ℕ → ℝ) (b : I → ℕ → ℝ)
    (z : I → ℕ)
    (ha : ∀ g n, n ≤ lineTotal line z g → 0 < a g n)
    (hb : ∀ i n, n ≤ z i → 0 < b i n)
    (halc : ∀ g, 2 ≤ lineTotal line z g →
      a g (lineTotal line z g) * a g (lineTotal line z g-2) ≤ a g (lineTotal line z g-1)^2)
    (hblc : ∀ i, 2 ≤ z i → b i (z i) * b i (z i-2) ≤ b i (z i-1)^2) :
    OnePositiveDirection (integerRemovalMatrix (productWeight line a b) z).toBilin' := by
  rw [integerRemoval_product_matrix]
  have hs := lineUnaryRemoval_onePositive line
    (fun g => a g (lineTotal line z g))
    (fun g => a g (lineTotal line z g-1))
    (fun g => if 2 ≤ lineTotal line z g then a g (lineTotal line z g-2) else 0)
    (fun i => b i (z i)) (fun i => b i (z i-1))
    (fun i => if 2 ≤ z i then b i (z i-2) else 0)
    (fun g => ha g _ le_rfl) (fun g => ha g _ (Nat.sub_le _ _))
    (fun g => by split_ifs; exact (ha g _ (Nat.sub_le _ _)).le; exact le_rfl)
    (fun i => hb i _ le_rfl) (fun i => hb i _ (Nat.sub_le _ _))
    (fun g => by split_ifs with h; exact halc g h; simp [sq_nonneg])
    (fun i => by split_ifs with h; exact hblc i h; simp [sq_nonneg])
  intro x hx y hxy
  rw [scaledMatrix_form] at hx hxy ⊢
  exact hs _ hx _ hxy

end ContingencyTables.ProductIntegerSignature

end OAI
