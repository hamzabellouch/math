import OAI.Algebra.OddKaplansky.GraphNumerics

namespace OAI

universe contextUniverse1

universe portUniverse1

section

namespace OddKaplansky.SourceFit
noncomputable section
open scoped Classical BigOperators
open SourceGraph
variable {K : Type portUniverse1} [Field K]
variable (p : ℕ) [sectionInstance8 : Fact p.Prime] [CharP K p] (hp : 1200 < p)

abbrev Slot := {T : Finset (Fin 1200) // T.card ≤ 400}
def polynomial (j : Vertex) : MvPolynomial (Fin 1200) K :=
  GraphPolynomial.polynomial j.val 600 200 600

def alpha (i : Vertex) (T : Slot) : K := if T.val ⊆ i.val then 1 else 0
def beta (j : Vertex) (T : Slot) : K := BooleanPolynomial.coefficient (polynomial j) T.val

def fitting (i j : Vertex) : K := ∑ T : Slot, alpha i T * beta j T

lemma fitting_eq (i j : Vertex) : fitting (K := K) i j =
    ∏ k ∈ Finset.Ico (200 : ℕ) 600, (((i.val ∩ j.val).card : K) - (k : K)) / ((600-k : ℕ) : K) := by
  simp only [fitting, alpha, beta]
  have hdeg : (polynomial (K := K) j).totalDegree ≤ 400 := GraphPolynomial.degree_polynomial _ _ _ _
  trans MvPolynomial.eval (BooleanPolynomial.value i.val) (polynomial (K := K) j)
  · exact (BooleanPolynomial.evaluate (polynomial j) i.val 400 hdeg).symm
  rw [polynomial, GraphPolynomial.eval_polynomial]
  simp only [Finset.inter_comm]

lemma denominator
    {K : Type contextUniverse1}
    [contextInstance1 : Field.{contextUniverse1} K]
    (p : Nat)
    [Fact (Nat.Prime p)]
    [@CharP.{contextUniverse1} K
  (@AddGroupWithOne.toAddMonoidWithOne.{contextUniverse1} K
    (@Ring.toAddGroupWithOne.{contextUniverse1} K (@DivisionRing.toRing.{contextUniverse1} K (@Field.toDivisionRing.{contextUniverse1} K contextInstance1))))
  p]
    (hp : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1200) (instOfNatNat (nat_lit 1200))) p) (k : ℕ) (hk : k ∈ Finset.Ico 200 600) : ((600-k : ℕ) : K) ≠ 0 := by
  have hk₁ : 0 < 600-k := by have := Finset.mem_Ico.mp hk; omega
  have hk₂ : 600-k < p := by omega
  exact (CharP.cast_eq_zero_iff K p (600-k)).not.mpr (Nat.not_dvd_of_pos_of_lt hk₁ hk₂)

include hp in
lemma fitting_diagonal (i : Vertex) : fitting (K := K) i i = 1 := by
  have hdeg : (polynomial (K := K) i).totalDegree ≤ 400 := GraphPolynomial.degree_polynomial _ _ _ _
  simp only [fitting, alpha, beta]
  trans MvPolynomial.eval (BooleanPolynomial.value i.val) (polynomial (K := K) i)
  · exact (BooleanPolynomial.evaluate (polynomial i) i.val 400 hdeg).symm
  exact GraphPolynomial.diagonal i.val 600 200 600 i.property (by omega) (denominator p hp)

lemma intersection_lt (i j : Vertex) (hij : i ≠ j) : (i.val ∩ j.val).card < 600 := by
  have hle : (i.val ∩ j.val).card ≤ 600 := by
    rw [← i.property]
    exact Finset.card_le_card Finset.inter_subset_left
  by_contra hn
  have hecard : (i.val ∩ j.val).card = i.val.card := by rw [i.property]; omega
  have he : i.val ∩ j.val = i.val := Finset.eq_of_subset_of_card_le Finset.inter_subset_left hecard.ge
  have hij' : i.val ⊆ j.val := by rw [← he]; exact Finset.inter_subset_right
  exact hij (Vertex.ext (Finset.eq_of_subset_of_card_le hij' (by rw [i.property,j.property])))

lemma fitting_nonedge (i j : Vertex) (hij : i ≠ j) (hn : ¬ graph.Adj i j) :
    fitting (K := K) i j = 0 := by
  have hlo : 200 ≤ (j.val ∩ i.val).card := by
    rw [Finset.inter_comm]
    by_contra hh
    apply hn
    exact ⟨hij,by omega⟩
  have hhi : (j.val ∩ i.val).card < 600 := intersection_lt j i hij.symm
  have hdeg : (polynomial (K := K) j).totalDegree ≤ 400 := GraphPolynomial.degree_polynomial _ _ _ _
  simp only [fitting, alpha, beta]
  trans MvPolynomial.eval (BooleanPolynomial.value i.val) (polynomial (K := K) j)
  · exact (BooleanPolynomial.evaluate (polynomial j) i.val 400 hdeg).symm
  exact GraphPolynomial.vanishes j.val i.val 600 200 600 hlo hhi

lemma card_slots : Fintype.card Slot = ∑ k ∈ Finset.range 401, Nat.choose 1200 k := by
  have he := GraphNumerics.card_small_sets (Fin 1200) 400
  simpa only [Fintype.card_fin] using he

lemma ratio_bound : 100 * Fintype.card Slot < sourceM := by
  rw [card_slots]
  unfold sourceM
  exact GraphNumerics.source_ratio_bound

end
end OddKaplansky.SourceFit

end

end OAI
