import OAI.Probability.InvariantIsing.Arrays.PerturbationWeights

namespace OAI

/-! A concrete complete enumeration of the spectral/tree monomials with linear degree cap. -/

noncomputable section

open scoped BigOperators

namespace InvariantIsing

def multidegreeDecode : (m : ℕ) → ℕ → Fin m → ℕ
  | 0, _ => Fin.elim0
  | m + 1, j => Fin.cases (Nat.unpair j).1 (multidegreeDecode m (Nat.unpair j).2)

def multidegreeEncode : (m : ℕ) → (Fin m → ℕ) → ℕ
  | 0, _ => 0
  | m + 1, d => Nat.pair (d 0) (multidegreeEncode m (Fin.tail d))

lemma multidegreeDecode_encode (m : ℕ) (d : Fin m → ℕ) :
    multidegreeDecode m (multidegreeEncode m d) = d := by
  induction m with
  | zero => exact Subsingleton.elim _ _
  | succ m ih =>
    funext i
    induction i using Fin.cases with
    | zero => simp only [multidegreeDecode, multidegreeEncode, Nat.unpair_pair, Fin.cases_zero]
    | succ i =>
      simpa only [multidegreeDecode, multidegreeEncode, Nat.unpair_pair, Fin.cases_succ,
        Fin.tail] using congrFun (ih (Fin.tail d)) i

lemma multidegreeDecode_sum_le (m j : ℕ) :
    (∑ i, multidegreeDecode m j i) ≤ j := by
  induction m generalizing j with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_succ]
    simp only [multidegreeDecode, Fin.cases_zero, Fin.cases_succ]
    exact (Nat.add_le_add_left (ih (Nat.unpair j).2) _).trans (Nat.unpair_add_le j)

/-- First `m` coordinates are spectral degrees; the final coordinate is
the tree degree. The constant kernel can be retained harmlessly. -/
def enumeratedSpectralDegree (m j : ℕ) (a : Fin m) : ℕ :=
  multidegreeDecode (m + 1) (j + 1) a.castSucc

def enumeratedTreeDegree (m j : ℕ) : ℕ :=
  multidegreeDecode (m + 1) (j + 1) (Fin.last m)

lemma enumeratedMonomial_degree_le (m j : ℕ) :
    (∑ a, enumeratedSpectralDegree m j a) + enumeratedTreeDegree m j ≤ j + 1 := by
  simpa only [Fin.sum_univ_castSucc, enumeratedSpectralDegree, enumeratedTreeDegree] using
    multidegreeDecode_sum_le (m + 1) (j + 1)

lemma enumeratedSpectralDegree_real_sum_le (m j : ℕ) :
    (∑ a, (enumeratedSpectralDegree m j a : ℝ)) ≤ (j : ℝ) + 1 := by
  have h := (Nat.le_add_right (∑ a, enumeratedSpectralDegree m j a)
    (enumeratedTreeDegree m j)).trans (enumeratedMonomial_degree_le m j)
  exact_mod_cast h

/-- Every nonconstant joint spectral/tree monomial occurs at a fixed
finite index, hence eventually occurs in the truncation through `N`. -/
theorem enumeratedMonomial_surjective (m : ℕ) (d : Fin m → ℕ) (r : ℕ)
    (h : 1 ≤ (∑ a, d a) + r) :
    ∃ j, (∀ a, enumeratedSpectralDegree m j a = d a) ∧ enumeratedTreeDegree m j = r := by
  let v : Fin (m + 1) → ℕ := Fin.lastCases r d
  let c := multidegreeEncode (m + 1) v
  have hc : 1 ≤ c := by
    have hs := multidegreeDecode_sum_le (m + 1) c
    rw [multidegreeDecode_encode] at hs
    rw [Fin.sum_univ_castSucc] at hs
    simp only [v, Fin.lastCases_castSucc, Fin.lastCases_last] at hs
    exact h.trans hs
  refine ⟨c - 1, ?_, ?_⟩
  · intro a
    have he := congrFun (multidegreeDecode_encode (m + 1) v) a.castSucc
    simpa only [enumeratedSpectralDegree, Nat.sub_add_cancel hc, v, Fin.lastCases_castSucc] using he
  · have he := congrFun (multidegreeDecode_encode (m + 1) v) (Fin.last m)
    simpa only [enumeratedTreeDegree, Nat.sub_add_cancel hc, v, Fin.lastCases_last] using he

end InvariantIsing

end

end OAI
