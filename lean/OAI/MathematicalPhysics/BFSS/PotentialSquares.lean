import Mathlib
import OAI.MathematicalPhysics.BFSS.PotentialBasis
import OAI.MathematicalPhysics.BFSS.ColorMatrices

namespace OAI

/-! Shifted potential squares, coercivity and odd gamma traces. -/

namespace BFSSGamma
noncomputable section
open Matrix Finset

lemma shiftedPair_squares (h m : ℝ) (b : SpatialPair → ℝ) (x : Space → ℝ) :
    (∑ p, (shiftedPair h m b x p)^2) =
      (h*b pair01 - 2*m*x 2)^2 + (h*b pair12 - 2*m*x 0)^2 +
      (h*b pair02 + 2*m*x 1)^2 + h^2 * ∑ p, if 3 ≤ p.1.2.val then (b p)^2 else 0 := by
  have he (p : SpatialPair) : (shiftedPair h m b x p)^2 =
      (if p = pair01 then (h*b pair01 - 2*m*x 2)^2 else 0) +
      (if p = pair12 then (h*b pair12 - 2*m*x 0)^2 else 0) +
      (if p = pair02 then (h*b pair02 + 2*m*x 1)^2 else 0) +
      h^2 * (if 3 ≤ p.1.2.val then (b p)^2 else 0) := by
    by_cases h01 : p = pair01
    · subst p
      norm_num [shiftedPair, pair01, pair02, pair12, Fin.ext_iff]
      ring
    by_cases h02 : p = pair02
    · subst p
      norm_num [shiftedPair, pair01, pair02, pair12, Fin.ext_iff]
      ring
    by_cases h12 : p = pair12
    · subst p
      norm_num [shiftedPair, pair01, pair02, pair12, Fin.ext_iff]
      ring
    have e01 : p.1 ≠ (0,1) := fun h => h01 (Subtype.ext h)
    have e02 : p.1 ≠ (0,2) := fun h => h02 (Subtype.ext h)
    have e12 : p.1 ≠ (1,2) := fun h => h12 (Subtype.ext h)
    have ht : 3 ≤ p.1.2.val := by
      have hlt := p.2
      have hn01 : ¬(p.1.1.val = 0 ∧ p.1.2.val = 1) := by
        rintro ⟨h1,h2⟩
        exact e01 (Prod.ext (Fin.ext h1) (Fin.ext h2))
      have hn02 : ¬(p.1.1.val = 0 ∧ p.1.2.val = 2) := by
        rintro ⟨h1,h2⟩
        exact e02 (Prod.ext (Fin.ext h1) (Fin.ext h2))
      have hn12 : ¬(p.1.1.val = 1 ∧ p.1.2.val = 2) := by
        rintro ⟨h1,h2⟩
        exact e12 (Prod.ext (Fin.ext h1) (Fin.ext h2))
      change p.1.1.val < p.1.2.val at hlt
      omega
    simp only [shiftedPair, ite_eq_right e01, ite_eq_right e02, ite_eq_right e12, h01, h02, h12,
      ite_false, ht, ite_true, add_zero]
    ring
  simp only [he, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    ← Finset.mul_sum]

end
end BFSSGamma

namespace BFSSGamma
noncomputable section
open Finset

lemma spatialTail_sum (f : Space × Space → ℝ) :
    (∑ p : SpatialPair, if 3 ≤ p.1.2.val then f p.1 else 0) =
      ∑ i : Space, ∑ j : Space, if i < j ∧ 3 ≤ j.val then f (i,j) else 0 := by
  calc
    _ = ∑ p ∈ univ.filter (fun p : Space × Space => p.1 < p.2),
        (if 3 ≤ p.2.val then f p else 0) :=
      (Finset.sum_subtype _ (by intro p; simp)
        (fun p : Space × Space => if 3 ≤ p.2.val then f p else 0)).symm
    _ = _ := by
      simp only [Finset.sum_filter, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      split_ifs <;> simp_all

lemma tailIndex_sum (f : Space → ℝ) :
    (∑ d : TailIndex, f d.1) = ∑ i : Space, if 3 ≤ i.val then f i else 0 := by
  calc
    _ = ∑ i ∈ univ.filter (fun i : Space => 3 ≤ i), f i :=
      (Finset.sum_subtype _ (by intro i; simp) f).symm
    _ = _ := by simp only [Finset.sum_filter, Fin.le_iff_val_le_val]; rfl

end
end BFSSGamma

namespace BFSSQuantum
noncomputable section
open Matrix Finset
namespace AlgebraData
variable {N : ℕ} (M : AlgebraData N)

lemma deformedBosonicPotential_matrix (h m : ℝ) (x : Boson N) :
    M.deformedBosonicPotential h m x = BFSS.massivePotential h m (M.matrixConfiguration x) := by
  have hpair (A : ColorIndex N) : (∑ p : SpatialPair,
      (BFSSGamma.shiftedPair h m (fun p => M.coordinateBracket x p A) (fun i => x (i,A)) p)^2) =
      (h*M.coordinateBracketAll x 0 1 A - 2*m*x (2,A))^2 +
      (h*M.coordinateBracketAll x 1 2 A - 2*m*x (0,A))^2 +
      (h*M.coordinateBracketAll x 2 0 A - 2*m*x (1,A))^2 +
      h^2 * ∑ i : SpaceIndex, ∑ j : SpaceIndex,
        if i < j ∧ 3 ≤ j.val then (M.coordinateBracketAll x i j A)^2 else 0 := by
    rw [BFSSGamma.shiftedPair_squares]
    rw [show (∑ p : SpatialPair, if 3 ≤ p.1.2.val then (M.coordinateBracket x p A)^2 else 0) =
      ∑ i : SpaceIndex, ∑ j : SpaceIndex,
        if i < j ∧ 3 ≤ j.val then (M.coordinateBracketAll x i j A)^2 else 0 from
      BFSSGamma.spatialTail_sum (fun p => (M.coordinateBracketAll x p.1 p.2 A)^2)]
    simp only [coordinateBracket, BFSSGamma.pair01, BFSSGamma.pair02, BFSSGamma.pair12]
    rw [M.coordinateBracketAll_skew x 0 2 A]
    dsimp only [coordinateBracketAll]
    ring
  have htail (A : ColorIndex N) : (∑ d : TailIndex, (m*x (d.1,A))^2) =
      m^2 * ∑ i : SpaceIndex, if 3 ≤ i.val then (x (i,A))^2 else 0 := by
    rw [BFSSGamma.tailIndex_sum (fun i => (m*x (i,A))^2)]
    simp_rw [mul_pow]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> simp
  rw [deformedBosonicPotential]
  simp only [hpair, htail, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [BFSS.massivePotential, M.coordinate_shifted_norm, M.coordinate_shifted_norm,
    M.coordinate_shifted_norm]
  have hp : (∑ A, ∑ i : SpaceIndex, ∑ j : SpaceIndex,
      if i < j ∧ 3 ≤ j.val then (M.coordinateBracketAll x i j A)^2 else 0) =
      ∑ i : SpaceIndex, ∑ j : SpaceIndex, if i < j ∧ 3 ≤ j.val then
      BFSS.hsNormSq (BFSS.realBracket (M.matrixConfiguration x i).val (M.matrixConfiguration x j).val)
      else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> simp [M.coordinate_bracket_norm]
  have ht : (∑ A, ∑ i : SpaceIndex, if 3 ≤ i.val then (x (i,A))^2 else 0) =
      ∑ i : SpaceIndex, if 3 ≤ i.val then BFSS.hsNormSq (M.matrixConfiguration x i).val else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> simp [matrixConfiguration, M.colorCombination_normSq]
  rw [hp, ht]
  ring

theorem deformedBosonicPotential_coercive (hN : 2 ≤ N) :
    ∃ c : ℝ, 0 < c ∧ ∃ R : ℝ, ∀ x : Boson N,
      R ≤ ‖x‖ → c * ‖x‖^2 ≤ M.deformedBosonicPotential 1 1 x := by
  obtain ⟨c,hc,R,hR⟩ := BFSS.massive_coercivity N hN
  refine ⟨c,hc,R,?_⟩
  intro x hx
  have hs := hR (M.matrixConfiguration x)
  rw [M.matrixConfiguration_norm, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg x)] at hs
  simpa only [M.deformedBosonicPotential_matrix] using hs hx

end AlgebraData
end
end BFSSQuantum

namespace BFSSGamma
noncomputable section
open Matrix Finset
variable (G : Space → Mat)
variable (hG : ∀ i j, G i * G j + G j * G i = (if i = j then 2 else 0) • (1 : Mat))
variable (hSym : ∀ i, (G i).IsSymm)
include hG

lemma trace_list_odd (l : List Space) (hl : l.length < 9) (ho : Odd l.length) :
    Matrix.trace (l.map G).prod = 0 := by
  have hc : l.toFinset.card < (univ : Finset Space).card := by
    calc
      l.toFinset.card ≤ l.length := List.toFinset_card_le l
      _ < 9 := hl
      _ = (univ : Finset Space).card := by simp [Space]
  obtain ⟨q,hqu,hq⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  have hn : q ∉ l := by simpa only [List.mem_toFinset] using hq
  have signs (l : List Space) (hn : q ∉ l) :
      (l.map (singleSign q)).prod = (-1 : ℝ)^l.length := by
    induction l with
    | nil => simp
    | cons a l ih =>
      have ha : q ≠ a := fun h => hn (by simp [h])
      have hn' : q ∉ l := fun h => hn (List.mem_cons_of_mem a h)
      simp only [List.map_cons, List.prod_cons, singleSign, ite_eq_right ha,
        ih hn', List.length_cons, pow_succ]
      ring
  have ht := trace_conj G hG q (l.map G).prod
  rw [list_conj G hG, signs l hn, ho.neg_one_pow, neg_one_smul, Matrix.trace_neg] at ht
  linarith

include hSym

lemma gamma_pair_trace_zero (i : Space) (p : SpatialPair) :
    Matrix.trace ((G i).transpose * pairGamma G p) = 0 := by
  rw [(hSym i).eq]
  have ht := trace_list_odd G hG [i,p.1.1,p.1.2] (by simp) (by norm_num [List.length_cons, List.length_nil])
  simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    pairGamma] using ht

lemma gamma_mass_trace_zero (i j : Space) :
    Matrix.trace ((G i).transpose * (G j * massT G)) = 0 := by
  rw [(hSym i).eq]
  have ht := trace_list_odd G hG [i,j,0,1,2] (by simp) (by norm_num [List.length_cons, List.length_nil])
  simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    massT, Matrix.mul_assoc] using ht

lemma gamma_bracketMass_trace_zero (h m : ℝ) (b : SpatialPair → ℝ)
    (x : Space → ℝ) (i : Space) :
    Matrix.trace ((G i).transpose * bracketMassMatrix G h m b x) = 0 := by
  simp only [bracketMassMatrix, Matrix.mul_add, mul_smul_comm, Matrix.mul_sum,
    Matrix.trace_add, Matrix.trace_sum, Matrix.trace_smul,
    gamma_pair_trace_zero G hG hSym, gamma_mass_trace_zero G hG hSym,
    smul_zero, Finset.sum_const_zero, add_zero]

end
end BFSSGamma

end OAI
