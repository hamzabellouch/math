import OAI.Combinatorics.MatchingPSD.GoodCells

namespace OAI

universe u_1

namespace PerfectMatchingPSD
open Matrix
open scoped BigOperators MatrixOrder
attribute [local instance] Classical.propDecidable

lemma domination_decoder {R : Type u_1} [Fintype R] [DecidableEq R] {q : ℕ}
    (Q : (Fin q → Bool) → Matrix R R ℝ)
    (T : Fin q → Bool → Matrix R R ℝ) (P E : Fin q → Matrix R R ℝ)
    (S : Matrix R R ℝ)
    (hQ : ∀ y, (Q y).PosSemidef) (hT : ∀ i b, (T i b).PosSemidef)
    (hP : ∀ i, (P i).PosSemidef) (hE : ∀ i, (E i).PosSemidef) (hS : S.PosSemidef)
    (hdom : ∀ i, T i false + T i true ≤ S+(2:ℝ) • P i+E i)
    (hzero : ∀ y i, (Q y*P i).trace=0) (hstar : ∀ y, (Q y*S).trace=2)
    (hbit : ∀ y i, (Q y*T i (y i)).trace=2)
    {m e δ : ℝ} (hδ : 0 < δ) (hm : ∀ y, (Q y).trace ≤ m)
    (he : ∀ y i, (Q y*E i).trace ≤ e)
    (hε : 0 ≤ (q:ℝ)*e+δ*m)
    (hsmall : (q:ℝ)*Real.sqrt ((q:ℝ)*e+δ*m) ≤ 1/4) :
    (2:ℝ)^q/2 ≤ Fintype.card R := by
  let F := fun i => (2:ℝ) • P i+E i
  have hF (i : Fin q) : (F i).PosSemidef := (hP i).smul (by norm_num) |>.add (hE i)
  let D := S+(∑ i, F i)+δ • (1 : Matrix R R ℝ)
  have hsum : (∑ i, F i).PosSemidef := matrix_sum_psd _ _ (fun i _ => hF i)
  have hdelt : (δ • (1 : Matrix R R ℝ)).PosDef := Matrix.PosDef.one.smul hδ
  have hD : D.PosDef := by
    simpa only [D, add_comm] using hdelt.add_posSemidef (hS.add hsum)
  have hleS : S ≤ D := by
    have he := add_nonneg hsum.nonneg hdelt.posSemidef.nonneg
    dsimp [D]
    simpa only [add_assoc] using le_add_of_nonneg_right he
  have hdomD (i : Fin q) : T i false+T i true ≤ D := by
    apply (hdom i).trans
    have hi : F i ≤ ∑ j, F j := Finset.single_le_sum (fun j _ => (hF j).nonneg) (Finset.mem_univ i)
    calc
      S+(2:ℝ) • P i+E i = S+F i := by dsimp [F]; abel
      _ ≤ S+(∑ j, F j) := by simpa only [add_comm] using add_le_add_left hi S
      _ ≤ D := le_add_of_nonneg_right hdelt.posSemidef.nonneg
  have htr (y : Fin q → Bool) : 2 ≤ (Q y*D).trace ∧ (Q y*D).trace ≤ 2+((q:ℝ)*e+δ*m) := by
    constructor
    · rw [← hstar y]
      exact trace_mul_le_of_le (hQ y) hleS
    · dsimp [D]
      rw [mul_add, mul_add, Matrix.trace_add, Matrix.trace_add, hstar,
        Finset.mul_sum, Matrix.trace_sum, mul_smul_comm, Matrix.trace_smul, mul_one]
      have hsumtr : (∑ i, (Q y*F i).trace) ≤ (q:ℝ)*e := by
        have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => he y i)
        have hFi (i : Fin q) : (Q y*F i).trace = (Q y*E i).trace := by
          simp only [F, mul_add, Matrix.trace_add, mul_smul_comm, Matrix.trace_smul,
            hzero, smul_zero, zero_add]
        simpa only [hFi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hh
      have hδm := mul_le_mul_of_nonneg_left (hm y) hδ.le
      change _ + δ*(Q y).trace ≤ _
      linarith
  obtain ⟨ρ,H,hρ,htρ,hH,hpair,hbit'⟩ := states_of_domination Q T D hD hQ hT hdomD
    ((q:ℝ)*e+δ*m) hε htr hbit
  exact nearly_perfect_bit_tests ρ H hρ htρ hH hpair _ hε hsmall hbit'

end PerfectMatchingPSD

end OAI
