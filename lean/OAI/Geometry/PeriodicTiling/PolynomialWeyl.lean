import OAI.Geometry.PeriodicTiling.CircleWeylCriterion
import OAI.Geometry.PeriodicTiling.ScalarVanDerCorput
import OAI.Geometry.PeriodicTiling.PolynomialShiftDifference
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace OAI

noncomputable section

namespace PeriodicTilingThree

open Filter Polynomial
open scoped Topology ComplexConjugate

def scalarPhase (x : ℝ) : ℂ :=
  AddCircle.toCircle (x : UnitAddCircle)

@[simp] theorem scalarPhase_zero : scalarPhase 0 = 1 := by
  simp only [scalarPhase, AddCircle.coe_zero, AddCircle.toCircle_zero, Circle.coe_one]

@[simp] theorem norm_scalarPhase (x : ℝ) : ‖scalarPhase x‖ = 1 :=
  Circle.norm_coe _

theorem scalarPhase_add (x y : ℝ) :
    scalarPhase (x + y) = scalarPhase x * scalarPhase y := by
  simp only [scalarPhase, AddCircle.coe_add, AddCircle.toCircle_add, Circle.coe_mul]

theorem scalarPhase_nat_mul (n : ℕ) (x : ℝ) :
    scalarPhase ((n : ℝ) * x) = scalarPhase x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ, add_mul, one_mul, scalarPhase_add, ih, pow_succ]

theorem scalarPhase_sub (x y : ℝ) :
    scalarPhase (x - y) = scalarPhase x * conj (scalarPhase y) := by
  have hy : scalarPhase y ≠ 0 := Circle.coe_ne_zero _
  apply mul_right_cancel₀ hy
  rw [← scalarPhase_add, sub_add_cancel, mul_assoc, Complex.conj_mul', norm_scalarPhase]
  norm_num

theorem scalarPhase_ne_one_of_irrational {x : ℝ} (hx : Irrational x) :
    scalarPhase x ≠ 1 := by
  intro h
  have he : AddCircle.toCircle (x : UnitAddCircle) = AddCircle.toCircle (0 : UnitAddCircle) := by
    apply Subtype.ext
    simpa only [AddCircle.toCircle_zero, Circle.coe_one, scalarPhase] using h
  have hz : (x : UnitAddCircle) = 0 :=
    AddCircle.injective_toCircle (by norm_num : (1 : ℝ) ≠ 0) he
  obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hz
  exact hx.ne_int m (by simpa only [zsmul_eq_mul, mul_one] using hm.symm)

theorem fourier_eq_scalarPhase (k : ℤ) (x : ℝ) :
    fourier k (x : UnitAddCircle) = scalarPhase ((k : ℝ) * x) := by
  simp only [fourier_apply, scalarPhase, ← AddCircle.coe_zsmul, zsmul_eq_mul]

private theorem eval_degree_one (P : Polynomial ℝ) (hP : P.natDegree = 1) (x : ℝ) :
    P.eval x = P.coeff 0 + P.leadingCoeff * x := by
  have hc : P.coeff 1 = P.leadingCoeff := by
    simpa only [hP] using P.coeff_natDegree
  rw [Polynomial.eval_eq_sum_range' (by omega : P.natDegree < 2)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero,
    mul_one, pow_one, hc]

theorem polynomial_phase_average_tendsto_zero (P : Polynomial ℝ)
    (hP : 0 < P.natDegree) (hI : Irrational P.leadingCoeff) :
    Tendsto (complexAverage (fun n : ℕ => scalarPhase (P.eval (n : ℝ))))
      atTop (𝓝 0) := by
  have hall : ∀ d : ℕ, ∀ Q : Polynomial ℝ, Q.natDegree = d →
      0 < d → Irrational Q.leadingCoeff →
      Tendsto (complexAverage (fun n : ℕ => scalarPhase (Q.eval (n : ℝ))))
        atTop (𝓝 0) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro Q hQ hd hI
      by_cases hd1 : d = 1
      · have heval : ∀ n : ℕ, scalarPhase (Q.eval (n : ℝ)) =
            scalarPhase (Q.coeff 0) * scalarPhase Q.leadingCoeff ^ n := by
          intro n
          rw [eval_degree_one Q (hQ.trans hd1), scalarPhase_add,
            mul_comm Q.leadingCoeff (n : ℝ), scalarPhase_nat_mul]
        simpa only [heval] using complexAverage_const_mul_geometric_tendsto
          (scalarPhase (Q.coeff 0)) (scalarPhase Q.leadingCoeff)
          (norm_scalarPhase _) (scalarPhase_ne_one_of_irrational hI)
      · apply complexAverage_vanDerCorput
        · intro n
          exact (norm_scalarPhase _).le
        · intro h k hhk
          let D := Polynomial.taylor (h : ℝ) Q - Polynomial.taylor (k : ℝ) Q
          obtain ⟨hDdeg, hDirr⟩ :=
            polynomial_shift_difference_degree_irrational Q (by omega) hI h k hhk
          have hDpos : 0 < D.natDegree := by dsimp [D]; rw [hDdeg]; omega
          have hDlt : D.natDegree < d := by dsimp [D]; rw [hDdeg, hQ]; omega
          have hDlim := ih D.natDegree hDlt D rfl hDpos hDirr
          have hseq :
              (fun n : ℕ => scalarPhase (Q.eval ((n + h : ℕ) : ℝ)) *
                conj (scalarPhase (Q.eval ((n + k : ℕ) : ℝ)))) =
              (fun n : ℕ => scalarPhase (D.eval (n : ℝ))) := by
            funext n
            rw [← scalarPhase_sub]
            congr 1
            simp only [D, Polynomial.eval_sub, Polynomial.taylor_eval, Nat.cast_add]
          rw [hseq]
          exact hDlim
  exact hall P.natDegree P rfl hP hI

theorem denseRange_circlePolynomial_of_irrational_leadingCoeff (P : Polynomial ℝ)
    (hP : 0 < P.natDegree) (hI : Irrational P.leadingCoeff) :
    DenseRange (fun n : ℕ => ((P.eval (n : ℝ) : ℝ) : UnitAddCircle)) := by
  apply denseRange_of_circleFourierCancellation
  intro k hk
  let Q : Polynomial ℝ := Polynomial.C (k : ℝ) * P
  have hkreal : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
  have hQdeg : Q.natDegree = P.natDegree := Polynomial.natDegree_C_mul hkreal
  have hQirr : Irrational Q.leadingCoeff := by
    simpa only [Q, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
      using hI.intCast_mul hk
  have hQlim := polynomial_phase_average_tendsto_zero Q (hQdeg.symm ▸ hP) hQirr
  have hseq :
      (fun n : ℕ => fourier k (((P.eval (n : ℝ) : ℝ) : UnitAddCircle))) =
      (fun n : ℕ => scalarPhase (Q.eval (n : ℝ))) := by
    funext n
    rw [fourier_eq_scalarPhase]
    simp only [Q, Polynomial.eval_mul, Polynomial.eval_C]
  change Tendsto (complexAverage
    (fun n : ℕ => fourier k (((P.eval (n : ℝ) : ℝ) : UnitAddCircle)))) atTop (𝓝 0)
  rw [hseq]
  exact hQlim

end PeriodicTilingThree

end

end OAI
