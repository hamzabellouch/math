import OAI.NumberTheory.JointDickman.Amplification.SingularSeriesTail

namespace OAI

/-! # Evaluating the two projected endpoint factors together -/

namespace JointDickman
open Finset
open scoped ComplexConjugate ArithmeticFunction.Moebius

theorem ramanujanSum_neg {q : ℕ} [NeZero q] (h : ZMod q) :
    ramanujanSum q (-h) = conj (ramanujanSum q h) := by
  unfold ramanujanSum
  rw [map_sum]
  apply sum_congr rfl
  intro r _
  rw [stdAddChar_conj,neg_mul]

theorem normalizedRamanujan_pair {q : ℕ} [NeZero q] (h : ZMod q) (A B : ℂ) :
    ((ramanujanSum q h/(q.totient : ℂ))*A)*
      ((ramanujanSum q (-h)/(q.totient : ℂ))*B) =
      ((‖ramanujanSum q h‖^2/(q.totient : ℝ)^2 : ℝ) : ℂ)*(A*B) := by
  rw [ramanujanSum_neg]
  have he : (ramanujanSum q h/(q.totient : ℂ))*
      (conj (ramanujanSum q h)/(q.totient : ℂ)) =
      ((‖ramanujanSum q h‖^2/(q.totient : ℝ)^2 : ℝ) : ℂ) := by
    rw [div_mul_div_comm,Complex.mul_conj']
    push_cast
    ring
  calc
    _ = ((ramanujanSum q h/(q.totient : ℂ))*
        (conj (ramanujanSum q h)/(q.totient : ℂ)))*(A*B) := by ring
    _ = _ := by rw [he]

theorem projected_residue_kernel {j q : ℕ} [NeZero j] [NeZero q] [NeZero (j*q)]
    (A B : ℂ) :
    ((μ q : ℂ)/(q.totient : ℂ))*
      (∑ h : ZMod (j*q), if h.val.Coprime q then
        ((ramanujanSum (j*q) h/((j*q).totient : ℂ))*A)*
          ((ramanujanSum (j*q) (-h)/((j*q).totient : ℂ))*B) else 0) =
      (((j : ℝ)/j.totient*singularSeriesCoefficient j q : ℝ) : ℂ)*(A*B) := by
  classical
  have he (h : ZMod (j*q)) :
      (if h.val.Coprime q then
        ((ramanujanSum (j*q) h/((j*q).totient : ℂ))*A)*
          ((ramanujanSum (j*q) (-h)/((j*q).totient : ℂ))*B) else 0) =
      ((if h.val.Coprime q then
        ‖ramanujanSum (j*q) h‖^2/((j*q).totient : ℝ)^2 else 0 : ℝ) : ℂ)*(A*B) := by
    split_ifs
    · exact normalizedRamanujan_pair h A B
    · simp
  simp_rw [he]
  rw [← sum_mul,← Complex.ofReal_sum]
  have hw := congrArg (fun x : ℝ => (x : ℂ))
    (weighted_ramanujan_residue_factor (j := j) (q := q))
  push_cast at hw
  rw [← mul_assoc]
  push_cast
  rw [hw]

end JointDickman

end OAI
