import OAI.NumberTheory.Ostmann.Arithmetic.SignedRightJacobiNonsquare
import OAI.NumberTheory.Ostmann.Dirichlet.SplitPrimeMassManuscript

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

def rootSplitPrimeMass (n : ℤ) (m : ℕ) (Q : ℝ) : ℝ :=
  ∑ p ∈ (⌊Q⌋₊).primesLE.filter
    (fun p => ¬p ∣ 4*m*n.natAbs ∧ jacobiSym n p=1), Real.log p/(p:ℝ)

theorem rootSplitPrimeMass_eq_character (n : ℤ) (hn : n≠0) (m : ℕ) (Q : ℝ) :
    rootSplitPrimeMass n m Q =
      Dirichlet.splitPrimeMass (Arithmetic.signedRightJacobiCharacter n hn)
        (4*m*n.natAbs) Q := by
  classical
  unfold rootSplitPrimeMass Dirichlet.splitPrimeMass Dirichlet.splitPrimeSupport
  congr 1
  ext p
  simp only [Finset.mem_filter]
  constructor <;> rintro ⟨hp,hd,hj⟩
  · refine ⟨hp,hd,?_⟩
    have hp2 : p≠2 := by
      intro he
      subst p
      exact hd (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (by norm_num : 2∣4) m) n.natAbs)
    rw [Arithmetic.signedRightJacobiCharacter_prime n hn (Nat.mem_primesLE.mp hp).2 hp2,hj]
    norm_num
  · refine ⟨hp,hd,?_⟩
    have hp2 : p≠2 := by
      intro he
      subst p
      exact hd (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (by norm_num : 2∣4) m) n.natAbs)
    rw [Arithmetic.signedRightJacobiCharacter_prime n hn (Nat.mem_primesLE.mp hp).2 hp2] at hj
    exact_mod_cast hj

theorem jacobiSym_square_prime {n : ℤ} (hs : IsSquare n) {p : ℕ}
    (hp : p.Prime) (hd : ¬p∣n.natAbs) : jacobiSym n p=1 := by
  obtain ⟨a,rfl⟩ := hs.exists_sq
  have ha : ¬p∣a.natAbs := by
    intro ha
    apply hd
    simpa only [Int.natAbs_pow] using (dvd_pow ha (by norm_num : 2≠0))
  have hc := (hp.coprime_iff_not_dvd.mpr ha).symm.gcd_eq_one
  apply jacobiSym.sq_one'
  simpa only [Int.gcd,Int.natAbs_natCast] using hc

theorem rootSplitPrimeMass_square (n : ℤ) (hs : IsSquare n) (m : ℕ) (Q : ℝ) :
    rootSplitPrimeMass n m Q =
      ∑ p ∈ (⌊Q⌋₊).primesLE.filter (fun p => ¬p∣4*m*n.natAbs), Real.log p/(p:ℝ) := by
  classical
  unfold rootSplitPrimeMass
  congr 1
  ext p
  simp only [Finset.mem_filter]
  constructor
  · tauto
  · rintro ⟨hp,hd⟩
    refine ⟨hp,hd,jacobiSym_square_prime hs (Nat.mem_primesLE.mp hp).2 ?_⟩
    intro hn
    exact hd (dvd_mul_of_dvd_right hn (4*m))

end Ostmann.QuadraticCenter

end

end OAI
