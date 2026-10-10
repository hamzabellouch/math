import OAI.NumberTheory.TwoPointCorrelations.SieveIntersections
import OAI.NumberTheory.TwoPointCorrelations.SieveBoundary
import OAI.NumberTheory.TwoPointCorrelations.SieveProducts

namespace OAI

/-! Finite rough-sieve bounds with every intersection error discharged by
CRT on the actual interval sample space. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem finite_interval_sieve {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)]
    (hcop : Pairwise (fun i j => (s i).Coprime (s j)))
    (A N : ℕ) [NeZero N] (E : ∀ i, ZMod (s i) → Prop) (r : ℕ) (Y : ℝ)
    (hY : 0 ≤ Y) (hs : ∀ i, (s i : ℝ) ≤ Y) :
    (uniformFiniteLaw (Fin N)).probability
      (avoidsEvents univ (fun i (j : Fin N) => E i ((A + j.val : ℕ) : ZMod (s i)))) ≤
      (∏ i, (1 - (uniformZModLaw (s i)).probability (E i))) +
        elementarySymmetric univ (fun i => (uniformZModLaw (s i)).probability (E i))
          (2 * r + 1) +
        1 / (N : ℝ) * (2 * r + 1 : ℕ) * ((Fintype.card ι : ℝ) * Y + 1) ^ (2 * r) := by
  have hh := finite_independent_sieve_bound (uniformFiniteLaw (Fin N))
    (fun i (j : Fin N) => E i ((A + j.val : ℕ) : ZMod (s i)))
    (fun i => uniformZModLaw (s i)) E r
    (fun S => 1 / (N : ℝ) * ∏ i ∈ S, (s i : ℝ)) (fun S _ _ => by
      exact (sieve_one_intersection s hcop A N E S).trans_eq (by ring))
  apply hh.trans
  gcongr
  simpa only [card_univ] using sieveIntersectionError_crude univ (fun i => (s i : ℝ))
    Y 1 hY zero_le_one (fun i _ => ⟨Nat.cast_nonneg _, hs i⟩) N (2 * r)

theorem finite_cube_sieve {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)]
    (hcop : Pairwise (fun i j => (s i).Coprime (s j)))
    (A : ℕ × ℕ × ℕ) (N : ℕ) [NeZero N]
    (E : ∀ i, (ZMod (s i) × ZMod (s i) × ZMod (s i)) → Prop) (r : ℕ) (Y : ℝ)
    (hY : 0 ≤ Y) (hs : ∀ i, (s i : ℝ) ≤ Y) :
    (uniformFiniteLaw (Fin N × Fin N × Fin N)).probability
      (avoidsEvents univ (fun i (j : Fin N × Fin N × Fin N) => E i
        (((A.1 + j.1.val : ℕ) : ZMod (s i)), ((A.2.1 + j.2.1.val : ℕ) : ZMod (s i)),
          ((A.2.2 + j.2.2.val : ℕ) : ZMod (s i))))) ≤
      (∏ i, (1 - (uniformResidueCubeLaw (s i)).probability (E i))) +
        elementarySymmetric univ
          (fun i => (uniformResidueCubeLaw (s i)).probability (E i)) (2 * r + 1) +
        3 / (N : ℝ) * (2 * r + 1 : ℕ) * ((Fintype.card ι : ℝ) * Y + 1) ^ (2 * r) := by
  have hh := finite_independent_sieve_bound (uniformFiniteLaw (Fin N × Fin N × Fin N))
    (fun i (j : Fin N × Fin N × Fin N) => E i
      (((A.1 + j.1.val : ℕ) : ZMod (s i)), ((A.2.1 + j.2.1.val : ℕ) : ZMod (s i)),
        ((A.2.2 + j.2.2.val : ℕ) : ZMod (s i))))
    (fun i => uniformResidueCubeLaw (s i)) E r
    (fun S => 3 / (N : ℝ) * ∏ i ∈ S, (s i : ℝ))
    (fun S _ _ => sieve_cube_intersection s hcop A N E S)
  apply hh.trans
  gcongr
  simpa only [card_univ] using sieveIntersectionError_crude univ (fun i => (s i : ℝ))
    Y 3 hY (by norm_num) (fun i _ => ⟨Nat.cast_nonneg _, hs i⟩) N (2 * r)

end TwoPointCorrelations

end OAI
