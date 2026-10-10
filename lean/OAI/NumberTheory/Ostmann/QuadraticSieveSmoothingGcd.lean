import OAI.NumberTheory.Ostmann.QuadraticSieveDualCorrelations
import OAI.NumberTheory.Ostmann.QuadraticSieveSmoothingGcdLattice
import OAI.NumberTheory.Ostmann.QuadraticSieveSmoothingGcdSupport
import OAI.NumberTheory.Ostmann.QuadraticSieveWeightedSmoothingNorm

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve
open ComplexConjugate

theorem gcdJacobiRow_eq_quotient_denominator (S : Finset ℕ) (a : ℕ → ℂ)
    {d : ℕ} (hd : 0<d) (hS : ∀ n ∈ S, 0<n) (m : ℤ) :
    gcdJacobiRow S a d m =
      complementaryPair (quotientSupport S d) (fun n => a (d*n))
        (fun q => (jacobiSym m (d^2*q):ℂ)) := by
  unfold gcdJacobiRow
  rw [gcdCorrelation_eq_quotient S _ hd]
  unfold complementaryPair
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro t ht
  have hn0 := (Nat.mul_pos hd (quotientSupport_pos hS hn)).ne'
  have ht0 := (Nat.mul_pos hd (quotientSupport_pos hS ht)).ne'
  have he : d^2*(n*t) = (d*n)*(d*t) := by ring
  dsimp only
  rw [he, jacobiSym.mul_right' m hn0 ht0]
  simp only [Int.cast_mul, star_mul, star_intCast, starRingEnd_apply]
  split_ifs <;> ring

theorem smoothing_weighted_gcdJacobiRow {M K d : ℕ} (hd : 0<d)
    (S : Finset ℕ) (a : ℕ → ℂ) (hS : ∀ n ∈ S, 0<n)
    {m : ℤ} (hm : m ∈ smoothingRows M K) :
    (smoothingWeight M m:ℂ)*gcdJacobiRow S a d m =
      complementaryPair (quotientSupport S d) (fun n => a (d*n))
        (fun q => smoothingCoprimeLatticeTerm M d q m) := by
  let : NeZero d := ⟨hd.ne'⟩
  rw [gcdJacobiRow_eq_quotient_denominator S a hd hS,
    ← complementaryPair_mul]
  apply complementaryPair_congr
  intro n hn t ht hnt
  let : NeZero (n*t) := ⟨(Nat.mul_pos
    (quotientSupport_pos hS hn) (quotientSupport_pos hS ht)).ne'⟩
  have he := odd_square_jacobi_eq_coprime m d (n*t)
    (sieveWeight ((m:ℝ)/(M:ℝ)))
  rw [ite_eq_left (mem_smoothingRows.mp hm).2.2.1] at he
  simpa only [smoothingCoprimeLatticeTerm, sieveWeight_apply, smoothingWeight,
    mul_comm] using he

theorem smoothing_gcdCorrelation_eq_dual_sub_complement {M d : ℕ}
    (hM : 0<M) (hd : 0<d) (K : ℕ) (S : Finset ℕ) (a : ℕ → ℂ)
    (hS : ∀ n ∈ S, 0<n) :
    weightedGcdCorrelation (smoothingRows M K) S (smoothingWeight M) a d =
      dualCorrelation sieveWeight (M:ℝ) d (quotientSupport S d) (fun n => a (d*n)) -
        complementaryCorrelation sieveWeight (M:ℝ) K d
          (quotientSupport S d) (fun n => a (d*n)) := by
  classical
  let : NeZero d := ⟨hd.ne'⟩
  unfold weightedGcdCorrelation
  rw [Finset.sum_congr rfl (fun m hm => smoothing_weighted_gcdJacobiRow hd S a hS hm)]
  rw [← complementaryPair_sum]
  unfold dualCorrelation complementaryCorrelation
  rw [← complementaryPair_sub]
  apply complementaryPair_congr
  intro n hn t ht hnt
  let : NeZero (n*t) := ⟨(Nat.mul_pos
    (quotientSupport_pos hS hn) (quotientSupport_pos hS ht)).ne'⟩
  exact (smoothing_lattice_sub_complement hM K d (n*t)).symm

theorem smoothing_gcdCorrelation_eq_of_oddSquarefree {M d N : ℕ}
    (hM : 0<M) (hd : 0<d) (K : ℕ) (S : Finset ℕ) (a : ℕ → ℂ)
    (hS : S ⊆ oddSquarefreeUpTo N) :
    weightedGcdCorrelation (smoothingRows M K) S (smoothingWeight M) a d =
      dualCorrelation sieveWeight (M:ℝ) d (quotientSupport S d) (fun n => a (d*n)) -
        complementaryCorrelation sieveWeight (M:ℝ) K d
          (quotientSupport S d) (fun n => a (d*n)) :=
  smoothing_gcdCorrelation_eq_dual_sub_complement hM hd K S a
    (fun _n hn => (mem_oddSquarefreeUpTo.mp (hS hn)).1)

theorem weightedGcdCorrelation_zero_of_bad_factor (W : Finset ℤ) (ω : ℤ → ℝ)
    {S : Finset ℕ} (a : ℕ → ℂ) {d : ℕ} (hd : 0<d)
    (hS : ∀ n ∈ S, Odd n ∧ Squarefree n) (hbad : ¬ (Odd d ∧ Squarefree d)) :
    weightedGcdCorrelation W S ω a d = 0 := by
  simp only [weightedGcdCorrelation, gcdJacobiRow_zero_of_bad_factor a hd hS hbad,
    mul_zero, Finset.sum_const_zero]

end Ostmann.QuadraticSieve

end

end OAI
