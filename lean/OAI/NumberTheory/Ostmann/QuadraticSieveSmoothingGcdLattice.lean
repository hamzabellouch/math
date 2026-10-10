import OAI.NumberTheory.Ostmann.QuadraticSieveComplementError
import OAI.NumberTheory.Ostmann.QuadraticSieveWeightedSmoothing

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve

lemma sieveWeight_zero_outside_rows {M : ℕ} (hM : 0 < M) (m : ℤ)
    (hm : m ∉ Finset.Icc 1 (3*(M:ℤ))) :
    sieveWeight ((m:ℝ)/(M:ℝ)) = 0 := by
  have hMr : (0:ℝ) < M := by exact_mod_cast hM
  simp only [Finset.mem_Icc, not_and_or] at hm
  apply sieveWeight_zero
  rcases hm with hlo | hhi
  · left
    have hm0 : (m:ℝ) ≤ 0 := by exact_mod_cast (show m ≤ 0 by omega)
    exact (div_nonpos_of_nonpos_of_nonneg hm0 hMr.le).trans (by norm_num)
  · right
    have hm3 : 3*(M:ℝ) < (m:ℝ) := by exact_mod_cast (lt_of_not_ge hhi)
    apply (le_div_iff₀ hMr).mpr
    linarith

lemma tsum_positive_nat_eq_integer (f : ℤ → ℂ) (hf : ∀ m : ℤ, m ≤ 0 → f m = 0) :
    (∑' n : {n:ℕ // 0<n}, f (n.val:ℤ)) = ∑' m : ℤ, f m := by
  have hi : Function.Injective (fun n : {n:ℕ // 0<n} => (n.val:ℤ)) := by
    intro a b h
    exact Subtype.ext (Int.ofNat.inj h)
  apply hi.tsum_eq
  intro m hm
  have hp : 0 < m := by
    by_contra h
    exact hm (hf m (le_of_not_gt h))
  refine ⟨⟨m.toNat, by omega⟩, ?_⟩
  exact Int.toNat_of_nonneg hp.le

def smoothingCoprimeLatticeTerm (M d q : ℕ) (m : ℤ) : ℂ :=
  if m.natAbs.Coprime (2*d) then
    (jacobiSym m q:ℂ)*sieveWeight ((m:ℝ)/(M:ℝ)) else 0

lemma smoothingCoprimeLatticeTerm_zero_outside {M : ℕ} (hM : 0<M) (d q : ℕ)
    (m : ℤ) (hm : m ∉ Finset.Icc 1 (3*(M:ℤ))) :
    smoothingCoprimeLatticeTerm M d q m = 0 := by
  simp only [smoothingCoprimeLatticeTerm, sieveWeight_zero_outside_rows hM m hm,
    mul_zero, ite_self]

lemma smoothingCoprimeLatticeTerm_summable {M : ℕ} (hM : 0<M) (d q : ℕ) :
    Summable (smoothingCoprimeLatticeTerm M d q) :=
  summable_of_ne_finset_zero (s := Finset.Icc 1 (3*(M:ℤ)))
    (smoothingCoprimeLatticeTerm_zero_outside hM d q)

lemma odd_square_jacobi_eq_coprime (m : ℤ) (d q : ℕ) [NeZero d] [NeZero q]
    (W : ℂ) :
    (if Odd m then (jacobiSym m (d^2*q):ℂ)*W else 0) =
      if m.natAbs.Coprime (2*d) then (jacobiSym m q:ℂ)*W else 0 := by
  rw [jacobi_square_mul_right]
  simp only [Nat.coprime_mul_iff_right, Nat.coprime_two_right, Int.natAbs_odd,
    Int.gcd_def, Int.natAbs_natCast, Nat.coprime_iff_gcd_eq_one]
  split_ifs <;> simp_all

theorem complementarySchwartzSum_eq_small_lattice {M : ℕ} (hM : 0<M)
    (K d q : ℕ) [NeZero d] [NeZero q] :
    complementarySchwartzSum sieveWeight (M:ℝ) K d q =
      ∑' m : ℤ, if squarefreeKernel m.natAbs ≤ K then
        smoothingCoprimeLatticeTerm M d q m else 0 := by
  unfold complementarySchwartzSum
  have he (n : {n:ℕ // 0<n}) :
      (if squarefreeKernel n.val ≤ K then
        (if Odd n.val then (jacobiSym (n.val:ℤ) (d^2*q):ℂ)*
          sieveWeight ((n.val:ℝ)/(M:ℝ)) else 0) else 0) =
      (if squarefreeKernel (n.val:ℤ).natAbs ≤ K then
        smoothingCoprimeLatticeTerm M d q (n.val:ℤ) else 0) := by
    simp only [Int.natAbs_natCast, smoothingCoprimeLatticeTerm]
    congr 1
    simpa only [Int.odd_coe_nat, Int.natAbs_natCast, Int.cast_natCast] using
      odd_square_jacobi_eq_coprime (n.val:ℤ) d q
        (sieveWeight ((n.val:ℝ)/(M:ℝ)))
  simp_rw [he]
  apply tsum_positive_nat_eq_integer (fun m : ℤ => if squarefreeKernel m.natAbs ≤ K then
    smoothingCoprimeLatticeTerm M d q m else 0)
  intro m hm
  have hz := smoothingCoprimeLatticeTerm_zero_outside hM d q m
    (by simp only [Finset.mem_Icc]; omega)
  simp only [hz, ite_self]

theorem smoothing_lattice_sub_complement {M : ℕ} (hM : 0<M)
    (K d q : ℕ) [NeZero d] [NeZero q] :
    (∑' m : ℤ, smoothingCoprimeLatticeTerm M d q m) -
      complementarySchwartzSum sieveWeight (M:ℝ) K d q =
      ∑ m ∈ smoothingRows M K, smoothingCoprimeLatticeTerm M d q m := by
  classical
  rw [complementarySchwartzSum_eq_small_lattice hM]
  have hsmall : Summable (fun m : ℤ => if squarefreeKernel m.natAbs ≤ K then
      smoothingCoprimeLatticeTerm M d q m else 0) := by
    apply summable_of_ne_finset_zero (s := Finset.Icc 1 (3*(M:ℤ)))
    intro m hm
    simp only [smoothingCoprimeLatticeTerm_zero_outside hM d q m hm, ite_self]
  rw [← (smoothingCoprimeLatticeTerm_summable hM d q).tsum_sub hsmall]
  rw [tsum_eq_sum (s := smoothingRows M K)]
  · apply Finset.sum_congr rfl
    intro m hm
    have hc := (mem_smoothingRows.mp hm).2.2.2
    simp only [ite_eq_right (not_le.mpr hc), sub_zero]
  · intro m hm
    by_cases hsmall : squarefreeKernel m.natAbs ≤ K
    · simp only [ite_eq_left hsmall, sub_self]
    · simp only [ite_eq_right hsmall, sub_zero]
      by_cases hrow : m ∈ Finset.Icc 1 (3*(M:ℤ))
      · have hodd : ¬ Odd m := by
          intro ho
          exact hm (mem_smoothingRows.mpr ⟨(Finset.mem_Icc.mp hrow).1,
            (Finset.mem_Icc.mp hrow).2, ho, lt_of_not_ge hsmall⟩)
        have hcop : ¬ m.natAbs.Coprime (2*d) := by
          simp only [Nat.coprime_mul_iff_right, Nat.coprime_two_right,
            Int.natAbs_odd]
          exact fun h => hodd h.1
        simp only [smoothingCoprimeLatticeTerm, ite_eq_right hcop]
      · exact smoothingCoprimeLatticeTerm_zero_outside hM d q m hrow

end Ostmann.QuadraticSieve

end

end OAI
