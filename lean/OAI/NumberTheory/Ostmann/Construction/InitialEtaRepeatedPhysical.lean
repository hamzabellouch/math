import OAI.NumberTheory.Ostmann.Construction.ActualLocalL2
import OAI.NumberTheory.Ostmann.Construction.InitialEtaPhysical
import OAI.NumberTheory.Ostmann.Construction.RepeatedPhysical

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators FourierTransform
namespace Ostmann.Construction.InitialEta

lemma tupleLocalTest_sum_zero (d : Decomposition) (P : Finset ℕ)
    {b s : ℕ} {ι : Type*} (i : Position b s ι) (q : ℕ) [NeZero q] :
    ∑x:ZMod q,tupleLocalTest d P i q x=0 := by
  rcases i with ⟨h,i⟩
  cases i with
  | inl _ => exact favorableGiantResidueTest_sum_zero d P q
  | inr _ => exact residueTest_sum_zero d q

lemma tupleLocalTest_sq_sum_le (d : Decomposition) (P : Finset ℕ)
    {b s : ℕ} {ι : Type*} (i : Position b s ι) (q : ℕ) (hq : q.Prime) [NeZero q] :
    (∑x:ZMod q,‖tupleLocalTest d P i q x‖^2)≤(q:ℝ) := by
  rcases i with ⟨h,i⟩
  cases i with
  | inl _ => exact favorableGiantResidueTest_sq_sum_le d P q
  | inr _ => exact (residueTest_sq_sum d hq).le

theorem tuplePhysical_repeated_bound (d : Decomposition) (P : Finset ℕ)
    (giant bulk spectator : PrimeSource) {ι : Type*} [Fintype ι]
    (aux : ι → PrimeSource) (b s : ℕ) (tb td : ℤ) {X : ℝ} (hX : 0<X)
    (x : JointSample giant bulk spectator aux b s)
    (hperiod : ((∏q:↥(tupleDistinctPrimes (tupleValues x)),(q:ℕ):ℕ):ℝ)/4<X) :
    ‖tuplePhysical d P giant bulk spectator aux b s tb td X x‖≤
      Real.sqrt X*‖𝓕 SchwartzCutoff.psi 0‖*
        (Real.sqrt (∏i,tupleValues x i:ℕ)/
          (∏q:↥(tupleDistinctPrimes (tupleValues x)),(q:ℕ):ℕ)) := by
  classical
  let (q : ↥(tupleDistinctPrimes (tupleValues x))) : NeZero (q:ℕ) :=
    ⟨(tupleDistinctPrimes_prime (tupleValues x) (tupleValues_prime x) q).ne_zero⟩
  have hb := centered_tuple_physical_bound (tupleValues x) (tupleValues_prime x)
    (tupleLocalTest d P)
    (fun q i => tupleLocalTest_sum_zero d P i q)
    (fun q i => tupleLocalTest_sq_sum_le d P i q
      (tupleDistinctPrimes_prime (tupleValues x) (tupleValues_prime x) q)) hX hperiod
  rw [tuplePhysical_eq,mul_div_assoc,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (tupleBins_nonneg tb td x)]
  exact (mul_le_of_le_one_left (norm_nonneg _) (tupleBins_le_one tb td x)).trans hb

lemma tuplePhysical_eq_zero_of_bins_zero (d : Decomposition) (P : Finset ℕ)
    (giant bulk spectator : PrimeSource) {ι : Type*} [Fintype ι]
    (aux : ι → PrimeSource) (b s : ℕ) (tb td : ℤ) (X : ℝ)
    (x : JointSample giant bulk spectator aux b s) (h : tupleBins tb td x=0) :
    tuplePhysical d P giant bulk spectator aux b s tb td X x=0 := by
  rw [tuplePhysical_eq,h,Complex.ofReal_zero,zero_mul,zero_div]

end Ostmann.Construction.InitialEta

end

end OAI
