import OAI.NumberTheory.SiegelZeros.Hilbert.HilbertMultiplicityFiltration

namespace OAI

namespace SiegelZeros

section

namespace WeightedTorusJets.W22

open WeightedTorusJets.W64
open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Fintype σ]

theorem component_multiplicity_bound
    (I Q : Ideal (MvPolynomial σ k)) [Q.IsPrime]
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (hQhom : Q.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (hQ : Q ∈ I.minimalPrimes) (v : σ) (hv : MvPolynomial.X v ∉ Q)
    (hdegree : (actualHP Q hQhom).natDegree = (actualHP I hI).natDegree) :
    ∃ m : ℕ,
      Module.length (Localization.AtPrime Q)
        (Localization.AtPrime Q ⧸ I.map
          (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q))) = m ∧
      1 ≤ actualMultiplicity Q hQhom (actualHP I hI).natDegree ∧
      (m : ℚ) * actualMultiplicity Q hQhom (actualHP I hI).natDegree ≤
        actualMultiplicity I hI (actualHP I hI).natDegree := by
  classical
  obtain ⟨n, J, f, degrees, hmono, hstart, hend, hdata, hlength⟩ :=
    exists_homogeneous_component_length_count I Q hI hQ
  let D := (actualHP I hI).natDegree
  have hJ : ∀ i, (J i).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) := by
    intro i
    by_cases hi : i < n
    · exact (hdata i hi).1
    · have heq : J i = ⊤ := by
        apply top_unique
        rw [← hend]
        exact (monotone_nat_of_le_succ hmono) (Nat.le_of_not_gt hi)
      rw [heq]
      exact Ideal.IsHomogeneous.top (MvPolynomial.homogeneousSubmodule σ k)
  have hIle : ∀ i, I ≤ J i := fun i =>
    hstart.symm.le.trans ((monotone_nat_of_le_succ hmono) (Nat.zero_le i))
  let P : Fin n → Ideal (MvPolynomial σ k) := fun i => (J i).colon {f i}
  have hP : ∀ i : Fin n, (P i).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) :=
    fun i => homogeneous_colon_singleton (J i) (hJ i) (hdata i i.isLt).2.1
  have hIP : ∀ i : Fin n, I ≤ P i := fun i =>
    (hIle i).trans (ideal_le_colon_singleton (J i) (f i))
  have hPdeg : ∀ i : Fin n, (actualHP (P i) (hP i)).natDegree ≤ D :=
    fun i => actualHP_natDegree_antitone hI (hP i) (hIP i)
  let U : ℕ → ℚ := fun i => actualMultiplicity (J i) (hJ i) D
  let V : ℕ → ℚ := fun i =>
    if hi : i < n then actualMultiplicity (P ⟨i, hi⟩) (hP ⟨i, hi⟩) D else 0
  have hUstep : ∀ i < n, U i = U (i+1) + V i := by
    intro i hi
    simp only [U, V, dite_eq_left hi]
    exact actualMultiplicity_cyclic_step (J i) (J (i+1)) (hJ i) (hJ (i+1))
      (f i) (hdata i hi).2.1 (hdata i hi).2.2.2.2 (hP ⟨i, hi⟩) D (hPdeg ⟨i, hi⟩)
  have hUzero : U 0 = actualMultiplicity I hI D :=
    actualMultiplicity_congr (hJ 0) hI hstart D
  have hUend : U n = 0 := by
    have htop := Ideal.IsHomogeneous.top (MvPolynomial.homogeneousSubmodule σ k)
    exact (actualMultiplicity_congr (hJ n) htop hend D).trans (actualMultiplicity_top htop D)
  have hsum : actualMultiplicity I hI D = ∑ i ∈ Finset.range n, V i := by
    have ht := rational_filtration_telescope U V n hUstep
    rw [hUzero, hUend, add_zero] at ht
    exact ht
  let m : ℕ := ∑ i ∈ Finset.range n, if (J i).colon {f i} = Q then 1 else 0
  have hm : Module.length (Localization.AtPrime Q)
      (Localization.AtPrime Q ⧸ I.map
        (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q))) = m := by
    rw [hlength]
    simp only [m, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  have hpositive : 1 ≤ actualMultiplicity Q hQhom D := by
    obtain ⟨N, hN⟩ := actualHP_eventually Q hQhom
    exact W27.prime_eventual_hilbert_coefficient_ge_one Q v hv (actualHP Q hQhom)
      (N+1) D (fun t ht => (hN t (by omega)).symm) hdegree
  refine ⟨m, hm, hpositive, ?_⟩
  rw [hsum]
  have hmcast : (m : ℚ) =
      ∑ i ∈ Finset.range n, if (J i).colon {f i} = Q then (1 : ℚ) else 0 := by
    simp only [m, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [hmcast, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hin : i < n := Finset.mem_range.mp hi
  simp only [V, dite_eq_left hin]
  by_cases heq : (J i).colon {f i} = Q
  · rw [ite_eq_left heq, one_mul]
    exact le_of_eq (actualMultiplicity_congr (hP ⟨i, hin⟩) hQhom heq D).symm
  · rw [ite_eq_right heq, zero_mul]
    exact actualMultiplicity_nonneg (P ⟨i, hin⟩) (hP ⟨i, hin⟩) D (hPdeg ⟨i, hin⟩)

end WeightedTorusJets.W22

end

end SiegelZeros

end OAI
