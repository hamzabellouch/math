import OAI.NumberTheory.SiegelZeros.Hilbert.HilbertMultiplicityFiltration

namespace OAI

namespace SiegelZeros

section

namespace WeightedTorusJets.W22

open WeightedTorusJets.W64
open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra

theorem distinct_selected_factor_weight_le
    {τ β : Type*} [Fintype τ] (Q : τ → β) (hQinj : Function.Injective Q)
    (P : β) (W : τ → ℚ) (V : ℚ) (hV : 0 ≤ V)
    (hmatch : ∀ a, P = Q a → W a = V) :
    (∑ a, if P = Q a then W a else 0) ≤ V := by
  classical
  by_cases hex : ∃ a, P = Q a
  · obtain ⟨a, ha⟩ := hex
    have hsum : (∑ b, if P = Q b then W b else 0) = W a := by
      rw [Finset.sum_eq_single a]
      · simp only [ite_eq_left ha]
      · intro b _ hba
        have hb : P ≠ Q b := by
          intro hb
          exact hba (hQinj (hb.symm.trans ha))
        exact ite_eq_right hb
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ a))
    rw [hsum, hmatch a ha]
  · have hzero : (∑ a, if P = Q a then W a else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      exact ite_eq_right (fun ha => hex ⟨a, ha⟩)
    rw [hzero]
    exact hV

theorem grouped_count_weighted_sum_eq
    {τ β : Type*} [Fintype τ] (n : ℕ) (P : ℕ → β) (Q : τ → β) (W : τ → ℚ) :
    (∑ a, ((∑ i ∈ Finset.range n, if P i = Q a then 1 else 0 : ℕ) : ℚ) * W a) =
      ∑ i ∈ Finset.range n, ∑ a, if P i = Q a then W a else 0 := by
  classical
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    Finset.sum_mul, ite_mul, one_mul, zero_mul]
  exact Finset.sum_comm

variable {k σ τ : Type*} [Field k] [Fintype σ] [Fintype τ]

theorem component_multiplicity_sum_bound
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (Q : τ → Ideal (MvPolynomial σ k)) [∀ a, (Q a).IsPrime]
    (hQinj : Function.Injective Q)
    (hQhom : ∀ a, (Q a).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (hQ : ∀ a, Q a ∈ I.minimalPrimes)
    (v : τ → σ) (hv : ∀ a, MvPolynomial.X (v a) ∉ Q a)
    (hdegree : ∀ a, (actualHP (Q a) (hQhom a)).natDegree = (actualHP I hI).natDegree) :
    ∃ m : τ → ℕ,
      (∀ a, Module.length (Localization.AtPrime (Q a))
        (Localization.AtPrime (Q a) ⧸ I.map
          (algebraMap (MvPolynomial σ k) (Localization.AtPrime (Q a)))) = m a) ∧
      (∀ a, 1 ≤ actualMultiplicity (Q a) (hQhom a) (actualHP I hI).natDegree) ∧
      (∑ a, (m a : ℚ) * actualMultiplicity (Q a) (hQhom a)
        (actualHP I hI).natDegree) ≤ actualMultiplicity I hI (actualHP I hI).natDegree := by
  classical
  obtain ⟨n, J, f, degrees, hmono, hstart, hend, hdata⟩ :=
    exists_homogeneous_cyclic_filtration_nat I hI
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
  let m : τ → ℕ := fun a =>
    ∑ i ∈ Finset.range n, if (J i).colon {f i} = Q a then 1 else 0
  have hm : ∀ a, Module.length (Localization.AtPrime (Q a))
      (Localization.AtPrime (Q a) ⧸ I.map
        (algebraMap (MvPolynomial σ k) (Localization.AtPrime (Q a)))) = m a := by
    intro a
    have hlength := localized_cyclic_filtration_length I (Q a) (hQ a)
      J hmono hstart n hend f
      (fun i hi => (hdata i hi).2.2.2.2) (fun i hi => (hdata i hi).2.2.2.1)
    rw [hlength]
    simp only [m, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  have hpositive : ∀ a, 1 ≤ actualMultiplicity (Q a) (hQhom a) D := by
    intro a
    obtain ⟨N, hN⟩ := actualHP_eventually (Q a) (hQhom a)
    exact W27.prime_eventual_hilbert_coefficient_ge_one (Q a) (v a) (hv a)
      (actualHP (Q a) (hQhom a)) (N+1) D
      (fun t ht => (hN t (by omega)).symm) (hdegree a)
  refine ⟨m, hm, hpositive, ?_⟩
  change (∑ a, (m a : ℚ) * actualMultiplicity (Q a) (hQhom a) D) ≤
    actualMultiplicity I hI D
  rw [hsum]
  have hgroup := grouped_count_weighted_sum_eq n
    (fun i => (J i).colon {f i}) Q (fun a => actualMultiplicity (Q a) (hQhom a) D)
  change (∑ a, (m a : ℚ) * actualMultiplicity (Q a) (hQhom a) D) = _ at hgroup
  rw [hgroup]
  apply Finset.sum_le_sum
  intro i hi
  have hin : i < n := Finset.mem_range.mp hi
  have hnonneg : 0 ≤ V i := by
    simp only [V, dite_eq_left hin]
    exact actualMultiplicity_nonneg (P ⟨i, hin⟩) (hP ⟨i, hin⟩) D (hPdeg ⟨i, hin⟩)
  apply distinct_selected_factor_weight_le Q hQinj ((J i).colon {f i})
    (fun a => actualMultiplicity (Q a) (hQhom a) D) (V i) hnonneg
  intro a heq
  simp only [V, dite_eq_left hin]
  exact (actualMultiplicity_congr (hP ⟨i, hin⟩) (hQhom a) heq D).symm

end WeightedTorusJets.W22

end

section

namespace WeightedTorusJets.W22

open WeightedTorusJets.W64
open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ τ : Type*} [Field k] [Fintype σ] [Fintype τ]

noncomputable def actualLocalLength (I Q : Ideal (MvPolynomial σ k)) [Q.IsPrime] : ℕ :=
  (Module.length (Localization.AtPrime Q)
    (Localization.AtPrime Q ⧸ I.map
      (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q)))).toNat

theorem actualLocalLength_spec
    (I Q : Ideal (MvPolynomial σ k)) [Q.IsPrime]
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (hQ : Q ∈ I.minimalPrimes) :
    Module.length (Localization.AtPrime Q)
      (Localization.AtPrime Q ⧸ I.map
        (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q))) = actualLocalLength I Q := by
  obtain ⟨n, J, f, d, hmono, hstart, hend, hdata, hlength⟩ :=
    exists_homogeneous_component_length_count I Q hI hQ
  let m : ℕ := ∑ i ∈ Finset.range n, if (J i).colon {f i} = Q then 1 else 0
  have hm : Module.length (Localization.AtPrime Q)
      (Localization.AtPrime Q ⧸ I.map
        (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q))) = m := by
    rw [hlength]
    simp only [m, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  simp only [actualLocalLength, hm, ENat.toNat_natCast]

omit [Fintype σ] in
theorem primeCut_isHomogeneous
    (P : Ideal (MvPolynomial σ k))
    (hP : P.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d) :
    (Ideal.span {f} ⊔ P).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) := by
  have hsingle : (Ideal.span {f}).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) := by
    apply Ideal.homogeneous_span (MvPolynomial.homogeneousSubmodule σ k)
    intro x hx
    have hxf : x = f := Set.mem_singleton_iff.mp hx
    subst x
    exact ⟨d, hf⟩
  exact hsingle.sup hP

theorem actualHP_prime_cut_degree_multiplicity
    (P : Ideal (MvPolynomial σ k)) [P.IsPrime]
    (hP : P.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d)
    (hfP : f ∉ P) (hd : 0 < d) (s : ℕ)
    (hdegree : (actualHP P hP).natDegree = s+1) :
    (actualHP (Ideal.span {f} ⊔ P) (primeCut_isHomogeneous P hP f hf)).natDegree = s ∧
      actualMultiplicity (Ideal.span {f} ⊔ P) (primeCut_isHomogeneous P hP f hf) s =
        (d : ℚ) * actualMultiplicity P hP (s+1) := by
  obtain ⟨N, hN⟩ := actualHP_eventually P hP
  obtain ⟨q, ⟨M, hM⟩, hqdegree, hqmult⟩ :=
    prime_hypersurface_actual_hilbert_degree P hP f hf hfP hd
      (actualHP P hP) N s hN hdegree
  have hq : actualHP (Ideal.span {f} ⊔ P) (primeCut_isHomogeneous P hP f hf) = q :=
    actualHP_unique _ _ q M hM
  refine ⟨by rw [hq]; exact hqdegree, ?_⟩
  unfold actualMultiplicity
  rw [hq]
  simpa only [Polynomial.leadingCoeff, hqdegree, hdegree] using hqmult

theorem prime_cut_component_budget
    (P : Ideal (MvPolynomial σ k)) [P.IsPrime]
    (hP : P.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d)
    (hfP : f ∉ P) (hd : 0 < d) (s : ℕ)
    (hdegree : (actualHP P hP).natDegree = s+1)
    (Q : τ → Ideal (MvPolynomial σ k)) [∀ a, (Q a).IsPrime]
    (hQinj : Function.Injective Q)
    (hQhom : ∀ a, (Q a).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (hQ : ∀ a, Q a ∈ (Ideal.span {f} ⊔ P).minimalPrimes)
    (v : τ → σ) (hv : ∀ a, MvPolynomial.X (v a) ∉ Q a)
    (hchildDegree : ∀ a, (actualHP (Q a) (hQhom a)).natDegree = s) :
    (∑ a, (actualLocalLength (Ideal.span {f} ⊔ P) (Q a) : ℚ) *
      actualMultiplicity (Q a) (hQhom a) s) ≤
      (d : ℚ) * actualMultiplicity P hP (s+1) := by
  have hI := primeCut_isHomogeneous P hP f hf
  obtain ⟨hIdegree, hImult⟩ := actualHP_prime_cut_degree_multiplicity
    P hP f hf hfP hd s hdegree
  obtain ⟨m, hm, hpositive, hbudget⟩ := component_multiplicity_sum_bound
    (Ideal.span {f} ⊔ P) hI Q hQinj hQhom hQ v hv
      (fun a => (hchildDegree a).trans hIdegree.symm)
  have hmactual : ∀ a, actualLocalLength (Ideal.span {f} ⊔ P) (Q a) = m a := by
    intro a
    unfold actualLocalLength
    rw [hm a, ENat.toNat_natCast]
  simpa only [hIdegree, hmactual, hImult] using hbudget

theorem actualHP_natDegree_of_prime_dimension
    (Q : Ideal (MvPolynomial σ k)) [Q.IsPrime]
    (hQ : Q.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (v : σ) (hv : MvPolynomial.X v ∉ Q) (s : ℕ)
    (hdim : ringKrullDim (MvPolynomial σ k ⧸ Q) = (s+1 : ℕ)) :
    (actualHP Q hQ).natDegree = s := by
  obtain ⟨N, hN⟩ := actualHP_eventually Q hQ
  have h := W24.prime_hilbert_natDegree_add_one_eq_krullDim Q hQ v hv
    (actualHP Q hQ) (N+1) (fun n hn => (hN n (by omega)).symm)
  have heq : (actualHP Q hQ).natDegree + 1 = s+1 := by exact_mod_cast h.trans hdim
  omega

end WeightedTorusJets.W22

end

end SiegelZeros

end OAI
