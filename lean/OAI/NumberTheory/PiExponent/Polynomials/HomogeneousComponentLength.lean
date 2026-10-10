import OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedFiltrationLength
import OAI.NumberTheory.PiExponent.Polynomials.HomogeneousPrimeFiltration

namespace OAI

namespace PiExponentJets.W22

open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Finite σ]

theorem exists_homogeneous_cyclic_filtration_nat
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    ∃ (n : ℕ) (J : ℕ → Ideal (MvPolynomial σ k))
      (f : ℕ → MvPolynomial σ k) (d : ℕ → ℕ),
      (∀ i, J i ≤ J (i + 1)) ∧ J 0 = I ∧ J n = ⊤ ∧
      ∀ i < n, (J i).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) ∧
        (f i).IsHomogeneous (d i) ∧ f i ∉ J i ∧
        ((J i).colon {f i}).IsPrime ∧ J (i + 1) = J i ⊔ Ideal.span {f i} := by
  classical
  obtain ⟨s, hshead, hslast⟩ := exists_homogeneous_prime_filtration I hI
  have hsmono : Monotone s :=
    (Fin.strictMono_iff_lt_succ.mpr fun i => (s.step i).lt).monotone
  let J : ℕ → Ideal (MvPolynomial σ k) := fun i =>
    s ⟨min i s.length, Nat.lt_succ_of_le (min_le_right _ _)⟩
  have hd : ∀ i : Fin s.length, ∃ (d : ℕ) (f : MvPolynomial σ k),
      f.IsHomogeneous d ∧ f ∉ s i.castSucc ∧
        ((s i.castSucc).colon {f}).IsPrime ∧
        s i.succ = s i.castSucc ⊔ Ideal.span {f} := fun i => (s.step i).2
  let degrees : Fin s.length → ℕ := fun i => (hd i).choose
  let generators : Fin s.length → MvPolynomial σ k := fun i => (hd i).choose_spec.choose
  let f : ℕ → MvPolynomial σ k := fun i =>
    if hi : i < s.length then generators ⟨i, hi⟩ else 0
  let d : ℕ → ℕ := fun i => if hi : i < s.length then degrees ⟨i, hi⟩ else 0
  refine ⟨s.length, J, f, d, ?_, ?_, ?_, ?_⟩
  · intro i
    apply hsmono
    exact min_le_min_right s.length (Nat.le_succ i)
  · change s.head = I
    exact hshead
  · simpa only [J, min_self, RelSeries.last, Fin.last] using hslast
  · intro i hi
    have hfi := (hd ⟨i, hi⟩).choose_spec.choose_spec
    have hleft : J i = s (Fin.castSucc ⟨i, hi⟩) := by
      apply congrArg s
      apply Fin.ext
      exact min_eq_left (Nat.le_of_lt hi)
    have hright : J (i + 1) = s (Fin.succ ⟨i, hi⟩) := by
      apply congrArg s
      apply Fin.ext
      exact min_eq_left (Nat.succ_le_of_lt hi)
    simpa only [f, d, dite_eq_left hi, degrees, generators, hleft, hright] using
      And.intro (s.step ⟨i, hi⟩).1 hfi

theorem exists_homogeneous_component_length_count
    (I Q : Ideal (MvPolynomial σ k)) [Q.IsPrime]
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (hQ : Q ∈ I.minimalPrimes) :
    ∃ (n : ℕ) (J : ℕ → Ideal (MvPolynomial σ k))
      (f : ℕ → MvPolynomial σ k) (d : ℕ → ℕ),
      (∀ i, J i ≤ J (i + 1)) ∧ J 0 = I ∧ J n = ⊤ ∧
      (∀ i < n, (J i).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) ∧
        (f i).IsHomogeneous (d i) ∧ f i ∉ J i ∧
        ((J i).colon {f i}).IsPrime ∧ J (i + 1) = J i ⊔ Ideal.span {f i}) ∧
      Module.length (Localization.AtPrime Q)
        (Localization.AtPrime Q ⧸ I.map
          (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q))) =
        ∑ i ∈ Finset.range n, if (J i).colon {f i} = Q then 1 else 0 := by
  obtain ⟨n, J, f, d, hmono, hstart, hend, hstep⟩ :=
    exists_homogeneous_cyclic_filtration_nat I hI
  refine ⟨n, J, f, d, hmono, hstart, hend, hstep, ?_⟩
  exact localized_cyclic_filtration_length I Q hQ J hmono hstart n hend f
    (fun i hi => (hstep i hi).2.2.2.2) (fun i hi => (hstep i hi).2.2.2.1)

end PiExponentJets.W22

end OAI
