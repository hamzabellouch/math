import Mathlib.Order.Minimal
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.LocalizedFiltrationLength

namespace OAI

namespace SiegelZeros

section

namespace WeightedTorusJets.W22

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Finite σ]

omit [Finite σ] in
theorem homogeneous_colon_singleton
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} {f : MvPolynomial σ k} (hf : f.IsHomogeneous d) :
    (I.colon {f}).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) := by
  intro n a ha
  apply Submodule.mem_colon_singleton.mpr
  have haf : a * f ∈ I := by simpa only [smul_eq_mul] using
    (Submodule.mem_colon_singleton.mp ha)
  have h := hI (n + d) haf
  rw [DirectSum.coe_decompose_mul_add_of_right_mem
    (MvPolynomial.homogeneousSubmodule σ k) hf] at h
  exact h

theorem exists_homogeneous_prime_colon
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (hproper : I ≠ ⊤) :
    ∃ (d : ℕ) (f : MvPolynomial σ k), f.IsHomogeneous d ∧ f ∉ I ∧
      (I.colon {f}).IsPrime := by
  classical
  let candidates : Ideal (MvPolynomial σ k) → Prop := fun P =>
    ∃ d f, f.IsHomogeneous d ∧ f ∉ I ∧ P = I.colon {f}
  have hnonempty : ∃ P, candidates P := by
    refine ⟨I.colon {(1 : MvPolynomial σ k)}, 0, 1, ?_, ?_, rfl⟩
    · exact MvPolynomial.isHomogeneous_one σ k
    · exact fun h => hproper (Ideal.eq_top_of_isUnit_mem I h isUnit_one)
  obtain ⟨P, hP, hmax⟩ := exists_maximal_of_wellFoundedGT candidates hnonempty
  obtain ⟨d, f, hf, hfI, rfl⟩ := hP
  refine ⟨d, f, hf, hfI, ?_⟩
  apply (homogeneous_colon_singleton I hI hf).isPrime_of_homogeneous_mem_or_mem
  · intro htop
    have h : (1 : MvPolynomial σ k) ∈ I.colon {f} := by
      rw [htop]
      trivial
    exact hfI (by simpa only [Submodule.mem_colon_singleton, one_smul] using h)
  · intro a b ha hb hab
    by_cases hbI : b ∈ I.colon {f}
    · exact Or.inr hbI
    · left
      obtain ⟨e, he⟩ := hb
      have hb' : b.IsHomogeneous e := he
      have hbf : (b * f).IsHomogeneous (e + d) := hb'.mul hf
      have hbfI : b * f ∉ I := by
        simpa only [Submodule.mem_colon_singleton, smul_eq_mul] using hbI
      have hle : I.colon {f} ≤ I.colon {b * f} := by
        intro r hr
        apply Submodule.mem_colon_singleton.mpr
        have hrf : r * f ∈ I := by
          simpa only [smul_eq_mul] using (Submodule.mem_colon_singleton.mp hr)
        simpa only [smul_eq_mul, mul_left_comm r b f] using I.mul_mem_left b hrf
      have hback : I.colon {b * f} ≤ I.colon {f} :=
        hmax ⟨e + d, b * f, hbf, hbfI, rfl⟩ hle
      apply hback
      apply Submodule.mem_colon_singleton.mpr
      simpa only [smul_eq_mul, mul_assoc] using (Submodule.mem_colon_singleton.mp hab)

end WeightedTorusJets.W22

end

section

namespace WeightedTorusJets.W22

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Finite σ]

def HomogeneousPrimeStep (I J : Ideal (MvPolynomial σ k)) : Prop :=
  I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) ∧
    ∃ (d : ℕ) (f : MvPolynomial σ k), f.IsHomogeneous d ∧ f ∉ I ∧
      (I.colon {f}).IsPrime ∧ J = I ⊔ Ideal.span {f}

omit [Finite σ] in
theorem HomogeneousPrimeStep.homogeneous {I J : Ideal (MvPolynomial σ k)}
    (h : HomogeneousPrimeStep I J) :
    J.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) := by
  obtain ⟨hI, d, f, hf, _, _, rfl⟩ := h
  apply hI.sup
  apply Ideal.homogeneous_span (MvPolynomial.homogeneousSubmodule σ k)
  intro x hx
  obtain rfl := Set.mem_singleton_iff.mp hx
  exact ⟨d, hf⟩

omit [Finite σ] in
theorem HomogeneousPrimeStep.lt {I J : Ideal (MvPolynomial σ k)}
    (h : HomogeneousPrimeStep I J) : I < J := by
  obtain ⟨_, d, f, _, hfI, _, rfl⟩ := h
  refine lt_of_le_of_ne le_sup_left ?_
  intro heq
  have hm : f ∈ I ⊔ Ideal.span {f} :=
    (show Ideal.span {f} ≤ I ⊔ Ideal.span {f} from le_sup_right)
      (Ideal.subset_span (by simp))
  exact hfI (by simpa only [← heq] using hm)

omit [Finite σ] in
theorem HomogeneousPrimeStep.isQuotientEquivQuotientPrime
    {I J : Ideal (MvPolynomial σ k)} (h : HomogeneousPrimeStep I J) :
    I.IsQuotientEquivQuotientPrime J := by
  obtain ⟨_, d, f, _, _, hp, rfl⟩ := h
  exact ⟨le_sup_left, ⟨⟨I.colon {f}, hp⟩, ⟨(cyclicFactorEquiv I f).symm⟩⟩⟩

theorem exists_homogeneous_prime_filtration
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    ∃ s : RelSeries {(A, B) | HomogeneousPrimeStep (k := k) (σ := σ) A B},
      s.head = I ∧ s.last = ⊤ := by
  let r : Set (Ideal (MvPolynomial σ k) × Ideal (MvPolynomial σ k)) :=
    {(A, B) | HomogeneousPrimeStep A B}
  have ht : (⊤ : Ideal (MvPolynomial σ k)).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule σ k) ∧
      ∃ s : RelSeries r, s.head = I ∧ s.last = ⊤ := by
    refine WellFoundedGT.induction_top
      ⟨I, hI, RelSeries.singleton r I, rfl, rfl⟩ ?_
    rintro J hJtop ⟨hJ, s, hshead, hslast⟩
    obtain ⟨d, f, hf, hfJ, hp⟩ := exists_homogeneous_prime_colon J hJ hJtop
    have hstep : HomogeneousPrimeStep J (J ⊔ Ideal.span {f}) :=
      ⟨hJ, d, f, hf, hfJ, hp, rfl⟩
    refine ⟨J ⊔ Ideal.span {f}, hstep.lt, hstep.homogeneous,
      s.snoc (J ⊔ Ideal.span {f}) (by
        change HomogeneousPrimeStep s.last (J ⊔ Ideal.span {f})
        simpa only [hslast] using hstep), ?_, by simp only [RelSeries.last_snoc]⟩
    simpa using hshead
  exact ht.2

end WeightedTorusJets.W22

end

section

namespace WeightedTorusJets.W22

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
  · calc
      J 0 = s.head := by
        apply congrArg s
        apply Fin.ext
        simp
      _ = I := hshead
  · calc
      J s.length = s.last := by
        apply congrArg s
        apply Fin.ext
        simp
      _ = ⊤ := hslast
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

end WeightedTorusJets.W22

end

end SiegelZeros

end OAI
