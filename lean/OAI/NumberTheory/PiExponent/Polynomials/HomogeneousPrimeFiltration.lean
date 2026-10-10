import OAI.NumberTheory.PiExponent.LocalAlgebra.CyclicPrimeFactor
import OAI.NumberTheory.PiExponent.Polynomials.HomogeneousPrimeFactor

namespace OAI

namespace PiExponentJets.W22

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k]

def HomogeneousPrimeStep (I J : Ideal (MvPolynomial σ k)) : Prop :=
  I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) ∧
    ∃ (d : ℕ) (f : MvPolynomial σ k), f.IsHomogeneous d ∧ f ∉ I ∧
      (I.colon {f}).IsPrime ∧ J = I ⊔ Ideal.span {f}

theorem HomogeneousPrimeStep.homogeneous {I J : Ideal (MvPolynomial σ k)}
    (h : HomogeneousPrimeStep I J) :
    J.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) := by
  obtain ⟨hI, d, f, hf, _, _, rfl⟩ := h
  apply hI.sup
  apply Ideal.homogeneous_span (MvPolynomial.homogeneousSubmodule σ k)
  intro x hx
  obtain rfl := Set.mem_singleton_iff.mp hx
  exact ⟨d, hf⟩

theorem HomogeneousPrimeStep.lt {I J : Ideal (MvPolynomial σ k)}
    (h : HomogeneousPrimeStep I J) : I < J := by
  obtain ⟨_, d, f, _, hfI, _, rfl⟩ := h
  refine lt_of_le_of_ne le_sup_left ?_
  intro heq
  have hm : f ∈ I ⊔ Ideal.span {f} :=
    (show Ideal.span {f} ≤ I ⊔ Ideal.span {f} from le_sup_right)
      (Ideal.subset_span (by simp))
  exact hfI (by simpa only [← heq] using hm)

theorem HomogeneousPrimeStep.isQuotientEquivQuotientPrime
    {I J : Ideal (MvPolynomial σ k)} (h : HomogeneousPrimeStep I J) :
    I.IsQuotientEquivQuotientPrime J := by
  obtain ⟨_, d, f, _, _, hp, rfl⟩ := h
  exact ⟨le_sup_left, ⟨⟨I.colon {f}, hp⟩, ⟨(cyclicFactorEquiv I f).symm⟩⟩⟩

variable [Finite σ]

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

end PiExponentJets.W22

end OAI
