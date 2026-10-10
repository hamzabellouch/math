import OAI.NumberTheory.PiExponent.Geometry.ProperHypersurfaceHilbert
import OAI.NumberTheory.PiExponent.LocalAlgebra.ComponentMultiplicitySum
import OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertComparison

namespace OAI

namespace PiExponentJets.W22

open PiExponentJets.W64
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

end PiExponentJets.W22

end OAI
