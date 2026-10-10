import OAI.NumberTheory.PiExponent.LocalAlgebra.LocalComponentDegree
import OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedCyclicFactor
import OAI.NumberTheory.PiExponent.LocalAlgebra.SubquotientLength

namespace OAI

namespace PiExponentJets.W22

open scoped BigOperators Classical

variable {R : Type*} [CommRing R]

theorem localized_cyclic_filtration_length
    (I Q : Ideal R) [Q.IsPrime] (hQ : Q ∈ I.minimalPrimes)
    (J : ℕ → Ideal R) (hmono : ∀ i, J i ≤ J (i + 1))
    (hstart : J 0 = I) (n : ℕ) (hend : J n = ⊤)
    (f : ℕ → R)
    (hstep : ∀ i < n, J (i + 1) = J i ⊔ Ideal.span {f i})
    (hprime : ∀ i < n, ((J i).colon {f i}).IsPrime) :
    Module.length (Localization.AtPrime Q)
      (Localization.AtPrime Q ⧸ I.map (algebraMap R (Localization.AtPrime Q))) =
      ∑ i ∈ Finset.range n, if (J i).colon {f i} = Q then 1 else 0 := by
  let L := Localization.AtPrime Q
  let N : ℕ → Ideal L := fun i => (J i).map (algebraMap R L)
  have hNmono : ∀ i, N i ≤ N (i + 1) := fun i => Ideal.map_mono (hmono i)
  have hNtop : N n = ⊤ := by simp only [N, hend, Ideal.map_top]
  have hstartlen := congrArg
    (fun A : Ideal R => Module.length L (L ⧸ A.map (algebraMap R L))) hstart
  have hlen := quotient_length_eq_sum_of_last_top N hNmono n hNtop
  have hbase : I ≤ J 0 := hstart.symm.le
  have hIle : ∀ i, I ≤ J i := fun i =>
    hbase.trans ((monotone_nat_of_le_succ hmono) (Nat.zero_le i))
  calc
    _ = Module.length L (L ⧸ N 0) := hstartlen.symm
    _ = ∑ i ∈ Finset.range n,
        Module.length L (N (i + 1) ⧸ (N i).submoduleOf (N (i + 1))) := hlen
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      have hin : i < n := Finset.mem_range.mp hi
      let := hprime i hin
      have hIP : I ≤ (J i).colon {f i} := by
        intro a ha
        apply Submodule.mem_colon_singleton.mpr
        exact (J i).mul_mem_right (f i) (hIle i ha)
      have heq : Module.length L (N (i + 1) ⧸ (N i).submoduleOf (N (i + 1))) =
          Module.length L (L ⧸ ((J i).colon {f i}).map (algebraMap R L)) := by
        have htransport := congrArg
          (fun K : Ideal R => Module.length L
            (↥(K.map (algebraMap R L)) ⧸
              ((J i).map (algebraMap R L)).submoduleOf (K.map (algebraMap R L))))
          (hstep i hin)
        exact htransport.trans
          (primeLocalizedCyclicFactorEquiv Q (J i) (f i)).symm.length_eq
      rw [heq]
      exact localized_prime_factor_length I ((J i).colon {f i}) Q hQ hIP

end PiExponentJets.W22

end OAI
