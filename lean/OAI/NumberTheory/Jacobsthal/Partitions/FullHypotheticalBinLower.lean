import OAI.NumberTheory.Jacobsthal.Estimates.SubbinAggregation
import OAI.NumberTheory.Jacobsthal.Estimates.SubbinScaleInheritance
import OAI.NumberTheory.Jacobsthal.Primes.PrimeWordArithmetic

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosStoppedArithmetic
open ErdosStoppedTagSieve Erdos970Dependency.SiegelWalfisz
  ErdosCommonMInterval ErdosInverseAlignment ErdosInversePrimeBin
  ErdosPrimeInputs.MertensStrong ErdosTagSubbins ErdosStoppedSubbinAggregation
  NumberTheoryLean.ReferenceProductsBasics

attribute [local instance] Classical.propDecidable

theorem hypothetical_full_bin_lower (Cs : ℝ) (hCs : 0 ≤ Cs) :
    ∃ K : ℝ,0 < K ∧ ∀ rho xi : ℝ,1 < rho → 0 < xi →
      ∃ w0 : ℝ,4 ≤ w0 ∧ ∀ w : ℝ,w0 ≤ w → ∀ P R theta : ℝ,
      Real.exp (K*(Real.log w)^3) ≤ P → P ≤ Real.exp (rho*K*(Real.log w)^3) →
      Real.exp (w^((1:ℝ)/4)*Real.log w) ≤ R → xi/4 ≤ theta → theta ≤ 1 →
      ∀ Y q : ℕ,0 < Y → 0 < q → ∀ r : ℚ,∀ a : ℕ → ℕ,
      (r.den : ℝ) ≤ w^Cs → |(r.num : ℝ)| ≤ (Y : ℝ)*w^(Cs+2) →
      (∀ x ∈ Set.Icc R ((1+theta)*R),
        203/100 ≤ lengthExponent P Y x q ∧ lengthExponent P Y x q ≤ 219/100) →
      (∀ t ∈ smallPrimeSet P,q.Coprime t) →
      (∀ p ∈ primeBin R theta,Squarefree (p*q) ∧ r.den.Coprime p ∧
        p ∉ smallPrimeSet P ∧ ∀ t ∈ (p*q).primeFactors,t ≠ p →
          aligns (fun u => (a u : ℤ)) r t) →
      (39/100 : ℝ)*primeProduct P*(∑ p ∈ primeBin R theta,(Y : ℝ)/((p : ℝ)*q)) ≤
        ∑ p ∈ primeBin R theta,primeHypothetical Y (smallPrimeSet P) a r q p := by
  obtain ⟨K,hK,hSub⟩ := hypothetical_subbin_lower Cs hCs
  refine ⟨K,hK,?_⟩
  intro rho xi hrho hxi
  obtain ⟨w0,hw0,hS⟩ := hSub rho xi hrho hxi
  refine ⟨w0,hw0,?_⟩
  intro w hw P R theta hPl hPu hR hThetaLo hThetaHi Y q hY hq r a hDen hNum hBand hqSmall hGeometry
  have hw1 : 1 < w := by linarith [hw0.trans hw]
  have hR0 : 0 < R := (Real.exp_pos _).trans_le hR
  have ht : 0 < theta := (div_pos hxi (by norm_num)).trans_le hThetaLo
  have hN : 0 < count w Cs := (count_bounds hw1 hCs).1
  apply aggregate_reference_lower (N:=count w Cs) hR0 ht hN (Nat.cast_nonneg Y)
    (show (0 : ℝ) < q by exact_mod_cast hq) (actual_primeProduct_pos P).le
    (primeHypothetical Y (smallPrimeSet P) a r q)
  intro i
  obtain ⟨_hLeft,_hStep,hRSub,_hLeftHi,hVlo,hVhi,_hRight⟩ :=
    subbin_scale_inheritance hw1 hCs hR0 hxi hThetaLo hThetaHi hR i
  have hBandSub := subbin_inherits_band hR0 ht hN
    (fun x => 203/100 ≤ lengthExponent P Y x q ∧ lengthExponent P Y x q ≤ 219/100) hBand i
  have hGeomSub : ∀ p ∈ intervalPrimes (left R theta (count w Cs) i)
      (step R theta (count w Cs)) 1 0,Squarefree (p*q) ∧ r.den.Coprime p ∧
      p ∉ smallPrimeSet P ∧ ∀ t ∈ (p*q).primeFactors,t ≠ p → aligns (fun u => (a u : ℤ)) r t := by
    intro p hp
    have hpSub : p ∈ subbin R theta (count w Cs) i := by
      rwa [subbin_eq_intervalPrimes hR0 ht hN]
    exact hGeometry p (subbin_subset hR0 ht i.isLt hpSub)
  have hh := hS w hw P (left R theta (count w Cs) i) (step R theta (count w Cs))
    hPl hPu hRSub hVlo hVhi Y q hY hq r a hDen hNum hBandSub.1 hBandSub.2 hqSmall hGeomSub
  rw [← primeHypothetical_sum] at hh
  rw [subbin_eq_intervalPrimes hR0 ht hN]
  exact hh

end ErdosStoppedArithmetic


end Erdos970

end OAI
