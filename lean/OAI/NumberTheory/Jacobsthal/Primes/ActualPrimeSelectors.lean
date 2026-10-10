import OAI.NumberTheory.Jacobsthal.Estimates.ActualModelTargets

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceMoments
open NumberTheoryLean ErdosVarianceSmallModel ErdosVarianceEffective ErdosVarianceCommon
  ErdosInverseCells
attribute [local instance] Classical.propDecidable

theorem actual_primePoint_survives (P : Finset ℕ) (w : ℝ) (a : ℕ → ℕ) (r : ℚ) (qf : ℕ)
    (hq : Squarefree qf) (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hPLarge : ∀ p ∈ P,w < (p : ℝ))
    (hQLarge : ∀ t ∈ qf.primeFactors,w < (t : ℝ)) (p : ℕ) [NeZero p]
    (hpGood : p ∈ goodPrimes P (effectiveModulus a r qf)) (j : ℕ) :
    actualModelSurvives w a r qf j
      (primePoint P w (effectiveModulus a r qf) (effectiveIntercept a r qf) hw hP hPLarge ⟨p,hpGood⟩) ↔
      ∀ t ∈ LargePrimeDeletion.cutoffPrimes ⌊w⌋₊,
        (effectiveInteger a r qf p (Finset.mem_filter.mp hpGood).2 (j : ℤ) : ZMod t) ≠ (a t : ZMod t) := by
  let H := effectiveModulus a r qf
  let C0 := effectiveIntercept a r qf
  let qA := alignedCofactor (fun t => (a t : ℤ)) r qf
  let v := primePoint P w H C0 hw hP hPLarge ⟨p,hpGood⟩
  have hC0 : Int.gcd C0 (H : ℤ) = 1 := effective_coordinates_gcd a r qf hq
  have hHp : H.Coprime p := (Finset.mem_filter.mp hpGood).2
  have h0 (t : ℕ) (ht : t ∈ divisorPrimes w H) :
      (patternKValue w H v.2 t+divisorPhase C0 v.1 t*(j : ZMod t) ≠ actualDivisorTarget a qf t) ↔
        (effectiveInteger a r qf p hHp (j : ℤ) : ZMod t) ≠ (a t : ZMod t) := by
    have htt := (Finset.mem_filter.mp ht).1
    have hprime := (LargePrimeDeletion.mem_cutoffPrimes.mp htt).1
    have htw := (Nat.le_floor_iff hw).mp (LargePrimeDeletion.mem_cutoffPrimes.mp htt).2
    have hqt := full_cofactor_coprime_small qf hq w hQLarge t hprime htw
    have ht0 : t ∣ divisorModulus w H := Finset.dvd_prod_of_mem _ ht
    dsimp only [v]
    rw [primePoint_kValue P w H C0 hw hP hPLarge ⟨p,hpGood⟩ t ht0]
    change ((primeK P H C0 hP ⟨p,hpGood⟩ : ZMod t) +
      divisorPhase C0 (primeM P H C0 hP ⟨p,hpGood⟩) t * (j : ZMod t) ≠ _) ↔ _
    rw [← prime_divisorPhase_eq P H C0 hP hC0 ⟨p,hpGood⟩ t (Finset.mem_filter.mp ht).2]
    have hh := effective_avoidance_unit a r qf p hHp t hqt (j : ℤ)
    simpa [H,C0,primeK,actualDivisorTarget,ZMod.unitOfCoprime] using hh.symm
  have h1 (t : ℕ) (ht : t ∈ coprimePrimes w H) :
      (patternPValue w H v.2 t*(qA : ZMod t)*((v.1 : ZMod t)+(H : ZMod t)*(j : ZMod t)) ≠ actualCoprimeTarget a r t) ↔
        (effectiveInteger a r qf p hHp (j : ℤ) : ZMod t) ≠ (a t : ZMod t) := by
    have htt := (Finset.mem_filter.mp ht).1
    have hprime := (LargePrimeDeletion.mem_cutoffPrimes.mp htt).1
    have ht1 : t ∣ coprimeModulus w H := Finset.dvd_prod_of_mem _ ht
    dsimp only [v]
    rw [primePoint_pValue P w H C0 hw hP hPLarge ⟨p,hpGood⟩ t ht1]
    have hh := effective_avoidance_not_dvd a r qf hq p hHp t hprime (Finset.mem_filter.mp ht).2 (j : ℤ)
    simpa only [H,C0,qA,primePoint,primeM,actualCoprimeTarget,Int.cast_natCast] using hh.symm
  change modelSurvives w H C0 qA (actualDivisorTarget a qf) (actualCoprimeTarget a r) j v ↔ _
  constructor
  · intro hv t ht
    by_cases hdiv : t ∣ H
    · have ht0 : t ∈ divisorPrimes w H := Finset.mem_filter.mpr ⟨ht,hdiv⟩
      exact (h0 t ht0).mp (hv.1 t ht0)
    · have ht1 : t ∈ coprimePrimes w H := Finset.mem_filter.mpr ⟨ht,hdiv⟩
      exact (h1 t ht1).mp (hv.2 t ht1)
  · intro hv
    refine ⟨?_,?_⟩
    · intro t ht
      exact (h0 t ht).mpr (hv t (Finset.mem_filter.mp ht).1)
    · intro t ht
      exact (h1 t ht).mpr (hv t (Finset.mem_filter.mp ht).1)

theorem common_card_eq_model_sum (P : Finset ℕ) (J : ℕ) (w : ℝ) (a : ℕ → ℕ) (r : ℚ) (qf : ℕ)
    (hq : Squarefree qf) (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hPLarge : ∀ p ∈ P,w < (p : ℝ))
    (hQLarge : ∀ t ∈ qf.primeFactors,w < (t : ℝ)) (p : ℕ) [NeZero p]
    (hpGood : p ∈ goodPrimes P (effectiveModulus a r qf)) :
    ((commonSurvivors J w a r qf p (Finset.mem_filter.mp hpGood).2).card : ℝ) =
      ∑ j ∈ Finset.range J,actualModelIndicator w a r qf j
        (primePoint P w (effectiveModulus a r qf) (effectiveIntercept a r qf) hw hP hPLarge ⟨p,hpGood⟩) := by
  classical
  let v := primePoint P w (effectiveModulus a r qf) (effectiveIntercept a r qf) hw hP hPLarge ⟨p,hpGood⟩
  have he : commonSurvivors J w a r qf p (Finset.mem_filter.mp hpGood).2 =
      (Finset.range J).filter (fun j => actualModelSurvives w a r qf j v) := by
    ext j
    simp only [mem_commonSurvivors,Finset.mem_filter,Finset.mem_range]
    exact and_congr Iff.rfl (actual_primePoint_survives P w a r qf hq hw hP hPLarge hQLarge p hpGood j).symm
  rw [he,Finset.natCast_card_filter]
  rfl

end ErdosVarianceMoments

end

end Erdos970

end OAI
