import OAI.NumberTheory.Jacobsthal.Partitions.FullPatternCoordinates

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceLargeMap
open NumberTheoryLean ErdosVarianceSmallModel ErdosVarianceMoments
attribute [local instance] Classical.propDecidable

theorem actualFullPattern_survives (P : Finset ℕ) (w : ℝ) (H qA : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ))
    (hC0 : Int.gcd C0 (H : ℤ) = 1) (beta delta : ∀ t : ℕ,ZMod t)
    (p : goodPrimes P H) (j : ℕ) :
    ErdosLargePatternLaw.survives w H qA beta delta j (actualFullPattern P w H C0 hw hP hlarge p) ↔
      modelSurvives w H C0 qA beta delta j (primePoint P w H C0 hw hP hlarge p) := by
  unfold ErdosLargePatternLaw.survives modelSurvives
  apply and_congr
  · apply forall_congr'
    intro t
    apply forall_congr'
    intro ht
    have ht0 : t ∣ divisorModulus w H := Finset.dvd_prod_of_mem _ ht
    rw [full_k0_projection P w H C0 hw hP hlarge p t ht0,
      full_p0_projection P w H C0 hw hP hlarge p t ht0,
      primePoint_kValue P w H C0 hw hP hlarge p t ht0]
    change ((primeK P H C0 hP p : ZMod t)+(p.val : ZMod t)*(j : ZMod t) ≠ beta t) ↔
      ((primeK P H C0 hP p : ZMod t)+divisorPhase C0 (primeM P H C0 hP p) t*(j : ZMod t) ≠ beta t)
    rw [← prime_divisorPhase_eq P H C0 hP hC0 p t (Finset.mem_filter.mp ht).2]
  · apply forall_congr'
    intro t
    apply forall_congr'
    intro ht
    have ht1 : t ∣ coprimeModulus w H := Finset.dvd_prod_of_mem _ ht
    rw [full_p1_projection P w H C0 hw hP hlarge p t ht1,
      full_m1_projection P w H C0 hw hP hlarge p t ht1,
      primePoint_pValue P w H C0 hw hP hlarge p t ht1]
    rfl

theorem full_count_eq_common (P : Finset ℕ) (J : ℕ) (w : ℝ) (a : ℕ → ℕ) (r : ℚ) (qf : ℕ)
    (hq : Squarefree qf) (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ))
    (hQLarge : ∀ t ∈ qf.primeFactors,w < (t : ℝ)) (p : ℕ) [NeZero p]
    (hpGood : p ∈ goodPrimes P (ErdosVarianceEffective.effectiveModulus a r qf)) :
    ErdosLargePatternLaw.survivorCount w (ErdosVarianceEffective.effectiveModulus a r qf)
      (ErdosVarianceEffective.alignedCofactor (fun t => (a t : ℤ)) r qf) J
      (actualDivisorTarget a qf) (actualCoprimeTarget a r)
      (actualFullPattern P w (ErdosVarianceEffective.effectiveModulus a r qf)
        (ErdosVarianceEffective.effectiveIntercept a r qf) hw hP hlarge ⟨p,hpGood⟩) =
      (ErdosVarianceCommon.commonSurvivors J w a r qf p (Finset.mem_filter.mp hpGood).2).card := by
  unfold ErdosLargePatternLaw.survivorCount
  apply congrArg Finset.card
  ext j
  simp only [Finset.mem_filter,Finset.mem_range,ErdosVarianceCommon.mem_commonSurvivors]
  apply and_congr Iff.rfl
  exact (actualFullPattern_survives P w _ _ _ hw hP hlarge
    (ErdosVarianceEffective.effective_coordinates_gcd a r qf hq)
    (actualDivisorTarget a qf) (actualCoprimeTarget a r) ⟨p,hpGood⟩ j).trans
      (actual_primePoint_survives P w a r qf hq hw hP hlarge hQLarge p hpGood j)

end ErdosVarianceLargeMap

end

end Erdos970

end OAI
