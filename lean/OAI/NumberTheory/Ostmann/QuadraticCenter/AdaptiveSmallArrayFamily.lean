import OAI.NumberTheory.Ostmann.QuadraticCenter.AdaptiveSmallArrayEnergy
import OAI.NumberTheory.Ostmann.QuadraticCenter.AdaptiveSmallArrayGrid

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

def adaptiveActualSmallArray (L M : ℕ) (lam : ℝ) (A : ∀ p : ℕ, Finset (ZMod p))
    (R : ℝ) (h : ℤ) (θ : ℝ) (s : ℕ) : ℂ := by
  classical
  exact if s ∈ adaptiveSmallSupport L then
    positiveDivisorArray L M lam A (adaptiveInverse M) 1 R h θ s else 0

theorem adaptiveSmallArray_l1 {L Z : ℕ} (hL : Squarefree L) (hZ : 1 ≤ Z)
    (hLZ : L ≤ Z) (hC : cutoffFourierBound ≤ (Z:ℝ)) {lam : ℝ} (hlam : |lam| ≤ 1)
    (A : ∀ p : ℕ, Finset (ZMod p)) {a : AdaptiveArrayParameters}
    (ha : a ∈ adaptiveSmallBaseParameters L Z) :
    ∑ s ∈ adaptiveSmallSupport L,‖adaptiveSmallArray L lam A a s‖ ≤ (Z:ℝ)^430 := by
  classical
  have ha0 := (Finset.mem_filter.mp ha).1
  have haP := (Finset.mem_filter.mp ha).2.1
  let b := adaptiveContinuousArray L Z a.modulusResidue a.phaseResidue a.multiple lam A a.theta a.radius
  have hb : b ∈ adaptiveArrayFamily L Z lam A := Finset.mem_image.mpr ⟨a,ha0,rfl⟩
  calc
    _ = ∑ s ∈ adaptiveSmallSupport L,‖b s‖ := by
      apply Finset.sum_congr rfl
      intro s hs
      simp only [b,adaptiveSmallArray,adaptiveContinuousArray,ite_eq_left hs,
        ite_eq_left (adaptiveSmallSupport_subset hZ hLZ hs),haP]
    _ ≤ ∑ s ∈ adaptiveArraySupport L Z,‖b s‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg (adaptiveSmallSupport_subset hZ hLZ)
        (fun s _ _ => norm_nonneg _)
    _ ≤ _ := adaptiveArrayFamily_l1 hL hZ hLZ hC hlam A hb

theorem adaptiveSmallArrayFamily_polynomial {L Z : ℕ} (hL : Squarefree L) (hZ : 2 ≤ Z)
    (hLZ : L ≤ Z) (hC : cutoffFourierBound ≤ (Z:ℝ)) {lam : ℝ} (hlam : |lam| ≤ 1)
    (A : ∀ p : ℕ, Finset (ZMod p)) :
    (adaptiveSmallArrayFamily L Z lam A).card ≤ Z^430 ∧
      ∀ b ∈ adaptiveSmallArrayFamily L Z lam A,∑ s ∈ adaptiveSmallSupport L,‖b s‖ ≤ (Z:ℝ)^430 := by
  classical
  refine ⟨Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans
    (adaptiveArrayParameters_card hZ hLZ)),?_⟩
  intro b hb
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
  exact adaptiveSmallArray_l1 hL (by omega) hLZ hC hlam A ha

theorem adaptiveOffEventArrayFamily_subset (L Z : ℕ) (lam : ℝ)
    (A : ∀ p : ℕ, Finset (ZMod p)) (K : ℝ) :
    adaptiveOffEventArrayFamily L Z lam A K ⊆ adaptiveSmallArrayFamily L Z lam A := by
  classical
  exact Finset.image_subset_image (Finset.filter_subset _ _)

theorem adaptiveOffEventArrayFamily_polynomial {L Z : ℕ} (hL : Squarefree L) (hZ : 2 ≤ Z)
    (hLZ : L ≤ Z) (hC : cutoffFourierBound ≤ (Z:ℝ)) {lam : ℝ} (hlam : |lam| ≤ 1)
    (A : ∀ p : ℕ, Finset (ZMod p)) (K : ℝ) :
    (adaptiveOffEventArrayFamily L Z lam A K).card ≤ Z^430 ∧
      ∀ b ∈ adaptiveOffEventArrayFamily L Z lam A K,
        ∑ s ∈ adaptiveSmallSupport L,‖b s‖ ≤ (Z:ℝ)^430 := by
  have hh := adaptiveSmallArrayFamily_polynomial hL hZ hLZ hC hlam A
  have hsub := adaptiveOffEventArrayFamily_subset L Z lam A K
  exact ⟨(Finset.card_le_card hsub).trans hh.1,fun b hb => hh.2 b (hsub hb)⟩

theorem exists_near_adaptiveOffEventArrayFamily {L Z M : ℕ} (hL : Squarefree L)
    (hZ : 1 ≤ Z) (hLZ : L ≤ Z) (hC : adaptiveArrayConstant ≤ (Z:ℝ)) (hM : Odd M)
    {lam : ℝ} (hlam : |lam| ≤ 1) (A : ∀ p : ℕ, Finset (ZMod p)) (h : ℤ)
    {θ R K : ℝ} (ht0 : 0 ≤ θ) (ht1 : θ ≤ 1)
    (hRlo : (L^6:ℕ) ≤ R) (hRhi : R ≤ (2*Z^13:ℕ))
    (hK : 10 ≤ K) (hKlog : K ≤ Real.log (Z:ℝ))
    (hno : adaptiveNoSmallWitness L M A R h θ K) :
    ∃ a ∈ adaptiveOffEventParameters L Z A K,
      adaptiveSmallArray L lam A a ∈ adaptiveOffEventArrayFamily L Z lam A K ∧
      ∀ s : ℕ,‖adaptiveActualSmallArray L M lam A R h θ s-adaptiveSmallArray L lam A a s‖ ≤
        (Z:ℝ)^(-(80:ℝ)) := by
  classical
  obtain ⟨a,ha,hMa,hha,hta,hRa⟩ := exists_near_adaptiveOffEventParameters hL hZ hLZ hC A h
    ht0 ht1 hRlo hRhi hK hKlog hno
  have habase := (Finset.mem_filter.mp ha).1
  have hab := mem_adaptiveArrayParameters (Finset.mem_filter.mp habase).1 (by omega)
  refine ⟨a,ha,Finset.mem_image.mpr ⟨a,ha,rfl⟩,?_⟩
  intro s
  by_cases hs : s ∈ adaptiveSmallSupport L
  · simp only [adaptiveActualSmallArray,adaptiveSmallArray,ite_eq_left hs]
    rw [positiveDivisorArray_canonical_reduction hL hM,hMa,hha]
    have hsI := Finset.mem_Icc.mp (Finset.mem_filter.mp (adaptiveSmallSupport_subset hZ hLZ hs)).1
    have hRone : (1:ℝ) ≤ R := (show (1:ℝ) ≤ (L^6:ℕ) from by exact_mod_cast Nat.one_le_pow 6 L hL.ne_zero.bot_lt).trans hRlo
    exact (positiveDivisorArray_grid_error hL hZ hLZ hsI.1 hsI.2 (M%(4*L)) 1 hlam A
      (adaptiveInverse (M%(4*L))) hRone hab.2.2.2.2.2.2.1 hRhi hab.2.2.2.2.2.2.2
      (adaptivePhaseResidue L h) hta hRa).trans (adaptiveArray_error_le hZ hC)
  · simp only [adaptiveActualSmallArray,adaptiveSmallArray,ite_eq_right hs,sub_self,norm_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem adaptiveOffEventArrayFamily_energy {L Z : ℕ} (hL : Squarefree L)
    {lam u : ℝ} (hlam : 0 ≤ lam) (hu : 0 ≤ u)
    (A : ∀ p : ℕ, Finset (ZMod p)) (K : ℝ) {b : ℕ → ℂ}
    (hb : b ∈ adaptiveOffEventArrayFamily L Z lam A K) :
    (∑ s ∈ adaptiveSmallSupport L,u^s.primeFactors.card*‖b s‖^2) ≤
      Real.exp (-(9/5:ℝ)*K)*(1+Real.sqrt 2*lam)^(2*L.primeFactors.card)*
        (reciprocalSqrtDivisorSum L)^2*adaptiveSmallEuler L u := by
  classical
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
  exact adaptiveOffEventArray_energy hL hlam hu A K ha

theorem adaptiveSmallArrayFamily_energy {L Z : ℕ} (hL : Squarefree L)
    {lam u : ℝ} (hlam : 0 ≤ lam) (hu : 0 ≤ u)
    (A : ∀ p : ℕ, Finset (ZMod p)) {b : ℕ → ℂ}
    (hb : b ∈ adaptiveSmallArrayFamily L Z lam A) :
    (∑ s ∈ adaptiveSmallSupport L,u^s.primeFactors.card*‖b s‖^2) ≤
      (2*cutoffFourierBound)^2*(1+Real.sqrt 2*lam)^(2*L.primeFactors.card)*
        (reciprocalSqrtDivisorSum L)^2*adaptiveSmallEuler L u := by
  classical
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
  exact adaptiveSmallArray_energy hL hlam hu A ha

end Ostmann.QuadraticCenter

end

end OAI
