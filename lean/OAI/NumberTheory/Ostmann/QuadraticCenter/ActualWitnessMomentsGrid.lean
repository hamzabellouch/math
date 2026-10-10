import OAI.NumberTheory.Ostmann.QuadraticCenter.ActualWitnessMomentsBasic
import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticEnergyNumeric
import OAI.NumberTheory.Ostmann.QuadraticCenter.WitnessArraySplit

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter
open scoped BigOperators

def witnessGridArray (L Z : ℕ) (A : ∀p:ℕ,Finset (ZMod p))
    (a : AdaptiveArrayParameters) : ℕ → ℂ :=
  adaptiveContinuousArray L Z a.modulusResidue a.phaseResidue a.multiple (1/16) A a.theta a.radius

def witnessLargeFamily (L Z : ℕ) (A : ∀p:ℕ,Finset (ZMod p)) : Finset (ℕ → ℂ) := by
  classical
  exact ((adaptiveArrayParameters L Z).filter (fun a => a.multiple=1)).image (witnessGridArray L Z A)

def witnessNontrivialFamily (L Z : ℕ) (A : ∀p:ℕ,Finset (ZMod p)) : Finset (ℕ → ℂ) := by
  classical
  exact ((adaptiveArrayParameters L Z).filter (fun a => Z ≤ a.multiple)).image (witnessGridArray L Z A)

theorem witnessLargeFamily_subset (L Z : ℕ) (A : ∀p:ℕ,Finset (ZMod p)) :
    witnessLargeFamily L Z A ⊆ adaptiveArrayFamily L Z (1/16) A := by
  classical
  exact Finset.image_subset_image (Finset.filter_subset _ _)

theorem witnessNontrivialFamily_subset (L Z : ℕ) (A : ∀p:ℕ,Finset (ZMod p)) :
    witnessNontrivialFamily L Z A ⊆ adaptiveArrayFamily L Z (1/16) A := by
  classical
  exact Finset.image_subset_image (Finset.filter_subset _ _)

theorem witnessLargeSupport_eq (L Z : ℕ) :
    adaptiveArraySupport L Z \ adaptiveSmallSupport L =
      (Finset.Icc (L^4) (Z^14)).filter (fun s => Squarefree s ∧ s.Coprime L) := by
  classical
  ext s
  simp only [adaptiveArraySupport,adaptiveSmallSupport,Finset.mem_sdiff,Finset.mem_filter,
    Finset.mem_Icc,Finset.mem_Ico]
  constructor
  · rintro ⟨⟨⟨hs,hB⟩,hSF,hcop⟩,hn⟩
    exact ⟨⟨by
      by_contra h
      exact hn ⟨⟨hs,by omega⟩,hSF,hcop⟩,hB⟩,hSF,hcop⟩
  · rintro ⟨⟨hL,hB⟩,hSF,hcop⟩
    have hs : 1 ≤ s := by
      by_cases hL0 : L=0
      · subst L
        have hh : s=1 := by simpa only [Nat.coprime_zero_right] using hcop
        omega
      · have := Nat.one_le_pow 4 L (Nat.pos_of_ne_zero hL0)
        omega
    exact ⟨⟨⟨hs,hB⟩,hSF,hcop⟩,by omega⟩

theorem witnessSubfamily_polynomial {L Z : ℕ} (hZ : adaptiveArrayThreshold ≤ Z)
    (hL : Squarefree L) (hLZ : L ≤ Z) (A : ∀p:ℕ,Finset (ZMod p))
    {F : Finset (ℕ → ℂ)} (hF : F ⊆ adaptiveArrayFamily L Z (1/16) A)
    {S : Finset ℕ} (hS : S ⊆ adaptiveArraySupport L Z) :
    F.card ≤ Z^430 ∧ ∀b∈F,∑s∈S,‖b s‖ ≤ (Z:ℝ)^430 := by
  have h := adaptiveArrayFamily_polynomial hZ hL hLZ (by norm_num : |(1/16:ℝ)| ≤ 1) A
  refine ⟨(Finset.card_le_card hF).trans h.1,?_⟩
  intro b hb
  exact (Finset.sum_le_sum_of_subset_of_nonneg hS (fun s _ _ => norm_nonneg (b s))).trans (h.2.1 b (hF hb))

theorem exists_near_witnessGridArray {L Z M P : ℕ} (hL : Squarefree L)
    (hZ : 1 ≤ Z) (hLZ : L ≤ Z) (hC : adaptiveArrayConstant ≤ (Z:ℝ))
    (hM : Odd M) (hP : 1 ≤ P) (hPZ : P ≤ Z^7)
    (A : ∀p:ℕ,Finset (ZMod p)) (h : ℤ) {θ R : ℝ}
    (ht0 : 0 ≤ θ) (ht1 : θ ≤ 1) (hR1 : 1 ≤ R) (hRB : R ≤ (2*Z^13:ℕ)) :
    ∃ a ∈ adaptiveArrayParameters L Z,a.multiple=P ∧
      ∀s∈adaptiveArraySupport L Z,
      ‖positiveDivisorArray L M (1/16) A (adaptiveInverse M) P R h θ s-witnessGridArray L Z A a s‖ ≤
        (Z:ℝ)^(-(80:ℝ)) := by
  have hLp := hL.ne_zero.bot_lt
  obtain ⟨a,ha,hMa,hha,hPa,hta,hRa⟩ := exists_near_adaptiveArrayParameters
    (by omega) (Nat.mod_lt M (by omega : 0 < 4*L)) (adaptivePhaseResidue_lt hLp h) hP hPZ ht0 ht1 hR1 hRB
  have hab := mem_adaptiveArrayParameters ha (by omega)
  refine ⟨a,ha,hPa,?_⟩
  intro s hs
  simp only [witnessGridArray,adaptiveContinuousArray,ite_eq_left hs]
  rw [hMa,hha,hPa,positiveDivisorArray_canonical_reduction hL hM]
  have hsI := Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1
  exact (positiveDivisorArray_grid_error hL hZ hLZ hsI.1 hsI.2 (M%(4*L)) P
    (by norm_num : |(1/16:ℝ)| ≤ 1) A (adaptiveInverse (M%(4*L))) hR1 hab.2.2.2.2.2.2.1
    hRB hab.2.2.2.2.2.2.2 (adaptivePhaseResidue L h) hta hRa).trans (adaptiveArray_error_le hZ hC)

theorem eventually_witnessLargeFamily_energy :
    ∀ᶠ T : ℝ in atTop, ∀ Z z L : ℕ,
      1 ≤ Z → T/2 ≤ Real.log Z → Real.log Z ≤ 2*T →
      1 ≤ z → T^auxiliaryExponent/2 ≤ Real.log z → Real.log z ≤ 2*T^auxiliaryExponent →
      Squarefree L → 2 ≤ L → L.primeFactors.card=auxiliaryK Z z →
      (L:ℝ) ≤ (Z:ℝ)^(1/50:ℝ) → (∀p∈L.primeFactors,z ≤ p) →
      ∀ A : ∀p:ℕ,Finset (ZMod p), ∀b∈witnessLargeFamily L Z A,
      (∑s∈adaptiveArraySupport L Z \ adaptiveSmallSupport L,
        ((((2*gridMomentParameter T:ℕ):ℝ)^2)^s.primeFactors.card)*‖b s‖^2) ≤
      Real.exp ((12/1000:ℝ)*auxiliaryK Z z) := by
  classical
  filter_upwards [positiveDivisorArray_actual_large_energy_eventually] with T hE
  intro Z z L hZ hZl hZu hz hzl hzu hL hL2 hLK hLsize hprimes A b hb
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨ha,hPa⟩ := Finset.mem_filter.mp ha
  have hab := mem_adaptiveArrayParameters ha (by omega)
  have he := hE Z z L a.modulusResidue hZ hZl hZu hz hzl hzu hL hL2 hLK hLsize hprimes
    A (adaptiveInverse a.modulusResidue) a.radius a.phaseResidue a.theta (by linarith [hab.2.2.2.2.2.2.1])
  rw [←witnessLargeSupport_eq] at he
  convert he using 1
  apply Finset.sum_congr rfl
  intro s hs
  simp only [witnessGridArray,adaptiveContinuousArray,ite_eq_left (Finset.mem_sdiff.mp hs).1,hPa]
  push_cast
  rfl

end Ostmann.QuadraticCenter

end

end OAI
