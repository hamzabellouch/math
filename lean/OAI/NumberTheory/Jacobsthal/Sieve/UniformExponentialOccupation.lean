import OAI.NumberTheory.Jacobsthal.Analysis.UncappedCompactMass

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.UniformExponentialOccupation

attribute [local instance] Classical.propDecidable
open _root_.Set _root_.Finset
open FinitePathGeometry PrimeHistories PrimeBinMembership ActualPrimeHigh
open UncappedCompactMass LiteralUniformPrimeTail LiteralPrimeOccupation
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail

noncomputable def positiveGapEnvelope (c r : ℝ) : ℝ := if 2 ≤ r then Real.exp (-c*r) else 0

noncomputable def exponentialPrefixMass (c w ell : ℝ) (start : Node) : ℝ :=
  ∑ ps ∈ uncappedPrefixes w ell start,prefixWeight ps*positiveGapEnvelope c (terminal w start ps).gap

theorem envelope_nonneg (c r : ℝ) : 0 ≤ positiveGapEnvelope c r := by
  unfold positiveGapEnvelope
  split_ifs <;> positivity

theorem compact_tail_split {c : ℝ} (hc : 0 < c) (K w ell : ℝ) (start : Node) :
    exponentialPrefixMass c w ell start ≤ compactPrefixMass K w ell start+
      ∑ ps ∈ uncappedPrefixes w ell start,prefixWeight ps*tailListReward c K w start ps := by
  unfold exponentialPrefixMass compactPrefixMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ps _hp
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ (prefixWeight_nonneg ps)
  unfold positiveGapEnvelope tailListReward
  by_cases hr : 2 ≤ (terminal w start ps).gap
  · rw [ite_eq_left hr]
    by_cases hK : (terminal w start ps).gap ≤ K
    · rw [ite_eq_left ⟨hr,hK⟩,ite_eq_right (not_lt_of_ge hK)]
      simpa only [add_zero] using Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (by linarith))
    · rw [ite_eq_right (fun h => hK h.2),ite_eq_left (lt_of_not_ge hK),zero_add]
  · rw [ite_eq_right hr,ite_eq_right (fun h => hr h.1),zero_add]
    split_ifs <;> positivity

theorem uniform_exponential_prefix_mass (ell c d : ℝ) (hell : 1 ≤ ell) (hc : 0 < c) (hd : 0 < d) :
    ∃ C B₀ w₀ : ℝ,0 < C ∧ 0 < B₀ ∧ 1 < w₀ ∧ ∀ B w : ℝ,B₀ ≤ B → w₀ ≤ w →
      Real.log B ≤ d*Real.log w → ∀ start : Node,
        start.side=.even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        Consistent start → start.cutoff=B → B^2*exponentialPrefixMass c w ell start ≤ C := by
  obtain ⟨M,BT,wT,hBT,hwT,htail⟩ := actual_uniform_original_prime_tail d c 1 hd hc (by norm_num)
  let K : ℝ := 3*((M:ℝ)+1)
  have hK : 3 ≤ K := by dsimp [K]; have hn := Nat.cast_nonneg (α:=ℝ) M; linarith
  obtain ⟨CC,BC,wC,hCC,hBC,hwC,hcompact⟩ := uniform_uncapped_compact_mass K ell d hK hell hd
  refine ⟨CC+1,max BC (max BT ell),max wC wT,by linarith,
    hBC.trans_le (le_max_left _ _),hwC.trans_le (le_max_left _ _),?_⟩
  intro B w hB hw hcomp start hi h199 h23 hcons hcut
  have hBC' : BC ≤ B := (le_max_left _ _).trans hB
  have hBT' : BT ≤ B := ((le_max_left _ _).trans (le_max_right _ _)).trans hB
  have hellB : ell ≤ B := ((le_max_right _ _).trans (le_max_right _ _)).trans hB
  have hwC' : wC ≤ w := (le_max_left _ _).trans hw
  have hwT' : wT ≤ w := (le_max_right _ _).trans hw
  have ht := htail M le_rfl B w hBT' hwT' ell hell hellB hcomp start hi h199 h23 hcons hcut
  have hcc := hcompact B w hBC' hwC' hcomp start hi h199 h23 hcons hcut
  have hsplit := mul_le_mul_of_nonneg_left (compact_tail_split hc K w ell start) (sq_nonneg B)
  dsimp only [K] at hsplit hcc
  nlinarith

theorem uniform_signed_exponential_rewards (ell c d : ℝ) (hell : 1 ≤ ell) (hc : 0 < c) (hd : 0 < d) :
    ∃ C B₀ w₀ : ℝ,0 < C ∧ 0 < B₀ ∧ 1 < w₀ ∧ ∀ B w : ℝ,B₀ ≤ B → w₀ ≤ w →
      Real.log B ≤ d*Real.log w → ∀ start : Node,
        start.side=.even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        Consistent start → start.cutoff=B → ∀ A : ℝ,0 ≤ A → ∀ F : List ℕ → ℝ,
          (∀ ps ∈ uncappedPrefixes w ell start,|F ps| ≤ A*positiveGapEnvelope c (terminal w start ps).gap) →
          B^2*|∑ ps ∈ uncappedPrefixes w ell start,prefixWeight ps*F ps| ≤ A*C := by
  obtain ⟨C,B₀,w₀,hC,hB₀,hw₀,h⟩ := uniform_exponential_prefix_mass ell c d hell hc hd
  refine ⟨C,B₀,w₀,hC,hB₀,hw₀,?_⟩
  intro B w hB hw hcomp start hi h199 h23 hcons hcut A hA F hF
  have hmass := h B w hB hw hcomp start hi h199 h23 hcons hcut
  have hab : |∑ ps ∈ uncappedPrefixes w ell start,prefixWeight ps*F ps| ≤
      A*exponentialPrefixMass c w ell start := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    rw [exponentialPrefixMass,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ps hp
    rw [abs_mul,abs_of_nonneg (prefixWeight_nonneg ps)]
    have hm := mul_le_mul_of_nonneg_left (hF ps hp) (prefixWeight_nonneg ps)
    convert hm using 1
    ring
  have hm := mul_le_mul_of_nonneg_left hab (sq_nonneg B)
  have hfinal := mul_le_mul_of_nonneg_left hmass hA
  nlinarith

end NumberTheoryLean.UniformExponentialOccupation

end

end Erdos970

end OAI
