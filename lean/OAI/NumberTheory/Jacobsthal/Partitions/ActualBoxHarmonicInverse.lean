import OAI.NumberTheory.Jacobsthal.Analysis.TripleWeightDensity
import OAI.NumberTheory.Jacobsthal.Sieve.ActualCofactorArithmetic

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseCells
open ErdosInverseSampling
attribute [local instance] Classical.decEq

theorem retained_initial_cell (P Q U : Finset ℕ) (a : ℕ → ℕ) (B xi Z sigma : ℝ) (k M0 : ℕ) [NeZero M0]
    (hB : 0 < B) (hxi : 0 < xi) (hxi1 : xi ≤ 1) (hZ : 0 < Z) (hsigma : 0 ≤ sigma)
    (hQ : ∀ q ∈ Q,B/(1+xi)^k ≤ (q : ℝ) ∧ (q : ℝ) ≤ B)
    (witness : (ℕ × ℕ) → ℕ → Prop) (hPpos : 0 < harmonicMass P) (hUpos : 0 < harmonicMass U)
    (hPspread : ∀ p ∈ P,∀ r ∈ P,(p : ℝ)⁻¹ ≤ (1+xi)*(r : ℝ)⁻¹)
    (hUspread : ∀ u ∈ U,∀ r ∈ U,(u : ℝ)⁻¹ ≤ (1+xi)*(r : ℝ)⁻¹)
    (hBad : sigma*(harmonicMass P*harmonicMass Q*harmonicMass U) < weightedWitness P Q U witness)
    (hDiscard : (∑ q ∈ discardedPoints Q (initialLabel a B xi k M0) (B/Z),(q : ℝ)⁻¹) ≤
      (sigma/2)*(∑ q ∈ Q,(q : ℝ)⁻¹)) :
    ∃ i : InitialLabel k M0,B/Z ≤ ((initialCell Q a B xi k M0 i).card : ℝ) ∧
      (initialCell Q a B xi k M0 i).Nonempty ∧
      (sigma/16)*((P.product (initialCell Q a B xi k M0 i)).card : ℝ)*(U.card : ℝ) ≤
        ((witnessPairs (P.product (initialCell Q a B xi k M0 i)) U witness).card : ℝ) := by
  have hDen := mul_pos hPpos hUpos
  have hCond := condition_harmonic_density P Q U witness sigma hDen hBad
  obtain ⟨i,hlarge,hdense⟩ := exists_dense_retained_fiber Q (initialLabel a B xi k M0) (B/Z) sigma hsigma
    (fun q => (q : ℝ)⁻¹) (fun q => (q : ℝ)⁻¹*conditionalReward P U witness q)
    (fun _ _ => by positivity) (fun q _ => conditioned_reward_upper P U witness hDen q) hCond hDiscard
  have hcardR : (0 : ℝ) < (initialCell Q a B xi k M0 i).card := (div_pos hB hZ).trans_le hlarge
  have hcard : 0 < (initialCell Q a B xi k M0 i).card := by exact_mod_cast hcardR
  have hne := Finset.card_pos.mp hcard
  have hCpos : 0 < harmonicMass (initialCell Q a B xi k M0 i) := by
    apply harmonicMass_pos _ hne
    intro q hq
    exact_mod_cast (initial_cell_interval Q a B xi k M0 hB hxi hQ i q hq).2.1
  have hWeighted := uncondition_harmonic_density P (initialCell Q a B xi k M0 i) U witness (sigma/2) hDen hdense
  exact ⟨i,hlarge,hne,triple_weighted_to_count P (initialCell Q a B xi k M0 i) U xi sigma hxi.le hxi1
    witness hPpos hCpos hUpos hPspread
    (fun q hq r hr => initial_cell_weight_spread Q a B xi k M0 hB hxi hQ i q r hq hr) hUspread hWeighted.le⟩

end ErdosInverseCells

end

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseCells
open NumberTheoryLean ErdosCofactorChoices ErdosInverseBoxHeight ErdosInverseEuler ErdosInversePrimeBin ErdosInverseSampleCost ErdosInverseSampling
open NumberTheoryLean.LogarithmicBinScale

theorem source_dense_initial_cell (C xi sigma alpha delta cp : ℝ) (hC : 0 ≤ C)
    (hxi : 0 < xi) (hxi1 : xi ≤ 1) (hsigma : 0 < sigma) (halpha : 0 < alpha) :
    ∀ᶠ z : ℝ in atTop,1 < z ∧ ∀ R thetaP U thetaU : ℝ,
      z^alpha ≤ R → sourceW z ≤ U → xi/4 ≤ thetaP → thetaP ≤ xi → xi/4 ≤ thetaU → thetaU ≤ xi →
      ∀ (m : Fin (binCount (sourceW z) z xi) → ℕ) (a : ℕ → ℕ),
        ((∑ j,m j : ℕ) : ℝ) ≤ C*Real.log (sourceB z) →
        let Q := cofactorChoices (actualBins z xi) m
        let S := cofactorScale z xi m
        let k := ∑ j,m j
        let P := primeBin R thetaP
        let Uset := primeBin U thetaU
        let M0 := smallModulus (sourceW z)
        let witness := actualWitness (sourceY z) (LargePrimeDeletion.cutoffPrimes ⌊sourceW z⌋₊) a delta
          (SmallSieveFinite.smallEuler ⌊sourceW z⌋₊) P S R (sourceZ z) cp
        sigma*(harmonicMass P*harmonicMass Q*harmonicMass Uset) < weightedWitness P Q Uset witness →
        ∃ (i : InitialLabel k M0) (q0 : ℕ),
          q0 ∈ initialCell Q a S xi k M0 i ∧
          S/sourceZ z ≤ ((initialCell Q a S xi k M0 i).card : ℝ) ∧
          (sigma/16)*((P.product (initialCell Q a S xi k M0 i)).card : ℝ)*(Uset.card : ℝ) ≤
            ((witnessPairs (P.product (initialCell Q a S xi k M0 i)) Uset witness).card : ℝ) ∧
          (initialCell Q a S xi k M0 i ⊆ Q) ∧
          ∀ q ∈ initialCell Q a S xi k M0 i,
            0 < q ∧ Squarefree q ∧ (q : ℝ) ≤ cellUpper S xi i ∧ cellUpper S xi i ≤ (1+xi)*(q : ℝ) ∧
              Int.ModEq (M0 : ℤ) (q : ℤ) (q0 : ℤ) ∧
              Int.ModEq (M0 : ℤ) (cofactorHit q a : ℤ) (cofactorHit q0 a : ℤ) := by
  filter_upwards [source_initial_discard_small C xi (sigma/2) hC hxi hxi1 (by positivity),
    source_cofactor_cell_data C xi 1 hC hxi hxi1 zero_lt_one,source_span_geometry,
    source_sample_population xi 1 0 hxi hxi1,sourceW_le_power alpha halpha,eventually_gt_atTop (1 : ℝ)]
    with z hdiscard hdata hspan hpop hWR hz
  refine ⟨hz,?_⟩
  intro R thetaP U thetaU hR hWU hPlow hPhigh hUlow hUhigh m a hm
  dsimp only
  intro hBad
  let Q := cofactorChoices (actualBins z xi) m
  let S := cofactorScale z xi m
  let k := ∑ j,m j
  let P := primeBin R thetaP
  let Uset := primeBin U thetaU
  let M0 := smallModulus (sourceW z)
  let witness := actualWitness (sourceY z) (LargePrimeDeletion.cutoffPrimes ⌊sourceW z⌋₊) a delta
    (SmallSieveFinite.smallEuler ⌊sourceW z⌋₊) P S R (sourceZ z) cp
  let : NeZero M0 := ⟨(smallModulus_pos _).ne'⟩
  have hd := hdata m hm
  have hZ : 0 < sourceZ z := Real.exp_pos _
  have hzpos : 0 < z := by linarith
  have hRpos : 0 < R := (Real.rpow_pos_of_pos hzpos alpha).trans_le hR
  have hUpos : 0 < U := hspan.1.trans_le hWU
  have hthetaP : 0 ≤ thetaP := (by positivity : (0 : ℝ) ≤ xi/4).trans hPlow
  have hthetaU : 0 ≤ thetaU := (by positivity : (0 : ℝ) ≤ xi/4).trans hUlow
  have hPn : P.Nonempty := Finset.card_pos.mp (hpop R thetaP (hWR.trans hR) hPlow hPhigh).1
  have hUn : Uset.Nonempty := Finset.card_pos.mp (hpop U thetaU hWU hUlow hUhigh).1
  have hPmass : 0 < harmonicMass P := harmonicMass_pos P hPn
    (fun p hp => ((mem_primeBin hRpos.le hthetaP p).mp hp).1.pos)
  have hUmass : 0 < harmonicMass Uset := harmonicMass_pos Uset hUn
    (fun u hu => ((mem_primeBin hUpos.le hthetaU u).mp hu).1.pos)
  have hQrange : ∀ q ∈ Q,S/(1+xi)^k ≤ (q : ℝ) ∧ (q : ℝ) ≤ S :=
    fun q hq => actual_cofactor_range hspan.1 hspan.2.1 hxi m q hq
  have hDisc : (∑ q ∈ discardedPoints Q (initialLabel a S xi k M0) (S/sourceZ z),(q : ℝ)⁻¹) ≤
      (sigma/2)*(∑ q ∈ Q,(q : ℝ)⁻¹) := hdiscard m a hm
  obtain ⟨i,hlarge,hne,hDense⟩ := retained_initial_cell P Q Uset a S xi (sourceZ z) sigma k M0
    hd.1 hxi hxi1 hZ hsigma.le hQrange witness hPmass hUmass
    (prime_bin_weight_spread R thetaP xi hRpos hthetaP hxi.le hPhigh)
    (prime_bin_weight_spread U thetaU xi hUpos hthetaU hxi.le hUhigh) hBad hDisc
  obtain ⟨q0,hq0⟩ := hne
  refine ⟨i,q0,hq0,hlarge,hDense,labelFiber_subset Q (initialLabel a S xi k M0) i,?_⟩
  intro q hq
  have hqQ := (mem_initialCell Q a S xi k M0 i q).mp hq |>.1
  have hqs := hd.2.2.2 q hqQ
  have hinterval := initial_cell_interval Q a S xi k M0 hd.1 hxi hQrange i q hq
  have hcong := initial_cell_congruences Q a S xi k M0 i q q0 hq hq0
  exact ⟨hqs.1,hqs.2,hinterval.2.2.1,hinterval.2.2.2,hcong.1,hcong.2⟩

end ErdosInverseCells

end

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseBoxApplication
open NumberTheoryLean ErdosCofactorChoices ErdosInverseCells ErdosInverseRefinement
  ErdosInverseBoxHeight ErdosInverseEuler ErdosInverseSampleCost ErdosInverseSampling
open NumberTheoryLean.LogarithmicBinScale NumberTheoryLean.LogarithmicBinEndpoints

theorem actual_box_nonstructured_harmonic (Clen Cparent aStar K alpha delta sigma : ℝ) (h : ℕ)
    (hClen : 0 ≤ Clen) (hCparent : 0 ≤ Cparent) (ha : 0 < aStar) (ha1 : aStar ≤ 1)
    (hK : 0 ≤ K) (halpha : 0 < alpha) (hd : 0 < delta) (hsigma : 0 < sigma) (hsigma1 : sigma ≤ 1)
    (hh : 12 < aStar*(h : ℝ)/2) :
    ∃ xi0 : ℝ,0 < xi0 ∧ xi0 ≤ 1 ∧ ∀ xi : ℝ,0 < xi → xi ≤ xi0 →
      ∀ᶠ z : ℝ in atTop,
        ∀ (m : Fin (binCount (sourceW z) z xi) → ℕ)
          (i j : Fin (binCount (sourceW z) z xi)),
          i ≠ j → m i = 0 → m j = 0 →
          ((∑ k,m k : ℕ) : ℝ) ≤ Clen*Real.log (sourceB z) →
          ∀ a : ℕ → ℕ,
          let R := lower (sourceW z) z xi i
          let U := lower (sourceW z) z xi j
          let P := actualBins z xi i
          let Uset := actualBins z xi j
          let Q := cofactorChoices (actualBins z xi) m
          let S := cofactorScale z xi m
          z^alpha ≤ R → R ≤ z^((1 : ℝ)/100) → U ≤ (sourceW z)^K →
          (∀ q ∈ Q,∀ p ∈ P,
            Real.logb (sourceW z) ((sourceY z : ℝ)/((p : ℝ)*q)) ≤ Cparent) →
          (∀ q ∈ Q,∀ p ∈ P,∀ u ∈ Uset,
            3*aStar/4 ≤ Real.log ((sourceY z : ℝ)/((p : ℝ)*q*u))/Real.log (sourceW z)) →
          weightedWitness P Q Uset
            (actualWitness (sourceY z) (LargePrimeDeletion.cutoffPrimes ⌊sourceW z⌋₊) a delta
              (SmallSieveFinite.smallEuler ⌊sourceW z⌋₊) P S R (sourceZ z) (sampleGamma (sigma/16) h/32)) ≤
            sigma*(harmonicMass P*harmonicMass Q*harmonicMass Uset) := by
  have hb : 0 < sigma/16 := by positivity
  have hb1 : sigma/16 ≤ 1 := by linarith
  obtain ⟨xi0,hxi0,hxi01,hNo⟩ := source_no_dense_cell Clen Cparent aStar K alpha delta (sigma/16) h
    hClen hCparent ha ha1 hK halpha hd hb hb1 hh
  refine ⟨xi0,hxi0,hxi01,?_⟩
  intro xi hxi hxib
  have hxi1 : xi ≤ 1 := hxib.trans hxi01
  filter_upwards [hNo xi hxi hxib,
    source_dense_initial_cell Clen xi sigma alpha delta (sampleGamma (sigma/16) h/32)
      hClen hxi hxi1 hsigma halpha,source_span_geometry]
    with z hno hdense hspan
  intro m i j hij hmi hmj hm a
  dsimp only
  intro hRlo hRhi hUhi hparent hchild
  let R := lower (sourceW z) z xi i
  let U := lower (sourceW z) z xi j
  let theta := effectiveWidth (sourceW z) z xi
  let P := actualBins z xi i
  let Uset := actualBins z xi j
  let Q := cofactorChoices (actualBins z xi) m
  let S := cofactorScale z xi m
  let k := ∑ t,m t
  let M0 := smallModulus (sourceW z)
  have hthetaLow : xi/4 ≤ theta :=
    effectiveWidth_ge_quarter hspan.1 hspan.2.1 hxi hxi1 (hspan.2.2 xi hxi hxi1)
  have hthetaHigh : theta ≤ xi := effectiveWidth_le hspan.1 hspan.2.1 hxi
  have hWU : sourceW z ≤ U := (bin_source_bounds hspan.1 hspan.2.1 hxi j).1
  by_contra hn
  have hBad := lt_of_not_ge hn
  obtain ⟨cell,q0,hq0,hCsize,hCount,hCQ,hdata⟩ := hdense.2 R theta U theta hRlo hWU
    hthetaLow hthetaHigh hthetaLow hthetaHigh m a hm hBad
  let C := initialCell Q a S xi k M0 cell
  have hq0Q : q0 ∈ Q := hCQ hq0
  have hq0data := hdata q0 hq0
  have hInfl := (actual_source_cofactor_inflation hspan.1 hspan.2.1 hxi Clen m hm q0 hq0Q).2
  have hCsq : ∀ q ∈ C,Squarefree q ∧ (q : ℝ) ≤ S := by
    intro q hq
    exact ⟨(hdata q hq).2.1,(actual_cofactor_effective_range hspan.1 hspan.2.1 hxi m q (hCQ hq)).2⟩
  have hCvalue : ∀ q ∈ C,(q : ℝ) ≤ cellUpper S xi cell ∧
      cellUpper S xi cell ≤ (1+xi)*(q : ℝ) := fun q hq =>
    ⟨(hdata q hq).2.2.1,(hdata q hq).2.2.2.1⟩
  have hCP : ∀ q ∈ C,∀ p ∈ P,q.Coprime p :=
    fun q hq => actual_excluded_bin_coprime hspan.1 hspan.2.1 hxi m i hmi q (hCQ hq)
  have hCU : ∀ q ∈ C,∀ u ∈ Uset,q.Coprime u :=
    fun q hq => actual_excluded_bin_coprime hspan.1 hspan.2.1 hxi m j hmj q (hCQ hq)
  have hpU : ∀ p ∈ P,∀ u ∈ Uset,p.Coprime u :=
    actual_distinct_bins_coprime hspan.1 hspan.2.1 hxi i j hij
  have hsmall : ∀ q ∈ C,∀ p ∈ P,∀ t : ℕ,t.Prime →
      (t : ℝ) ≤ sourceW z → (p*q).Coprime t :=
    fun q hq p hp => actual_parent_small_coprime hspan.1 hspan.2.1 hxi m q (hCQ hq) i p hp
  have hcong : ∀ q ∈ C,Int.ModEq (M0 : ℤ) (q : ℤ) (q0 : ℤ) ∧
      Int.ModEq (M0 : ℤ) (cofactorHit q a : ℤ) (cofactorHit q0 a : ℤ) :=
    fun q hq => (hdata q hq).2.2.2.2
  exact hno R theta U theta (cellUpper S xi cell) S C q0 (cofactorHit q0 a) a
    hRlo hRhi hWU hUhi hthetaLow hthetaHigh hthetaLow hthetaHigh hq0 hq0data.1 hInfl
    hCsq hCvalue hpU hCP hCU hsmall (fun q hq => hchild q (hCQ hq))
    (hparent q0 hq0Q) hcong hCsize hCount

end ErdosInverseBoxApplication

end

end Erdos970

end OAI
