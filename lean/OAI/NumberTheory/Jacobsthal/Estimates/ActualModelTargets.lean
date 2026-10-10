import Mathlib
import OAI.NumberTheory.Jacobsthal.Partitions.EffectiveCommonInterval
import OAI.NumberTheory.Jacobsthal.Sieve.ResidueProjection
import OAI.NumberTheory.Jacobsthal.Sieve.ResidueTailUpper

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceCommon

theorem relative_deviation_iff (N mu eps : ℝ) (hmu : 0 < mu) :
    eps < |N/mu-1| ↔ eps*mu < |N-mu| := by
  have he : N/mu-1 = (N-mu)/mu := by field_simp
  rw [he,abs_div,abs_of_pos hmu,lt_div_iff₀ hmu]

theorem common_deviation_transfer (N mu S M eps A B : ℝ)
    (hM : 0 ≤ M) (hmu : M ≤ mu) (heps : 0 < eps)
    (hN : |N-S| ≤ A*M) (href : |mu-M| ≤ B*M) (hbudget : A+B ≤ eps/2)
    (hbad : eps*mu < |N-mu|) : (eps/2)*M < |S-M| := by
  have htri : |N-mu| ≤ |N-S|+|S-M|+|mu-M| := by
    calc
      _ ≤ |N-S|+|S-mu| := abs_sub_le N S mu
      _ ≤ |N-S|+(|S-M|+|M-mu|) := add_le_add le_rfl (abs_sub_le S M mu)
      _ = _ := by rw [abs_sub_comm M mu];ring
  have hmu' := mul_le_mul_of_nonneg_left hmu heps.le
  have hsum := mul_le_mul_of_nonneg_right hbudget hM
  nlinarith

end ErdosVarianceCommon

end

section

namespace ErdosVarianceMoments
open ErdosVarianceSmallModel
attribute [local instance] Classical.propDecidable

def modelSurvives (w : ℝ) (H : ℕ) (C0 : ℤ) (qA : ℕ)
    (beta delta : ∀ t : ℕ,ZMod t) (j : ℕ) (v : ModelPoint w H) : Prop :=
  (∀ t ∈ divisorPrimes w H,patternKValue w H v.2 t+divisorPhase C0 v.1 t*(j : ZMod t) ≠ beta t) ∧
  (∀ t ∈ coprimePrimes w H,patternPValue w H v.2 t*(qA : ZMod t)*
    ((v.1 : ZMod t)+(H : ZMod t)*(j : ZMod t)) ≠ delta t)

noncomputable def modelIndicator (w : ℝ) (H : ℕ) (C0 : ℤ) (qA : ℕ)
    (beta delta : ∀ t : ℕ,ZMod t) (j : ℕ) (v : ModelPoint w H) : ℝ :=
  if modelSurvives w H C0 qA beta delta j v then 1 else 0

def jointCondition (w : ℝ) (H : ℕ) (C0 : ℤ) (qA : ℕ)
    (beta delta : ∀ t : ℕ,ZMod t) (S : Finset ℕ) (v : ModelPoint w H) : Prop :=
  ∀ j ∈ S,modelSurvives w H C0 qA beta delta j v

noncomputable def jointIndicator (w : ℝ) (H : ℕ) (C0 : ℤ) (qA : ℕ)
    (beta delta : ∀ t : ℕ,ZMod t) (S : Finset ℕ) (v : ModelPoint w H) : ℝ :=
  if jointCondition w H C0 qA beta delta S v then 1 else 0

theorem modelIndicator_binary (w : ℝ) (H : ℕ) (C0 : ℤ) (qA : ℕ)
    (beta delta : ∀ t : ℕ,ZMod t) (j : ℕ) (v : ModelPoint w H) :
    modelIndicator w H C0 qA beta delta j v = 0 ∨ modelIndicator w H C0 qA beta delta j v = 1 := by
  unfold modelIndicator
  split <;> simp

theorem jointCondition_split (w : ℝ) (H : ℕ) (C0 : ℤ) (qA : ℕ)
    (beta delta : ∀ t : ℕ,ZMod t) (S : Finset ℕ) (v : ModelPoint w H) :
    jointCondition w H C0 qA beta delta S v ↔
      (∀ t ∈ divisorPrimes w H,∀ j ∈ S,patternKValue w H v.2 t+divisorPhase C0 v.1 t*(j : ZMod t) ≠ beta t) ∧
      (∀ t ∈ coprimePrimes w H,∀ j ∈ S,patternPValue w H v.2 t*(qA : ZMod t)*
        ((v.1 : ZMod t)+(H : ZMod t)*(j : ZMod t)) ≠ delta t) := by
  constructor
  · intro h
    exact ⟨fun t ht j hj => (h j hj).1 t ht,fun t ht j hj => (h j hj).2 t ht⟩
  · rintro ⟨h0,h1⟩ j hj
    exact ⟨fun t ht => h0 t ht j hj,fun t ht => h1 t ht j hj⟩

theorem jointIndicator_singleton (w : ℝ) (H : ℕ) (C0 : ℤ) (qA : ℕ)
    (beta delta : ∀ t : ℕ,ZMod t) (j : ℕ) (v : ModelPoint w H) :
    jointIndicator w H C0 qA beta delta {j} v = modelIndicator w H C0 qA beta delta j v := by
  simp [jointIndicator,jointCondition,modelIndicator]

theorem jointIndicator_pair (w : ℝ) (H : ℕ) (C0 : ℤ) (qA : ℕ)
    (beta delta : ∀ t : ℕ,ZMod t) (i j : ℕ) (v : ModelPoint w H) :
    jointIndicator w H C0 qA beta delta {i,j} v =
      modelIndicator w H C0 qA beta delta i v*modelIndicator w H C0 qA beta delta j v := by
  by_cases hi : modelSurvives w H C0 qA beta delta i v <;>
    by_cases hj : modelSurvives w H C0 qA beta delta j v <;>
    simp [jointIndicator,jointCondition,modelIndicator,hi,hj]

theorem jointIndicator_empty (w : ℝ) (H : ℕ) (C0 : ℤ) (qA : ℕ)
    (beta delta : ∀ t : ℕ,ZMod t) (v : ModelPoint w H) :
    jointIndicator w H C0 qA beta delta ∅ v = 1 := by simp [jointIndicator,jointCondition]

end ErdosVarianceMoments

end

section

namespace ErdosVarianceCommon
open NumberTheoryLean

noncomputable def referenceCount (Y : ℕ) (w : ℝ) (p qf : ℕ) : ℝ :=
  (Y : ℝ)/((p : ℝ)*qf)*SmallSieveFinite.smallEuler ⌊w⌋₊

noncomputable def commonReference (J : ℕ) (w : ℝ) : ℝ :=
  (J : ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊

theorem reference_above_common (Y qf p : ℕ) (hq : 0 < qf) (hp : 0 < p) (w R xi : ℝ)
    (hR : 0 < R) (hxi : 0 ≤ xi) (hxi1 : xi ≤ 1)
    (hV : 0 ≤ SmallSieveFinite.smallEuler ⌊w⌋₊)
    (hbin : R < (p : ℝ) ∧ (p : ℝ) ≤ (1+xi)*R) :
    commonReference (commonLength Y qf R xi) w ≤ referenceCount Y w p qf :=
  mul_le_mul_of_nonneg_right (commonLength_reference_bounds Y qf p hq hp R xi hR hxi hxi1 hbin).1 hV

theorem common_reference_error (Y qf p : ℕ) (hq : 0 < qf) (hp : 0 < p) (w R xi : ℝ)
    (hR : 0 < R) (hxi : 0 ≤ xi) (hxi1 : xi ≤ 1)
    (hV : 0 ≤ SmallSieveFinite.smallEuler ⌊w⌋₊)
    (hbin : R < (p : ℝ) ∧ (p : ℝ) ≤ (1+xi)*R)
    (hpay : 3 ≤ xi*(commonLength Y qf R xi : ℝ)) :
    |referenceCount Y w p qf-commonReference (commonLength Y qf R xi) w| ≤
      2*xi*commonReference (commonLength Y qf R xi) w := by
  have hr := commonLength_reference_bounds Y qf p hq hp R xi hR hxi hxi1 hbin
  have hd : (Y : ℝ)/((p : ℝ)*qf)-(commonLength Y qf R xi : ℝ) ≤
      2*xi*(commonLength Y qf R xi : ℝ) := by linarith [hr.2]
  rw [abs_of_nonneg (sub_nonneg.mpr (reference_above_common Y qf p hq hp w R xi hR hxi hxi1 hV hbin))]
  have hh := mul_le_mul_of_nonneg_right hd hV
  dsimp [referenceCount,commonReference]
  nlinarith

end ErdosVarianceCommon

end

section

namespace ErdosVarianceCommon
open NumberTheoryLean ErdosVarianceEffective ErdosInverseCounts ErdosHypotheticalTag
  ErdosInverseHits ErdosInverseTail
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def commonSurvivors (J : ℕ) (w : ℝ) (a : ℕ → ℕ) (r : ℚ)
    (qf p : ℕ) [NeZero p] (hHp : (effectiveModulus a r qf).Coprime p) : Finset ℕ :=
  ProgressionSmallSieve.progressionSurvivors J ⌊w⌋₊ (effectiveBase a r qf p hHp) (p*qf) a

theorem effectiveSurvivors_eq_progression (Y : ℕ) (w : ℝ) (a : ℕ → ℕ) (r : ℚ)
    (qf p : ℕ) [NeZero p] (hHp : (effectiveModulus a r qf).Coprime p) :
    effectiveSurvivors Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) a r qf p hHp =
      commonSurvivors (hitLength Y (p*qf) (effectiveBase a r qf p hHp)) w a r qf p hHp := by
  ext j
  simp only [effectiveSurvivors,commonSurvivors,ProgressionSmallSieve.progressionSurvivors,
    SievePartition.mem_survivors,Finset.mem_filter,Finset.mem_range,ProgressionSmallSieve.progressionHit]
  apply and_congr_right
  intro _hj
  apply forall_congr'
  intro t
  apply forall_congr'
  intro _ht
  rw [← Nat.cast_mul,← Nat.cast_add,Int.natCast_modEq_iff]
  rfl

theorem mem_commonSurvivors (J : ℕ) (w : ℝ) (a : ℕ → ℕ) (r : ℚ)
    (qf p : ℕ) [NeZero p] (hHp : (effectiveModulus a r qf).Coprime p) (j : ℕ) :
    j ∈ commonSurvivors J w a r qf p hHp ↔ j < J ∧
      ∀ t ∈ LargePrimeDeletion.cutoffPrimes ⌊w⌋₊,
        (effectiveInteger a r qf p hHp (j : ℤ) : ZMod t) ≠ (a t : ZMod t) := by
  simp only [commonSurvivors,ProgressionSmallSieve.progressionSurvivors,SievePartition.mem_survivors,
    Finset.mem_range,ProgressionSmallSieve.progressionHit]
  apply and_congr_right
  intro _hj
  apply forall_congr'
  intro t
  apply forall_congr'
  intro _ht
  rw [← Nat.cast_mul,← Nat.cast_add,effectiveInteger_nat_coordinate,← ZMod.intCast_eq_intCast_iff]
  simp only [Int.cast_natCast]

theorem hypothetical_count_eq_full_common_card (Y : ℕ) (w : ℝ) (a : ℕ → ℕ) (r : ℚ)
    (qf : ℕ) (hq : Squarefree qf) (p : ℕ) [NeZero p] (hp : p.Prime)
    (hqp : qf.Coprime p) (hHp : (effectiveModulus a r qf).Coprime p)
    (hps : p ∉ LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) :
    (modulusCount Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) (hypotheticalClass a r p) (p*qf) : ℝ) =
      ((commonSurvivors (hitLength Y (p*qf) (effectiveBase a r qf p hHp)) w a r qf p hHp).card : ℝ) := by
  rw [hypothetical_count_eq_effective_card Y _ a r qf hq p hp hqp hHp hps,
    effectiveSurvivors_eq_progression Y w a r qf p hHp,Int.cast_natCast]

end ErdosVarianceCommon

end

section

open _root_.Filter
open scoped Topology
namespace ErdosVarianceCommon
open ErdosInverseTail ErdosInverseBoxHeight ErdosInverseEuler

theorem source_common_interval_slack (aStar xi : ℝ) (ha : 0 < aStar)
    (hxi : 0 < xi) (hxi1 : xi ≤ 1) :
    ∀ᶠ z : ℝ in atTop,2 ≤ sourceW z ∧
      ∀ (Y qf p : ℕ) (R : ℝ),0 < qf → 0 < p → 0 < R →
        R < (p : ℝ) → (p : ℝ) ≤ (1+xi)*R →
        3*aStar/4 ≤ Real.log ((Y : ℝ)/((p : ℝ)*qf))/Real.log (sourceW z) →
        (sourceW z)^(5*aStar/8) ≤ (commonLength Y qf R xi : ℝ) ∧
        3 ≤ xi*(commonLength Y qf R xi : ℝ) ∧
        (sourceW z)^(aStar/2) ≤ 2*xi*(commonLength Y qf R xi : ℝ) := by
  have h8 := (tendsto_rpow_atTop (by positivity : 0 < aStar/8)).comp sourceW_tendsto_atTop
  have h34 := (tendsto_rpow_atTop (by positivity : 0 < 3*aStar/4)).comp sourceW_tendsto_atTop
  filter_upwards [source_common_length_regime aStar xi ha hxi hxi1,
    h8.eventually_ge_atTop 4,h34.eventually_ge_atTop 4] with z hreg h8z h34z
  refine ⟨hreg.1,?_⟩
  intro Y qf p R hq hp hR hpR hpU hlen
  change 4 ≤ (sourceW z)^(aStar/8) at h8z
  change 4 ≤ (sourceW z)^(3*aStar/4) at h34z
  have hcomp := bin_upper_comparison R xi hR hxi.le p ⟨hpR,hpU⟩
  have hlen' : 3*aStar/4 ≤ Real.log ((Y : ℝ)/((qf : ℝ)*p*1))/Real.log (sourceW z) := by
    simpa only [mul_one,mul_comm (qf : ℝ) (p : ℝ)] using hlen
  have hsmall := hreg.2 Y qf p 1 ((1+xi)*R) hq hp Nat.zero_lt_one hcomp.1 hcomp.2 (by simpa only [Nat.cast_one] using hlen')
  have hgeo := common_length_from_log Y qf p 1 hq hp Nat.zero_lt_one ((1+xi)*R) xi (sourceW z) aStar
    hcomp.1 hcomp.2 hxi.le hxi1 (by linarith [hreg.1]) ha (by simpa only [Nat.cast_one] using hlen')
  simp only [Nat.cast_one,div_one] at hsmall hgeo
  have hlow : (sourceW z)^(3*aStar/4)/4 ≤ (commonLength Y qf R xi : ℝ) := by
    change (sourceW z)^(3*aStar/4) ≤ 2*(commonLength Y qf R xi : ℝ)+2 at hgeo
    nlinarith
  have hW : 0 < sourceW z := by linarith [hreg.1]
  have hfactor : (sourceW z)^(5*aStar/8)*(sourceW z)^(aStar/8) = (sourceW z)^(3*aStar/4) := by
    rw [← Real.rpow_add hW]
    congr 1
    ring
  have hmul := mul_le_mul_of_nonneg_left h8z (Real.rpow_nonneg hW.le (5*aStar/8))
  refine ⟨?_,hsmall.1,hsmall.2⟩
  nlinarith

theorem commonLength_comparable (Y qf : ℕ) (hq : 0 < qf) (R xi : ℝ)
    (hR : 0 < R) (hxi : 0 ≤ xi) (hxi1 : xi ≤ 1) (hJ : 1 ≤ commonLength Y qf R xi) :
    (Y : ℝ)/(R*(qf : ℝ))/4 ≤ (commonLength Y qf R xi : ℝ) ∧
      (commonLength Y qf R xi : ℝ) ≤ (Y : ℝ)/(R*(qf : ℝ)) := by
  have hqR : (0 : ℝ) < qf := by exact_mod_cast hq
  have hF : 0 < 1+xi := by linarith
  have hA : 0 ≤ (Y : ℝ)/((qf : ℝ)*((1+xi)*R)) := by positivity
  have hfloor : (commonLength Y qf R xi : ℝ) ≤ (Y : ℝ)/((qf : ℝ)*((1+xi)*R)) := Nat.floor_le hA
  have hceil : (Y : ℝ)/((qf : ℝ)*((1+xi)*R)) < (commonLength Y qf R xi : ℝ)+1 := Nat.lt_floor_add_one _
  have hJr : (1 : ℝ) ≤ commonLength Y qf R xi := by exact_mod_cast hJ
  have he : (Y : ℝ)/(R*(qf : ℝ)) = (1+xi)*((Y : ℝ)/((qf : ℝ)*((1+xi)*R))) := by field_simp
  constructor
  · have hm := mul_le_mul_of_nonneg_left hceil.le hF.le
    have hj0 : (0 : ℝ) ≤ commonLength Y qf R xi := Nat.cast_nonneg _
    nlinarith
  · apply hfloor.trans
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
    have hm := mul_nonneg hxi (mul_pos hR hqR).le
    nlinarith

end ErdosVarianceCommon

end

section

open _root_.Filter
open scoped Topology
namespace ErdosVarianceCommon
open NumberTheoryLean ErdosVarianceEffective ErdosInverseCounts ErdosHypotheticalTag
  ErdosInverseHits ErdosInverseTail ErdosInverseBoxHeight ErdosInverseEuler

theorem large_prime_not_cutoff (w : ℝ) (hw : 0 ≤ w) (p : ℕ) (hwp : w < (p : ℝ)) :
    p ∉ LargePrimeDeletion.cutoffPrimes ⌊w⌋₊ := by
  intro hp
  have hh := (LargePrimeDeletion.mem_cutoffPrimes.mp hp).2
  have hhR := (Nat.le_floor_iff hw).mp hh
  linarith

theorem effective_step_coprime_small (w : ℝ) (qf : ℕ) (hq : Squarefree qf)
    (hlarge : ∀ t ∈ qf.primeFactors,w < (t : ℝ)) (p : ℕ) (hp : p.Prime) (hwp : w < (p : ℝ)) :
    ∀ t : ℕ,t.Prime → (t : ℝ) ≤ w → (p*qf).Coprime t := by
  intro t ht htw
  have hqt := full_cofactor_coprime_small qf hq w hlarge t ht htw
  apply Nat.Coprime.mul_left _ hqt
  apply (Nat.coprime_primes hp ht).mpr
  intro he
  subst p
  linarith

theorem source_common_count_errors (aStar : ℝ) (ha : 0 < aStar) :
    ∃ C : ℝ,0 < C ∧ ∀ xi : ℝ,0 < xi → xi ≤ 1 →
      ∀ᶠ z : ℝ in atTop,2 ≤ sourceW z ∧
      ∀ (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (_hq : Squarefree qf)
        (p : ℕ) [NeZero p] (_hp : p.Prime) (_hqp : qf.Coprime p)
        (hHp : (effectiveModulus a r qf).Coprime p) (R : ℝ),
        0 < R → R < (p : ℝ) → (p : ℝ) ≤ (1+xi)*R → sourceW z < (p : ℝ) →
        (∀ t ∈ qf.primeFactors,sourceW z < (t : ℝ)) →
        3*aStar/4 ≤ Real.log ((sourceY z : ℝ)/((p : ℝ)*qf))/Real.log (sourceW z) →
        let J := commonLength (sourceY z) qf R xi
        (sourceW z)^(5*aStar/8) ≤ (J : ℝ) ∧
        |(modulusCount (sourceY z) (LargePrimeDeletion.cutoffPrimes ⌊sourceW z⌋₊)
            (hypotheticalClass a r p) (p*qf) : ℝ)-
          ((commonSurvivors J (sourceW z) a r qf p hHp).card : ℝ)| ≤
          2*C*xi*commonReference J (sourceW z) ∧
        |referenceCount (sourceY z) (sourceW z) p qf-commonReference J (sourceW z)| ≤
          2*xi*commonReference J (sourceW z) := by
  obtain ⟨C,hC,w0,hw0,hupper⟩ := sieve_tail_upper (aStar/2) (by positivity)
  refine ⟨C,hC,?_⟩
  intro xi hxi hxi1
  filter_upwards [source_common_interval_slack aStar xi ha hxi hxi1,
    sourceW_tendsto_atTop.eventually_ge_atTop w0] with z hslack hW
  refine ⟨hslack.1,?_⟩
  intro a r qf hq p instP hp hqp hHp R hR hpl hpu hwp hlarge hlen
  let J := commonLength (sourceY z) qf R xi
  let N := hitLength (sourceY z) (p*qf) (effectiveBase a r qf p hHp)
  have hqpos := Nat.pos_of_ne_zero hq.ne_zero
  have hs := hslack.2 (sourceY z) qf p R hqpos hp.pos hR hpl hpu hlen
  have hwpos : 0 < sourceW z := by linarith [hslack.1]
  have hV : 0 ≤ SmallSieveFinite.smallEuler ⌊sourceW z⌋₊ :=
    ((inv_pos.mpr hwpos).trans_le (SmallSieveFinite.smallEuler_floor_ge_inv (sourceW z) hslack.1)).le
  have hJN : J ≤ N := commonLength_le_effective (sourceY z) a r qf hq p hHp R xi hR hxi.le ⟨hpl,hpu⟩
  have htail : ((N-J : ℕ) : ℝ) ≤ 2*xi*(J : ℝ) := by
    have hh := commonLength_tail_bound (sourceY z) a r qf hq p hHp R xi hR hxi.le hxi1 ⟨hpl,hpu⟩
    change ((N-J : ℕ) : ℝ) ≤ xi*(J : ℝ)+3 at hh
    linarith [hs.2.1]
  refine ⟨hs.1,?_,common_reference_error (sourceY z) qf p hqpos hp.pos (sourceW z) R xi hR hxi.le hxi1 hV ⟨hpl,hpu⟩ hs.2.1⟩
  rw [hypothetical_count_eq_full_common_card (sourceY z) (sourceW z) a r qf hq p hp hqp hHp
    (large_prime_not_cutoff (sourceW z) hwpos.le p hwp)]
  rw [commonSurvivors,commonSurvivors,survivor_count_difference J N ⌊sourceW z⌋₊ hJN]
  have hh := hupper J N (sourceW z) (2*xi*(J : ℝ)) (effectiveBase a r qf p hHp) (p*qf) a
    hW hs.2.2 htail (effective_step_coprime_small (sourceW z) qf hq hlarge p hp hwp)
  dsimp only [commonReference]
  nlinarith

end ErdosVarianceCommon

end

section

open _root_.Filter
open scoped Topology
namespace ErdosVarianceCommon
open NumberTheoryLean ErdosVarianceEffective ErdosInverseCounts ErdosHypotheticalTag
  ErdosInverseHits ErdosInverseTail ErdosInverseBoxHeight ErdosInverseEuler ErdosInverseAlignment

theorem source_actual_bad_to_common (aStar eps : ℝ) (ha : 0 < aStar) (heps : 0 < eps) :
    ∃ xi0 : ℝ,0 < xi0 ∧ xi0 ≤ 1 ∧ ∀ xi : ℝ,0 < xi → xi ≤ xi0 →
      ∀ᶠ z : ℝ in atTop,
      ∀ (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (_hq : Squarefree qf)
        (p : ℕ) [NeZero p] (_hp : p.Prime) (_hqp : qf.Coprime p)
        (hHp : (effectiveModulus a r qf).Coprime p) (R : ℝ),
        0 < R → R < (p : ℝ) → (p : ℝ) ≤ (1+xi)*R → sourceW z < (p : ℝ) →
        (∀ t ∈ qf.primeFactors,sourceW z < (t : ℝ)) →
        3*aStar/4 ≤ Real.log ((sourceY z : ℝ)/((p : ℝ)*qf))/Real.log (sourceW z) →
        aligns (fun t => (a t : ℤ)) r p →
        eps < |(modulusCount (sourceY z) (LargePrimeDeletion.cutoffPrimes ⌊sourceW z⌋₊) a (p*qf) : ℝ)/
          referenceCount (sourceY z) (sourceW z) p qf-1| →
        let J := commonLength (sourceY z) qf R xi
        (sourceW z)^(5*aStar/8) ≤ (J : ℝ) ∧
          (eps/2)*commonReference J (sourceW z) <
            |((commonSurvivors J (sourceW z) a r qf p hHp).card : ℝ)-commonReference J (sourceW z)| := by
  obtain ⟨C,hC,herrors⟩ := source_common_count_errors aStar ha
  have hden : 0 < 4*(C+1) := by positivity
  refine ⟨min 1 (eps/(4*(C+1))),lt_min zero_lt_one (div_pos heps hden),min_le_left _ _,?_⟩
  intro xi hxi hxib
  have hxi1 : xi ≤ 1 := hxib.trans (min_le_left _ _)
  have hxiBudget := (le_div_iff₀ hden).mp (hxib.trans (min_le_right _ _))
  have hBudget : 2*C*xi+2*xi ≤ eps/2 := by nlinarith
  filter_upwards [herrors xi hxi hxi1] with z hz
  intro a r qf hq p instP hp hqp hHp R hR hpl hpu hwp hlarge hlen halign hbad
  let J := commonLength (sourceY z) qf R xi
  have herr := hz.2 a r qf hq p hp hqp hHp R hR hpl hpu hwp hlarge hlen
  have hcount := herr.2.1
  rw [hypothetical_count_agrees (sourceY z) _ a r (p*qf) p hp halign] at hcount
  have hW : 0 < sourceW z := by linarith [hz.1]
  have hV : 0 < SmallSieveFinite.smallEuler ⌊sourceW z⌋₊ :=
    (inv_pos.mpr hW).trans_le (SmallSieveFinite.smallEuler_floor_ge_inv (sourceW z) hz.1)
  have hJ : (0 : ℝ) < J := (Real.rpow_pos_of_pos hW _).trans_le herr.1
  have hM : 0 < commonReference J (sourceW z) := mul_pos hJ hV
  have hmu := reference_above_common (sourceY z) qf p (Nat.pos_of_ne_zero hq.ne_zero) hp.pos
    (sourceW z) R xi hR hxi.le hxi1 hV.le ⟨hpl,hpu⟩
  have hmuPos : 0 < referenceCount (sourceY z) (sourceW z) p qf := hM.trans_le hmu
  have hbad' := (relative_deviation_iff _ _ eps hmuPos).mp hbad
  refine ⟨herr.1,?_⟩
  exact common_deviation_transfer _ _ _ _ eps (2*C*xi) (2*xi) hM.le hmu heps hcount herr.2.2 hBudget hbad'

end ErdosVarianceCommon

end

section

namespace ErdosVarianceMoments
open ErdosVarianceSmallModel ErdosVarianceEffective ErdosInverseCells ErdosPrimitiveIntercept ErdosInverseAlignment

noncomputable def actualDivisorTarget (a : ℕ → ℕ) (qf t : ℕ) : ZMod t :=
  ((a t : ZMod t)-(cofactorHit qf a : ZMod t))*(qf : ZMod t)⁻¹

noncomputable def actualCoprimeTarget (a : ℕ → ℕ) (r : ℚ) (t : ℕ) : ZMod t :=
  (r.den : ZMod t)*(a t : ZMod t)-(r.num : ZMod t)

def actualModelSurvives (w : ℝ) (a : ℕ → ℕ) (r : ℚ) (qf j : ℕ)
    (v : ModelPoint w (effectiveModulus a r qf)) : Prop :=
  modelSurvives w (effectiveModulus a r qf) (effectiveIntercept a r qf)
    (alignedCofactor (fun t => (a t : ℤ)) r qf) (actualDivisorTarget a qf) (actualCoprimeTarget a r) j v

noncomputable def actualModelIndicator (w : ℝ) (a : ℕ → ℕ) (r : ℚ) (qf j : ℕ)
    (v : ModelPoint w (effectiveModulus a r qf)) : ℝ :=
  modelIndicator w (effectiveModulus a r qf) (effectiveIntercept a r qf)
    (alignedCofactor (fun t => (a t : ℤ)) r qf) (actualDivisorTarget a qf) (actualCoprimeTarget a r) j v

theorem aligned_isolated_coprime_effective (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf)
    (p : ℕ) (hp : p.Prime) (hqp : qf.Coprime p) (halign : aligns (fun t => (a t : ℤ)) r p) :
    (effectiveModulus a r qf).Coprime p := by
  have hD := ErdosAlignedProgression.aligned_den_coprime_prime a r p hp halign
  have hd : badPrimeProduct (fun t => (a t : ℤ)) r qf ∣ qf := by
    refine ⟨alignedCofactor (fun t => (a t : ℤ)) r qf,?_⟩
    simpa only [mul_comm] using (alignedCofactor_mul_bad (fun t => (a t : ℤ)) r qf hq).symm
  exact hD.mul_left (hqp.of_dvd_left hd)

theorem aligned_coefficient_coprime_small (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf)
    (w : ℝ) (hlarge : ∀ u ∈ qf.primeFactors,w < (u : ℝ)) (t : ℕ) (ht : t.Prime) (htw : (t : ℝ) ≤ w) :
    (alignedCofactor (fun u => (a u : ℤ)) r qf).Coprime t := by
  have hd : alignedCofactor (fun u => (a u : ℤ)) r qf ∣ qf :=
    ⟨badPrimeProduct (fun u => (a u : ℤ)) r qf,(alignedCofactor_mul_bad (fun u => (a u : ℤ)) r qf hq).symm⟩
  exact (full_cofactor_coprime_small qf hq w hlarge t ht htw).of_dvd_left hd

end ErdosVarianceMoments

end

end Erdos970

end OAI
