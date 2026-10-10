import OAI.NumberTheory.Jacobsthal.Estimates.SmallModelSourceScales
import OAI.NumberTheory.Jacobsthal.Sieve.ResidueTailUpper

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseTail
open NumberTheoryLean

theorem interval_replacement_bounds (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ,0 < C ∧ ∃ w0 : ℝ,2 ≤ w0 ∧
      ∀ (J N u : ℕ) [NeZero u] (e : ZMod u) (w L : ℝ) (b : ℤ) (step : ℕ) (a : ℕ → ℕ),
        w0 ≤ w → J ≤ N → w^eta ≤ L → w^eta ≤ L/(u : ℝ) → ((N-J : ℕ) : ℝ) ≤ L →
        (∀ t : ℕ,t.Prime → (t : ℝ) ≤ w → step.Coprime t) →
        (∀ t : ℕ,t.Prime → (t : ℝ) ≤ w → (step*u).Coprime t) →
        |((ProgressionSmallSieve.progressionSurvivors N ⌊w⌋₊ b step a).card : ℝ)-
          ((ProgressionSmallSieve.progressionSurvivors J ⌊w⌋₊ b step a).card : ℝ)| ≤
            C*L*SmallSieveFinite.smallEuler ⌊w⌋₊ ∧
        |(((ProgressionSmallSieve.progressionSurvivors N ⌊w⌋₊ b step a).filter (fun j : ℕ => (j : ZMod u) = e)).card : ℝ)-
          (((ProgressionSmallSieve.progressionSurvivors J ⌊w⌋₊ b step a).filter (fun j : ℕ => (j : ZMod u) = e)).card : ℝ)| ≤
            2*C*(L/(u : ℝ))*SmallSieveFinite.smallEuler ⌊w⌋₊ := by
  obtain ⟨C1,hC1,w1,hw1,hparent⟩ := sieve_tail_upper eta heta
  obtain ⟨C2,hC2,w2,hw2,hchild⟩ := residue_tail_upper eta heta
  refine ⟨C1+C2,by linarith,max w1 w2,hw1.trans (le_max_left _ _),?_⟩
  intro J N u inst e w L b step a hw hJN hL hLu hNL hcop hcopu
  have hwleft : w1 ≤ w := (le_max_left _ _).trans hw
  have hwright : w2 ≤ w := (le_max_right _ _).trans hw
  have hw2' : 2 ≤ w := hw1.trans hwleft
  have hwpos : 0 < w := by linarith
  have hV : 0 ≤ SmallSieveFinite.smallEuler ⌊w⌋₊ :=
    ((inv_pos.mpr hwpos).trans_le (SmallSieveFinite.smallEuler_floor_ge_inv w hw2')).le
  have hLpos : 0 ≤ L := (Real.rpow_pos_of_pos hwpos eta).le.trans hL
  have hLupos : 0 ≤ L/(u : ℝ) := (Real.rpow_pos_of_pos hwpos eta).le.trans hLu
  constructor
  · rw [survivor_count_difference J N ⌊w⌋₊ hJN b step a]
    calc
      _ ≤ C1*L*SmallSieveFinite.smallEuler ⌊w⌋₊ := hparent J N w L b step a hwleft hL hNL hcop
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith : C1 ≤ C1+C2) hLpos) hV
  · rw [residue_count_difference J N ⌊w⌋₊ u hJN e b step a]
    calc
      _ ≤ 2*C2*(L/(u : ℝ))*SmallSieveFinite.smallEuler ⌊w⌋₊ :=
        hchild J N u e w L b step a hwright hLu hNL hcopu
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith : 2*C2 ≤ 2*(C1+C2)) hLupos) hV

end ErdosInverseTail

end

section

namespace ErdosInverseFrozen
open NumberTheoryLean ErdosInverseEuler

theorem center_step_coprime (w : ℝ) (p q q0 t : ℕ) (ht : t.Prime) (htw : (t : ℝ) ≤ w)
    (hqq : Int.ModEq (smallModulus w : ℤ) (q : ℤ) (q0 : ℤ))
    (hactual : (p*q).Coprime t) : (p*q0).Coprime t := by
  have htmem : t ∈ LargePrimeDeletion.cutoffPrimes ⌊w⌋₊ :=
    LargePrimeDeletion.mem_cutoffPrimes.mpr ⟨ht,(Nat.le_floor_iff ((Nat.cast_nonneg t).trans htw)).mpr htw⟩
  have hdiv : (t : ℤ) ∣ (smallModulus w : ℤ) := by
    exact_mod_cast cutoffPrime_dvd_smallModulus w t htmem
  have hqt : Nat.ModEq t q q0 := Int.natCast_modEq_iff.mp (hqq.of_dvd hdiv)
  have hprod : Nat.ModEq t (p*q) (p*q0) := hqt.mul_left p
  have hn := ht.coprime_iff_not_dvd.mp hactual.symm
  apply Nat.Coprime.symm
  apply ht.coprime_iff_not_dvd.mpr
  intro hd
  apply hn
  change (p*q)%t = (p*q0)%t at hprod
  exact Nat.dvd_of_mod_eq_zero (hprod.trans (Nat.mod_eq_zero_of_dvd hd))

end ErdosInverseFrozen

end

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseTail
open NumberTheoryLean ErdosInverseHits ErdosInverseFrozen ErdosInverseEuler ErdosInverseCounts ErdosInverseBoxHeight

theorem source_interval_replacement (aStar : ℝ) (ha : 0 < aStar) :
    ∃ C : ℝ,0 < C ∧ ∀ xi : ℝ,0 < xi → xi ≤ 1 →
      ∀ᶠ z : ℝ in atTop,∀ (a : ℕ → ℕ) (p q q0 u : ℕ) [NeZero p] [NeZero u]
        (_hp : p.Prime) (_hu : u.Prime) (hqp : q.Coprime p) (hq : Squarefree q)
        (hpu : p.Coprime u) (hqu : q.Coprime u) (Qplus : ℝ) (b0 v : ℤ),
        (q : ℝ) ≤ Qplus → Qplus ≤ (1+xi)*(q : ℝ) →
        3*aStar/4 ≤ Real.log ((sourceY z : ℝ)/((p : ℝ)*q*u))/Real.log (sourceW z) →
        (∀ t : ℕ,t.Prime → (t : ℝ) ≤ sourceW z → (p*q*u).Coprime t) →
        Int.ModEq (smallModulus (sourceW z) : ℤ) (q : ℤ) (q0 : ℤ) →
        Int.ModEq (smallModulus (sourceW z) : ℤ) (primeHitRepresentative q hq a : ℤ) b0 →
        Int.ModEq (smallModulus (sourceW z) : ℤ)
          (parentSlope p q hqp (a p) (primeHitRepresentative q hq a) : ℤ) v →
        let J := commonParentLength (sourceY z) p Qplus
        let V0 := SmallSieveFinite.smallEuler ⌊sourceW z⌋₊
        |(modulusCount (sourceY z) (LargePrimeDeletion.cutoffPrimes ⌊sourceW z⌋₊) a (p*q) : ℝ)-
          ((frozenCoordinates J (sourceW z) p q0 b0 v a).card : ℝ)| ≤ 2*C*xi*(J : ℝ)*V0 ∧
        |(modulusCount (sourceY z) (LargePrimeDeletion.cutoffPrimes ⌊sourceW z⌋₊) a (p*q*u) : ℝ)-
          (((frozenCoordinates J (sourceW z) p q0 b0 v a).filter
            (fun j : ℕ => (j : ZMod u) = parentEdgeResidue p q u hqp hq hpu hqu a)).card : ℝ)| ≤
              4*C*xi*(J : ℝ)*V0/(u : ℝ) := by
  obtain ⟨C,hC,w0,hw0,hbound⟩ := interval_replacement_bounds (aStar/2) (by positivity)
  refine ⟨C,hC,?_⟩
  intro xi hxi hxi1
  filter_upwards [source_common_length_regime aStar xi ha hxi hxi1,
    sourceW_tendsto_atTop.eventually_ge_atTop w0] with z hreg hw
  intro a p q q0 u instP instU hp hu hqp hq hpu hqu Qplus b0 v hqQ hQq hlog hcop hqq hbb hsv
  let J := commonParentLength (sourceY z) p Qplus
  let N := hitLength (sourceY z) (p*q) (sourceParentBase p q hqp hq a)
  have hqpos : 0 < q := Nat.pos_of_ne_zero hq.ne_zero
  have hlength := hreg.2 (sourceY z) p q u Qplus hp.pos hqpos hu.pos hqQ hQq hlog
  have hb := sourceParentBase_bounds p q hqp hq a
  have hJN : J ≤ N := commonParentLength_le_hits (sourceY z) p q _ hp.pos hqpos hb.2 Qplus hqQ
  have htail : ((N-J : ℕ) : ℝ) ≤ 2*xi*(J : ℝ) := by
    have hh := actual_cell_tail_length (sourceY z) p q _ hp.pos hqpos hb.1 hb.2 Qplus xi hxi.le hxi1 hqQ hQq
    change ((N-J : ℕ) : ℝ) ≤ xi*(J : ℝ)+3 at hh
    change 3 ≤ xi*(J : ℝ) ∧ _ at hlength
    nlinarith [hlength.1]
  have hLpos : 0 ≤ 2*xi*(J : ℝ) := by positivity
  have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast hu.pos
  have hL : (sourceW z)^(aStar/2) ≤ 2*xi*(J : ℝ) :=
    hlength.2.trans (div_le_self hLpos hu1)
  have hstep : ∀ t : ℕ,t.Prime → (t : ℝ) ≤ sourceW z → (p*q0).Coprime t := by
    intro t ht htw
    exact center_step_coprime (sourceW z) p q q0 t ht htw hqq (Nat.coprime_mul_iff_left.mp (hcop t ht htw)).1
  have hstepu : ∀ t : ℕ,t.Prime → (t : ℝ) ≤ sourceW z → (p*q0*u).Coprime t := by
    intro t ht htw
    have hactual : ((p*u)*q).Coprime t := by simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hcop t ht htw
    have hh := center_step_coprime (sourceW z) (p*u) q q0 t ht htw hqq hactual
    simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hh
  have herr := hbound J N u (parentEdgeResidue p q u hqp hq hpu hqu a) (sourceW z)
    (2*xi*(J : ℝ)) (b0+(q0 : ℤ)*v) (p*q0) a hw hJN hL hlength.2 htail hstep hstepu
  dsimp only
  rw [actual_parent_count_frozen (sourceY z) (sourceW z) a p q q0 hp hqp hq b0 v hqq hbb hsv,
    actual_child_count_frozen (sourceY z) (sourceW z) a p q q0 u hp hu hqp hq hpu hqu b0 v hqq hbb hsv]
  simp only [Int.cast_natCast]
  change _ ≤ _ ∧ _ ≤ _
  constructor
  · calc
      _ ≤ C*(2*xi*(J : ℝ))*SmallSieveFinite.smallEuler ⌊sourceW z⌋₊ := herr.1
      _ = _ := by ring
  · calc
      _ ≤ 2*C*((2*xi*(J : ℝ))/(u : ℝ))*SmallSieveFinite.smallEuler ⌊sourceW z⌋₊ := herr.2
      _ = _ := by ring

end ErdosInverseTail

end

end Erdos970

end OAI
