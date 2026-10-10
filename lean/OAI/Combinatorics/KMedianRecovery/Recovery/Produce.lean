import Mathlib
import OAI.Combinatorics.KMedianRecovery.Geometry.IndexedCost

namespace OAI

namespace MetricKMedianRecovery.PhaseSurplusProducer
open PhaseOriginalLedger LocalSearch Anchoring Surplus
variable {V : Type*} [MetricSpace V] [DecidableEq V] [Fintype V]

theorem produce (δ : V → V → ℕ) (F D : Finset V) (h L M N : ℕ) (v : ℝ)
    (hD : D.Nonempty) (hh : 2 ≤ h) (hkF : h+L ≤ F.card)
    (hN : N = D.card+F.card) (hM : 0 < M)
    (hδ : ∀ p ∈ D, ∀ i ∈ F, (δ p i : ℝ) = dist p i)
    (hfar : ∀ i ∈ F, ∀ p ∈ D, 1 ≤ dist i p)
    (hdiam : ∀ p ∈ D, ∀ i ∈ F, δ p i ≤ M)
    (hv : 0 < v) (hv1 : v ≤ 1/12)
    (hvc : v ≤ strictnessGap (200*countConstant (1/100))/1000)
    (hsmall : v^2 ≤ strictnessGap (200*countConstant (1/100))/(6*(200*countConstant (1/100)+2)))
    (hsize : 2/(N:ℝ) ≤ strictnessGap (200*countConstant (1/100))/200)
    (herror : (N:ℝ)^2/2^N ≤ v)
    (hL : 3*(HistoryPhaseBound.limit v ((M:ℝ)+8*(D.card:ℝ)*(M:ℝ))+1) ≤ L) :
    ∃ S : Finset V, S ⊆ F ∧ S.Nonempty ∧ S.card = h+L ∧ WidthLocalMin F D S 5 ∧
      ∀ O H : Finset V, ∀ xi : ℝ,
        O ⊆ F → O.card = h → H ⊆ F → H.Nonempty → H.card+L = h →
        cost D H ≤ (1+xi)*cost D O → xi ≤ 1 →
        cost D S ≤ (2-strictnessGap (200*countConstant (1/100))/100)*cost D O := by
  classical
  have hn : 0 < D.card := Finset.card_pos.mpr hD
  have hnN : D.card ≤ N := by omega
  have hhN : h ≤ N := by omega
  have hN3 : 3 ≤ N := by omega
  have hF : F.Nonempty := Finset.card_pos.mp (by omega)
  let : Nonempty D := hD.to_subtype
  have hfar' (i : V) (hi : i ∈ F) (j : D) : 1 ≤ dist i j.val := hfar i hi j.val j.property
  have hdiam' (i : V) (hi : i ∈ F) (j : D) : dist i j.val ≤ ((M:ℚ):ℝ) := by
    rw [dist_comm,← hδ _ j.property _ hi]
    exact_mod_cast hdiam _ j.property _ hi
  have hNQ : (1:ℚ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hnQ : (1:ℚ) ≤ D.card := by exact_mod_cast hn
  have hMQ : (1:ℚ) ≤ M := by exact_mod_cast hM
  have hlo : (0:ℚ) < 2/(N:ℚ)^2 := by positivity
  have hlohi : (2/(N:ℚ)^2) ≤ 8*(Fintype.card D:ℚ)*(M:ℚ) := by
    rw [Fintype.card_coe]
    have htwo : (2/(N:ℚ)^2) ≤ 2 := by
      apply (div_le_iff₀ (sq_pos_of_pos (by linarith : (0:ℚ) < N))).mpr
      nlinarith only [hNQ]
    have hprod : (1:ℚ) ≤ (D.card:ℚ)*(M:ℚ) := by
      simpa only [one_mul] using mul_le_mul hnQ hMQ (by norm_num : (0:ℚ) ≤ 1) (by linarith : (0:ℚ) ≤ D.card)
    linarith only [htwo,hprod]
  have hrate : 0 ≤ (1:ℝ)/2^N := by positivity
  have hbudget := PhaseOriginalLedger.produce (fun j : D => (j:V)) F v ((1:ℝ)/2^N)
    (2/(N:ℚ)^2) (M:ℚ) h N hv (by linarith only [hv1]) hrate le_rfl hlo
    (by exact_mod_cast hM) hN3 (by simpa only [Fintype.card_coe] using hnN) hh hlohi hF hfar' hdiam'
  rcases hbudget with hlow | hnormal
  · obtain ⟨U,Q,alpha,hUF,hU,hcard,hQ,hcost,hdual,hpay⟩ := hlow
    obtain ⟨S,hSF,hS,hSc,hSU,hlocal⟩ := pad_and_descend δ F D U (h+L) M hU hUF
      (hcard.trans (by omega)) hkF hδ hdiam
    rw [indexed_cost] at hcost
    refine ⟨S,hSF,hS,hSc,hlocal,?_⟩
    intro O H xi hOF hOh _ _ _ _ _
    have hO : O.Nonempty := Finset.card_pos.mp (by omega)
    have hd : Dual (fun j : D => (j:V)) F v (2/(N:ℝ)^2) alpha := by
      simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_pow,Rat.cast_natCast] using hdual
    have hp : (1-3*v)*Q ≤ ∑ j, alpha j := by simpa only [Nat.cast_zero,zero_mul,add_zero] using hpay
    exact small_cost F D O S hO hD hOF hfar N (by omega) (by omega) alpha Q v hd
      (hSU.trans hcost) hv hv1 hvc hsmall hsize hp
  · obtain ⟨lam,hlo',_,U,Q,alpha,hUF,hU,hcard,hQ,hcost,hdual,hpay⟩ := hnormal
    simp only [Rat.cast_natCast,Fintype.card_coe] at hcard
    obtain ⟨S,hSF,hS,hSc,hSU,hlocal⟩ := pad_and_descend δ F D U (h+L) M hU hUF
      (hcard.trans (by omega)) hkF hδ hdiam
    rw [indexed_cost] at hcost
    refine ⟨S,hSF,hS,hSc,hlocal,?_⟩
    intro O H xi hOF hOh hHF hH hHL hHcost hxi
    have hO : O.Nonempty := Finset.card_pos.mp (by omega)
    have hP1 := comparison_ge_one F D O hD hO hOF hfar
    have hlam : 0 < lam := (Rat.cast_pos.mpr hlo).trans_le hlo'
    have hOe : (O.card:ℝ) ≤ N := by exact_mod_cast (by omega : O.card ≤ N)
    have hne : (D.card:ℝ) ≤ N := by exact_mod_cast hnN
    have hprod : (O.card:ℝ)*D.card ≤ (N:ℝ)^2 := by
      simpa only [pow_two] using mul_le_mul hOe hne (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have herr : (O.card:ℝ)*D.card*((1:ℝ)/2^N) ≤ v*cost D O := by
      calc
        _ ≤ (N:ℝ)^2*((1:ℝ)/2^N) := mul_le_mul_of_nonneg_right hprod hrate
        _ = (N:ℝ)^2/2^N := by ring
        _ ≤ v := herror
        _ ≤ v*cost D O := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hP1 hv.le
    have hp : (1-3*v)*Q+(O.card:ℝ)*(lam-(D.card:ℝ)*((1:ℝ)/2^N)) ≤ ∑ j, alpha j := by
      simpa only [hOh,Fintype.card_coe] using hpay
    exact normal_cost F D O S H hO hS hH hOF hSF hHF (by omega) L (by omega)
      (by omega) hlocal (by linarith only [hP1]) alpha lam Q ((1:ℝ)/2^N) xi v hdual
      hlam hQ (hSU.trans hcost) hHcost hxi hv hv1 hvc hsmall herr hp

end MetricKMedianRecovery.PhaseSurplusProducer
namespace MetricKMedianRecovery.LocalSearch
variable {V : Type*} [PseudoMetricSpace V]

def feasibleSets (F : Finset V) (r : ℕ) : Finset (Finset V) :=
  F.powerset.filter (fun S => S.Nonempty ∧ S.card ≤ r)
omit [PseudoMetricSpace V] in
lemma mem_feasibleSets (F S : Finset V) (r : ℕ) :
    S ∈ feasibleSets F r ↔ S ⊆ F ∧ S.Nonempty ∧ S.card ≤ r := by
  simp only [feasibleSets,Finset.mem_filter,Finset.mem_powerset]
omit [PseudoMetricSpace V] in
lemma feasibleSets_nonempty (F : Finset V) (hF : F.Nonempty) (r : ℕ) (hr : 0 < r) :
    (feasibleSets F r).Nonempty := by
  obtain ⟨i,hi⟩ := hF
  exact ⟨{i},(mem_feasibleSets F {i} r).mpr
    ⟨Finset.singleton_subset_iff.mpr hi,Finset.singleton_nonempty i,by simp only [Finset.card_singleton]; omega⟩⟩
noncomputable def optimum (F D : Finset V) (r : ℕ) : ℝ :=
  if h : (feasibleSets F r).Nonempty then (feasibleSets F r).inf' h (cost D) else 0
lemma optimum_nonneg (F D : Finset V) (r : ℕ) : 0 ≤ optimum F D r := by
  unfold optimum
  split_ifs with h
  · exact Finset.le_inf' h _ (fun _ _ => cost_nonneg _ _)
  · rfl
lemma optimum_le (F D S : Finset V) (r : ℕ) (hSF : S ⊆ F)
    (hS : S.Nonempty) (hSr : S.card ≤ r) : optimum F D r ≤ cost D S := by
  have hm : S ∈ feasibleSets F r := (mem_feasibleSets F S r).mpr ⟨hSF,hS,hSr⟩
  rw [optimum,dite_eq_left ⟨S,hm⟩]
  exact Finset.inf'_le _ hm
lemma optimum_attained (F D : Finset V) (hF : F.Nonempty) (r : ℕ) (hr : 0 < r) :
    ∃ O ⊆ F, O.Nonempty ∧ O.card ≤ r ∧ cost D O = optimum F D r := by
  have h := feasibleSets_nonempty F hF r hr
  obtain ⟨O,hO,hmin⟩ := Finset.exists_min_image (feasibleSets F r) (cost D) h
  have hm := (mem_feasibleSets F O r).mp hO
  refine ⟨O,hm.1,hm.2.1,hm.2.2,?_⟩
  rw [optimum,dite_eq_left h]
  exact le_antisymm (Finset.le_inf' h _ hmin) (Finset.inf'_le _ hO)
lemma optimum_attained_exact (F D : Finset V) (hF : F.Nonempty) (r : ℕ)
    (hr : 0 < r) (hrF : r ≤ F.card) :
    ∃ O ⊆ F, O.Nonempty ∧ O.card = r ∧ cost D O = optimum F D r := by
  obtain ⟨S,hSF,hS,hSr,hcost⟩ := optimum_attained F D hF r hr
  obtain ⟨O,hSO,hOF,hOr⟩ := Finset.exists_subsuperset_card_eq hSF hSr hrF
  refine ⟨O,hOF,hS.mono hSO,hOr,?_⟩
  exact le_antisymm ((cost_mono D hS hSO).trans_eq hcost)
    (optimum_le F D O r hOF (hS.mono hSO) hOr.le)
lemma optimum_antitone (F D : Finset V) (hF : F.Nonempty) {a b : ℕ}
    (ha : 0 < a) (hab : a ≤ b) : optimum F D b ≤ optimum F D a := by
  obtain ⟨O,hOF,hO,hOa,hcost⟩ := optimum_attained F D hF a ha
  exact (optimum_le F D O b hOF hO (hOa.trans hab)).trans_eq hcost

end MetricKMedianRecovery.LocalSearch

end OAI
