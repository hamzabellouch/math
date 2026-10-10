import Mathlib
import OAI.Combinatorics.ThinTrees.Continuation.Loop
import OAI.Combinatorics.ThinTrees.Signing.Realization

namespace OAI

/-! Shortcut extraction. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped MatrixOrder
variable {n m : ℕ}

def State.active (a : State n m) : Finset (Fin m) := univ.filter (fun e => 0 < a.capacity e)

def State.packingTarget (a : State n m) : ℕ := ⌊a.quality-1⌋₊

lemma active_mem (a : State n m) (e : Fin m) : e ∈ a.active ↔ 0 < (a.capacity e:ℝ) := by
  simp only [State.active,mem_filter,mem_univ,true_and]
  exact_mod_cast Iff.rfl

lemma baseline_total_lt_one (m : ℕ) : (m:ℝ)*continuationBaseline m < 1 := by
  unfold continuationBaseline
  rw [mul_one_div]
  exact (div_lt_one (by positivity)).mpr (by linarith)

lemma sum_capacity_le_active (H : MultiGraph n m) (a : State n m)
    (hu : ∀e, 0 ≤ (a.capacity e:ℝ) ∧ (a.capacity e:ℝ) ≤ 1)
    (p : Fin n → Fin n) :
    capacity H.left H.right (fun e => (a.capacity e:ℝ)+continuationBaseline m) (Setoid.ker p) <
      ((H.crossing a.active p).card:ℝ)+1 := by
  classical
  rw [capacity_eq_sum,Orientations.crossing_ker,sum_add_distrib]
  have hmain : (∑e ∈ H.crossing univ p, (a.capacity e:ℝ)) ≤ (H.crossing a.active p).card := by
    have he : H.crossing a.active p=(H.crossing univ p).filter (fun e => 0 < a.capacity e) := by
      ext e
      simp only [MultiGraph.crossing,State.active,mem_filter,mem_univ,true_and]
      tauto
    rw [he,←Finset.sum_boole]
    apply sum_le_sum
    intro e _
    by_cases h : 0 < a.capacity e
    · simpa only [h,ite_true] using (hu e).2
    · have hh : ¬0 < (a.capacity e:ℝ) := by exact_mod_cast h
      simpa only [h,ite_false] using not_lt.mp hh
  have hcount : (H.crossing univ p).card ≤ m := (card_le_card (filter_subset _ _)).trans_eq (card_fin _)
  have hbase : (∑_e ∈ H.crossing univ p, continuationBaseline m) < 1 := by
    simp only [sum_const,nsmul_eq_mul]
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) (continuation_parameters m).1.le).trans_lt
      (baseline_total_lt_one m)
  linarith only [hmain,hbase]

lemma active_packable (H : MultiGraph n m) (hn : 0 < n) (a : State n m)
    (ha : Invariant H a) {q : ℕ} (hq : 0 < q) (hqQ : (q:ℝ) ≤ (a.quality:ℝ)-1) :
    H.TreePackable a.active q := by
  apply H.partition_criterion_sufficient a.active hq hn
  intro p
  by_cases hp : partitionSize p ≤ 1
  · have he : partitionSize p-1=0 := by omega
    simp only [he,mul_zero,Nat.zero_le]
  · have hp2 : 2 ≤ partitionSize p := by omega
    have hslack := ha.2.2.2 (Setoid.ker p)
    rw [slack,sub_nonneg,Orientations.partCount_ker] at hslack
    have hcap := sum_capacity_le_active H a (fun e => ⟨(ha.2.2.1 e).1,(ha.2.2.1 e).2.1⟩) p
    have hd : (1:ℝ) ≤ (partitionSize p:ℝ)-1 := by
      have hh : (2:ℝ) ≤ partitionSize p := by exact_mod_cast hp2
      linarith only [hh]
    have hm := mul_le_mul_of_nonneg_right hqQ (by linarith : (0:ℝ) ≤ (partitionSize p:ℝ)-1)
    have hnat : ((q*(partitionSize p-1):ℕ):ℝ)=(q:ℝ)*((partitionSize p:ℝ)-1) := by
      rw [Nat.cast_mul,Nat.cast_sub (by omega : 1 ≤ partitionSize p),Nat.cast_one]
    have hh : ((q*(partitionSize p-1):ℕ):ℝ) ≤ ((H.crossing a.active p).card:ℝ) := by
      rw [hnat]
      nlinarith only [hm,hcap,hslack,hd]
    exact_mod_cast hh

lemma packingTarget_lower (a : State n m) :
    (a.quality:ℝ)-2 ≤ (a.packingTarget:ℝ) := by
  have hh := Nat.lt_floor_add_one (a.quality-1)
  have hc : (a.quality:ℝ)-1 < (a.packingTarget:ℝ)+1 := by
    exact_mod_cast hh
  linarith only [hc]

lemma packingTarget_upper (a : State n m) (hq : 1 ≤ (a.quality:ℝ)) :
    (a.packingTarget:ℝ) ≤ (a.quality:ℝ)-1 := by
  have hi : (0:ℚ) ≤ a.quality-1 := by exact_mod_cast (sub_nonneg.mpr hq)
  exact_mod_cast Nat.floor_le hi

lemma packingTarget_pos (a : State n m) (hq : 2 ≤ (a.quality:ℝ)) : 0 < a.packingTarget := by
  apply Nat.floor_pos.mpr
  exact_mod_cast (show (1:ℝ) ≤ (a.quality:ℝ)-1 by linarith only [hq])

lemma active_resistance (H : MultiGraph n m) (hn : 0 < n) (hc : H.Connected univ)
    (a : State n m) (ha : Invariant H a) (e : Fin m) (he : e ∈ a.active) :
    resistance H a.realMatrix e < (a.scale:ℝ)⁻¹ := by
  have hX := domain_positive H hn hc ha.2.1
  have hR := centered_resistance_pos H hn hX e
  have hramp := (active_mem a e).mp he |>.trans_le (ha.2.2.1 e).2.2
  have hp := (ramp_active H hramp).1
  have hrec : 1 < ((a.scale:ℝ)*resistance H a.realMatrix e)⁻¹ :=
    hp.trans_le (min_le_right _ _)
  have hprod := (inv_lt_inv₀ (by norm_num : (0:ℝ)<1) (mul_pos ha.1 hR)).mp
    (by simpa using hrec)
  rw [←one_div]
  apply (lt_div_iff₀ ha.1).mpr
  nlinarith only [hprod]

lemma rounding_absorbed (r : ℕ) (hr : 1 ≤ r) : 1 ≤ (r:ℝ)^(-1/16:ℝ)*r := by
  have hp : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have he : (r:ℝ)^(-1/16:ℝ)*r=(r:ℝ)^(15/16:ℝ) := by
    conv_lhs => arg 2; rw [←Real.rpow_one (r:ℝ)]
    rw [←Real.rpow_add hp]
    norm_num
  rw [he]
  exact Real.one_le_rpow (by exact_mod_cast hr) (by norm_num)

theorem shortcut_correct : ∃R : ℕ, 64^16 ≤ R ∧ ∀r : ℕ, R ≤ r →
    ∀(n m : ℕ) (H : MultiGraph n m), 2 ≤ n → H.TreePackable univ r →
      let a := extractState H r
      a.realMatrix ∈ metricDomain H ∧ H.TreePackable a.active a.packingTarget ∧
      0 < a.packingTarget ∧ a.packingTarget ≤ r ∧
      (1-6*(r:ℝ)^(-1/16:ℝ))*r ≤ (a.packingTarget:ℝ) ∧
      ∀e ∈ a.active, resistance H a.realMatrix e ≤ (r:ℝ)^(-1/4:ℝ) := by
  obtain ⟨R,hR,hcorrect⟩ := extractState_correct
  refine ⟨R,hR,?_⟩
  intro r hr n m H hn hpack
  dsimp only
  have hrlarge : 64^16 ≤ r := hR.trans hr
  have hr3 : 3 ≤ r := (by norm_num : 3 ≤ 64^16).trans hrlarge
  have hr0 : 0 < r := by omega
  have hconn := packing_connected H hr0 hpack
  obtain ⟨ha,hscale,hlower,hupper⟩ := hcorrect r hr n m H hn hpack
  have hQ : 2 ≤ ((extractState H r).quality:ℝ) := by
    have hl := (running_quality_lower m r (scheduleLength m r) hrlarge le_rfl).trans
      (stateAt_quality H r (scheduleLength m r)).1
    change 3*(r:ℝ)/4 ≤ ((extractState H r).quality:ℝ) at hl
    have hrR : (3:ℝ) ≤ r := by exact_mod_cast hr3
    linarith only [hl,hrR]
  have hqpos := packingTarget_pos (extractState H r) hQ
  have hqupper := packingTarget_upper (extractState H r) (by linarith only [hQ])
  refine ⟨ha.2.1,active_packable H (by omega) (extractState H r) ha hqpos hqupper,hqpos,?_,?_,?_⟩
  · exact_mod_cast (show ((extractState H r).packingTarget:ℝ) ≤ r by linarith only [hqupper,hupper])
  · have hfloor := packingTarget_lower (extractState H r)
    have hrnd := rounding_absorbed r (by omega)
    nlinarith only [hfloor,hlower,hrnd]
  · intro e he
    have hres := active_resistance H (by omega) hconn (extractState H r) ha e he
    have hpow : 0 < (r:ℝ)^(1/4:ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast hr0) _
    have hrec := inv_anti₀ hpow hscale
    have heq : ((r:ℝ)^(1/4:ℝ))⁻¹=(r:ℝ)^(-1/4:ℝ) := by
      rw [←Real.rpow_neg (Nat.cast_nonneg r)]
      congr 1
      norm_num
    exact hres.le.trans (heq ▸ hrec)

end AlgorithmicThinTrees.MetricTests.RationalStep
end

end OAI
