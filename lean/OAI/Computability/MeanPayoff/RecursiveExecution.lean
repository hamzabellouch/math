import OAI.Computability.MeanPayoff.Allocation

namespace OAI

namespace MeanPayoff.Label

def downOracle (G : Game) (A : Fin G.n → ℤ) (d : ℕ) (a b : Fin G.n → ℚ)
    (ha : ∀ i, 0<a i) (hb : ∀ i, 0<b i) (g : Grid G.n) : Fin G.n → Bool :=
  (labeller G (fun i => gridPivot A ((2:ℤ)^(d-12)) g i-16*(2:ℤ)^(d-12)) (d-7)
    a (fun i => 4/3*b i) ha (fun i => mul_pos (by norm_num) (hb i))).val

def upOracle (G : Game) (A : Fin G.n → ℤ) (d : ℕ) (a b : Fin G.n → ℚ)
    (ha : ∀ i, 0<a i) (hb : ∀ i, 0<b i) (g : Grid G.n) : Fin G.n → Bool :=
  (labeller G (fun i => gridPivot A ((2:ℤ)^(d-12)) g i-16*(2:ℤ)^(d-12)) (d-7)
    (fun i => 4/3*a i) b (fun i => mul_pos (by norm_num) (ha i)) hb).val

def provisionalLabels (G : Game) (A : Fin G.n → ℤ) (d : ℕ) (a b : Fin G.n → ℚ)
    (ha : ∀ i, 0<a i) (hb : ∀ i, 0<b i) : Fin G.n → Bool :=
  (labeller G (fun i => finalPivot A ((2:ℤ)^(d-12))
      (downOracle G A d a b ha hb) (upOracle G A d a b ha hb) i-1024*(2:ℤ)^(d-12))
    (d-1) a b ha hb).val

def continuationLabels (G : Game) (A : Fin G.n → ℤ) (d : ℕ) (a b : Fin G.n → ℚ)
    (ha : ∀ i, 0<a i) (hb : ∀ i, 0<b i) : Fin G.n → Bool :=
  (labeller G A d (reweight a (provisionalLabels G A d a b ha hb))
    (reweight b (fun i => !(provisionalLabels G A d a b ha hb i)))
    (reweight_pos ha _) (reweight_pos hb _)).val

theorem labeller_base (G : Game) (A : Fin G.n → ℤ) (d : ℕ) (a b : Fin G.n → ℚ)
    (ha : ∀ i, 0<a i) (hb : ∀ i, 0<b i) (hbase : ∀ i, 1<a i*b i) :
    (labeller G A d a b ha hb).val=massLabels b := by
  rw [labeller.eq_1,dite_eq_left hbase]

theorem labeller_small (G : Game) (A : Fin G.n → ℤ) (d : ℕ) (a b : Fin G.n → ℚ)
    (ha : ∀ i, 0<a i) (hb : ∀ i, 0<b i) (hbase : ¬∀ i, 1<a i*b i) (hd : d<12) :
    (labeller G A d a b ha hb).val=widthLabels A
      (basic G A (shift A ((2:ℤ)^d)) (fun i => by
        dsimp [shift]; exact le_add_of_nonneg_right (by positivity))).1 ((2:ℤ)^d) := by
  rw [labeller.eq_1,dite_eq_right hbase,dite_eq_left hd]

theorem labeller_step (G : Game) (A : Fin G.n → ℤ) (d : ℕ) (a b : Fin G.n → ℚ)
    (ha : ∀ i, 0<a i) (hb : ∀ i, 0<b i) (hbase : ¬∀ i, 1<a i*b i) (hd : 12≤d) :
    (labeller G A d a b ha hb).val=override A
      (downPivot A ((2:ℤ)^(d-12)) (downOracle G A d a b ha hb))
      (finalPivot A ((2:ℤ)^(d-12)) (downOracle G A d a b ha hb) (upOracle G A d a b ha hb))
      ((2:ℤ)^(d-12)) (continuationLabels G A d a b ha hb) := by
  rw [labeller.eq_1,dite_eq_right hbase,dite_eq_right (Nat.not_lt.mpr hd)]
  rfl

end MeanPayoff.Label

namespace MeanPayoff.TreeDevice.Certified.DetDriver
open BinaryData DetRaw Label

def branchFactor (n : ℕ) : ℕ := 2*(1024*n+1)+1

theorem call_exec (G : Game) (A : Fin G.n → ℤ) (d : ℕ) (a b : Fin G.n → ℚ)
    (ha : ∀ i, 0<a i) (hb : ∀ i, 0<b i) (w : Fin G.m → W)
    (hw : ∀ e, (w e).val=transformed G e) (x : Input) (h : Rep A d a b x) (ks : List Frame) :
    ∃ k, k+1≤2*Label.callBound (branchFactor G.n) (d+budget a b ha hb) (budget a b ha hb) ∧
      Exec (Graph.codeVertices G w) (call x ks) (ret (List.ofFn (labeller G A d a b ha hb).val) ks) k := by
  let ar := Graph.codeVertices G w
  let s := branchFactor G.n
  let B := budget a b ha hb
  have hp := Label.callBound_pos s (d+B) B
  by_cases hbase : ∀ i, 1<a i*b i
  · refine ⟨1,by change 2≤2*Label.callBound s (d+B) B; omega,?_⟩
    have he : step (ar,call x ks)=ret (List.ofFn (labeller G A d a b ha hb).val) ks := by
      rw [step_call,base_eq h,ite_eq_left (by simpa using hbase),baseLabels_eq h,labeller_base G A d a b ha hb hbase]
    simpa only [he] using Exec.one ar (call x ks)
  · by_cases hsmall : d<12
    · refine ⟨1,by change 2≤2*Label.callBound s (d+B) B; omega,?_⟩
      have he : step (ar,call x ks)=ret (List.ofFn (labeller G A d a b ha hb).val) ks := by
        rw [step_call,base_eq h,ite_eq_right (by simpa using hbase),small_eq h,ite_eq_left (by simpa using hsmall)]
        rw [basic_eq G h hsmall w hw,labeller_small G A d a b ha hb hbase hsmall]
      simpa only [he] using Exec.one ar (call x ks)
    · have hd : 12≤d := by omega
      have hB : 0<B := by
        apply Nat.pos_of_ne_zero
        intro he
        exact hbase ((budget_zero_iff a b ha hb).mp he)
      let H := d+B-1
      let D := B-1
      let cd := Label.callBound s H D
      let cp := Label.callBound s H B
      let od := downOracle G A d a b ha hb
      let ou := upOracle G A d a b ha hb
      have hdb := down_budget ha hb hbase
      have hub := up_budget ha hb hbase
      have hod : ∀ (g : Grid G.n) (vs : List W), VectorRep (gridPivot A ((2:ℤ)^(d-12)) g) vs →
          ∀ fs : List Frame, ∃ k, k+1≤2*cd ∧
            Exec ar (call (child false (x,vs)) fs) (ret (List.ofFn (od g)) fs) k := by
        intro g vs hv fs
        have hc := child_rep h hd false hv
        obtain ⟨k,hk,he⟩ := call_exec G _ (d-7) a (fun i => 4/3*b i) ha
          (fun i => mul_pos (by norm_num) (hb i)) w hw (child false (x,vs)) hc fs
        refine ⟨k,?_,he⟩
        apply hk.trans
        apply Nat.mul_le_mul_left
        apply Label.callBound_mono le_rfl <;> dsimp [H,D,B] <;> omega
      have hou : ∀ (g : Grid G.n) (vs : List W), VectorRep (gridPivot A ((2:ℤ)^(d-12)) g) vs →
          ∀ fs : List Frame, ∃ k, k+1≤2*cd ∧
            Exec ar (call (child true (x,vs)) fs) (ret (List.ofFn (ou g)) fs) k := by
        intro g vs hv fs
        have hc := child_rep h hd true hv
        obtain ⟨k,hk,he⟩ := call_exec G _ (d-7) (fun i => 4/3*a i) b
          (fun i => mul_pos (by norm_num) (ha i)) hb w hw (child true (x,vs)) hc fs
        refine ⟨k,?_,he⟩
        apply hk.trans
        apply Nat.mul_le_mul_left
        apply Label.callBound_mono le_rfl <;> dsimp [H,D,B] <;> omega
      obtain ⟨ds,kd,hrd,hkd,hed⟩ := down_pass h hd ar od (2*cd) hod gridCenter (center x) [] (center_rep h hd) ks
      obtain ⟨us,ku,hru,hku,heu⟩ := up_pass h hd ar ou (2*cd) hou (downRun od gridCenter).val.1 ds ds hrd ks
      let ls := provisionalLabels G A d a b ha hb
      let lc := continuationLabels G A d a b ha hb
      have hprov := provisional_rep h hd hru
      obtain ⟨kp,hkp,hep⟩ := call_exec G _ (d-1) a b ha hb w hw (provisional (x,us)) hprov (frame 2 x ds us::ks)
      have hkp' : kp+1≤2*cp := by
        apply hkp.trans
        apply Nat.mul_le_mul_left
        apply Label.callBound_mono le_rfl (by dsimp [H,B]; omega) le_rfl
      have hc := continuation_rep h ls
      have hcb := cont_budget ha hb hbase ls
      obtain ⟨kc,hkc,hec⟩ := call_exec G A d _ _ (reweight_pos ha ls) (reweight_pos hb _) w hw
        (continuation (x,List.ofFn ls)) hc (frame 3 x ds us::ks)
      have hkc' : kc+1≤2*cd := by
        apply hkc.trans
        apply Nat.mul_le_mul_left
        apply Label.callBound_mono le_rfl <;> dsimp [H,D,B] <;> omega
      have hstart : Exec ar (call x ks)
          (call (child false (x,center x)) (frame 0 x [] (center x)::ks)) 1 := by
        have he : step (ar,call x ks)=call (child false (x,center x)) (frame 0 x [] (center x)::ks) := by
          rw [step_call,base_eq h,ite_eq_right (by simpa using hbase),small_eq h,ite_eq_right (by simpa using hsmall)]
        simpa only [he] using Exec.one ar (call x ks)
      have hpqs : Exec ar (ret (List.ofFn ls) (frame 2 x ds us::ks))
          (call (continuation (x,List.ofFn ls)) (frame 3 x ds us::ks)) 1 := by
        simpa only [step_provisional] using Exec.one ar (ret (List.ofFn ls) (frame 2 x ds us::ks))
      have hlast : Exec ar (ret (List.ofFn lc) (frame 3 x ds us::ks))
          (ret (List.ofFn (labeller G A d a b ha hb).val) ks) 1 := by
        have he : step (ar,ret (List.ofFn lc) (frame 3 x ds us::ks))=
            ret (List.ofFn (labeller G A d a b ha hb).val) ks := by
          rw [step_continuation,finish_eq h hd hrd hru lc,labeller_step G A d a b ha hb hbase hd]
          rfl
        simpa only [he] using Exec.one ar (ret (List.ofFn lc) (frame 3 x ds us::ks))
      refine ⟨((((1+kd)+ku)+kp)+1)+kc+1,?_,?_⟩
      · have hr1 := downRank_le (gridCenter : Grid G.n)
        have hr2 := upRank_le (downRun od gridCenter).val.1
        have hkdb : kd≤(1024*G.n+1)*(2*cd) := hkd.trans (Nat.mul_le_mul_right _ (by omega))
        have hkub : ku≤(1024*G.n+1)*(2*cd) := hku.trans (Nat.mul_le_mul_right _ (by omega))
        have hh : 1+cp+s*cd≤Label.callBound s (d+B) B := by
          have hh := Label.callBound_step s H D
          have heB : D+1=B := by dsimp [D]; omega
          have heH : H+1=d+B := by dsimp [H]; omega
          simpa only [heB,heH] using hh
        change _ ≤ 2*Label.callBound s (d+B) B
        have hs : s=2*(1024*G.n+1)+1 := rfl
        change 1+cp+(2*(1024*G.n+1)+1)*cd≤Label.callBound s (d+B) B at hh
        nlinarith only [hkdb,hkub,hkp',hkc',hh]
      · exact (((((hstart.trans hed).trans heu).trans hep).trans hpqs).trans hec).trans hlast
termination_by d+budget a b ha hb
decreasing_by
  all_goals first
    | exact (narrow_rank ha hb hbase d).1
    | exact (narrow_rank ha hb hbase d).2
    | exact continuation_rank ha hb hbase d ls
    | omega

end MeanPayoff.TreeDevice.Certified.DetDriver

end OAI
