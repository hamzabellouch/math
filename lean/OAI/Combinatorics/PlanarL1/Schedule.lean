import OAI.Combinatorics.PlanarL1.CutExtraction

namespace OAI


section

namespace PlanarL1.Parameters
open scoped NNReal
noncomputable def persistenceSlope : ℝ :=
  2/a₁+2/a₂+(mainN:ℝ)^2*(4*(mainK:ℝ)/mainQ+4*(mainK:ℝ)/EA)+
  (1+Columns.Model.SurvivingGroups.packBound*secondaryN : ℕ)^2*
    (4*(secondaryK:ℝ)/secondaryQ+4*(secondaryK:ℝ)/EB)
noncomputable def persistenceCount : ℝ :=
  4+2*(mainN:ℝ)^2+2*(1+Columns.Model.SurvivingGroups.packBound*secondaryN : ℕ)^2
lemma persistenceSlope_nonneg : 0 ≤ persistenceSlope := by
  unfold persistenceSlope
  apply add_nonneg
  · apply add_nonneg
    · exact add_nonneg (div_nonneg (by norm_num) interpolationA.2.1.le) (div_nonneg (by norm_num) interpolationB.2.1.le)
    · apply mul_nonneg (sq_nonneg _)
      exact add_nonneg (div_nonneg (mul_nonneg (by norm_num) (NNReal.coe_nonneg _)) mainQ_pos.le)
        (div_nonneg (mul_nonneg (by norm_num) (NNReal.coe_nonneg _)) interpolationA.1.le)
  · apply mul_nonneg (sq_nonneg _)
    exact add_nonneg (div_nonneg (mul_nonneg (by norm_num) (NNReal.coe_nonneg _)) secondaryQ_pos.le)
      (div_nonneg (mul_nonneg (by norm_num) (NNReal.coe_nonneg _)) interpolationB.1.le)
lemma persistenceCount_pos : 0 < persistenceCount := by
  unfold persistenceCount
  have h1 := sq_nonneg (mainN:ℝ)
  have h2 := sq_nonneg ((1+Columns.Model.SurvivingGroups.packBound*secondaryN : ℕ):ℝ)
  linarith
lemma persistenceLoss_eq (ρ : ℝ) {m : ℕ} (hm : 0 < m) :
    persistenceLoss ρ m=persistenceSlope*ρ+persistenceCount/m := by
  have hm' : (m:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  have hA := (interpolationA.2.1).ne'
  have hB := (interpolationB.2.1).ne'
  have heA := interpolationA.1.ne'
  have heB := interpolationB.1.ne'
  have hqA := mainQ_pos.ne'
  have hqB := secondaryQ_pos.ne'
  unfold persistenceLoss heightLoss mainLoss mainTestLoss secondaryLoss secondaryTestLoss persistenceSlope persistenceCount
  field_simp
  ring

/-- A single universal integer spacing. It is independent of the graph, its
edge lengths, the number of scales, and every finite random grid. -/
def GoodSpacing (Q : ℝ) : Prop :=
  2 ≤ Q ∧ 10 ≤ (R/200)*Q ∧ 20/Q ≤ persistenceRadius ∧
  20*persistenceSlope/(Q-1) ≤ 1/4 ∧ 3/(Q-1) ≤ successGain/2
lemma exists_goodSpacing : ∃ q : ℕ, GoodSpacing q := by
  obtain ⟨q,hq⟩ := exists_nat_gt (max 2 (max (2000/R) (max (20/persistenceRadius+1)
    (max (80*persistenceSlope+1) (6/successGain+1)))))
  have h2 : (2:ℝ)<q := (le_max_left _ _).trans_lt hq
  have hg : 2000/R<(q:ℝ) := (le_trans (le_max_left _ _) (le_max_right _ _)).trans_lt hq
  have hr : 20/persistenceRadius+1<(q:ℝ) := (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _))).trans_lt hq
  have hs : 80*persistenceSlope+1<(q:ℝ) := (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))).trans_lt hq
  have hb : 6/successGain+1<(q:ℝ) := (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))).trans_lt hq
  have hp : (0:ℝ)<q := by linarith
  have hp' : (0:ℝ)<q-1 := by linarith
  refine ⟨q,h2.le,?_,?_,?_,?_⟩
  · have hh := (div_lt_iff₀ (show (0:ℝ)<R by norm_num [R])).mp hg
    nlinarith
  · apply (div_le_iff₀ hp).mpr
    have hh := (div_lt_iff₀ persistenceRadius_pos).mp (show 20/persistenceRadius<(q:ℝ) by linarith)
    linarith
  · apply (div_le_iff₀ hp').mpr
    linarith
  · apply (div_le_iff₀ hp').mpr
    have hh := (div_lt_iff₀ successGain_pos).mp (show 6/successGain<(q:ℝ)-1 by linarith)
    nlinarith

lemma exists_mesh (N : ℕ) : ∃ m : ℕ, 0 < m ∧ 10000 ≤ m ∧ (N:ℝ)*persistenceCount/m ≤ 1/4 := by
  obtain ⟨m,hm⟩ := exists_nat_gt (max 10000 (4*N*persistenceCount))
  have ht : (10000:ℝ) < m := (le_max_left _ _).trans_lt hm
  have hp : 0 < m := by exact_mod_cast (show (0:ℝ) < m by linarith)
  refine ⟨m,hp,?_,?_⟩
  · exact_mod_cast (show (10000:ℝ) ≤ m by linarith)
  · apply (div_le_iff₀ (Nat.cast_pos.mpr hp)).mpr
    have hh := (le_max_right _ _).trans_lt hm
    linarith
end PlanarL1.Parameters

end



section

namespace PlanarL1.Execution
variable {α β γ : Type*}
lemma bind_assoc (E : Execution α) (F : α → Execution β) (G : β → Execution γ) :
    (E.bind F).bind G=E.bind (fun x => (F x).bind G) := by
  induction E with
  | pure x => rfl
  | choose n E ih => simp only [bind]; congr; funext i; exact ih i

def iterate (F : α → Execution α) (E : Execution α) : ℕ → Execution α
  | 0 => E
  | n+1 => (iterate F E n).bind F
lemma iterate_add (F : α → Execution α) (E : Execution α) (a b : ℕ) :
    iterate F E (a+b)=iterate F (iterate F E a) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change (iterate F E (a+b)).bind F=(iterate F (iterate F E a) b).bind F
    rw [ih]
lemma Holds.iterate {F : α → Execution α} {E : Execution α} {P : ℕ → α → Prop}
    (hE : E.Holds (P 0)) (h : ∀ n x, P n x → (F x).Holds (P (n+1))) (n : ℕ) :
    (iterate F E n).Holds (P n) := by
  induction n with
  | zero => exact hE
  | succ n ih => exact ih.bind F (h n)
lemma Holds.and {E : Execution α} {P Q : α → Prop} (hP : E.Holds P) (hQ : E.Holds Q) :
    E.Holds (fun x => P x ∧ Q x) := by
  induction E with
  | pure x => exact ⟨hP,hQ⟩
  | choose n E ih => exact fun i => ih i (hP i) (hQ i)
lemma prob_iterate_monotone (F : α → Execution α) (E : Execution α) (P : ℕ → α → Prop)
    (h : ∀ n x, P n x → (F x).Holds (P (n+1))) (N : ℕ) :
    E.prob (P 0) ≤ (iterate F E N).prob (P N) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have hh := conditional_success (iterate F E N) F (P N) (P (N+1)) (p := 1)
      (fun x hx => (h N x hx).prob_eq_one.ge)
    simp only [one_mul] at hh
    exact ih.trans hh
lemma iterate_loss (F : α → Execution α) (E : Execution α) (P : ℕ → α → Prop)
    (ε : ℕ → ℝ) (N : ℕ) (hε : ∀ n<N, 0 ≤ ε n)
    (h : ∀ n<N, ∀ x, P n x → (F x).prob (fun y => ¬P (n+1) y) ≤ ε n) :
    (iterate F E N).prob (fun x => ¬P N x) ≤
      E.prob (fun x => ¬P 0 x)+∑ n ∈ Finset.range N, ε n := by
  induction N with
  | zero => simp only [iterate,Finset.range_zero,Finset.sum_empty,add_zero,le_refl]
  | succ N ih =>
    have hh := conditional_loss (iterate F E N) F (P N) (P (N+1))
      (hε N (Nat.lt_succ_self N)) (h N (Nat.lt_succ_self N))
    have ih' := ih (fun n hn => hε n (Nat.lt_succ_of_lt hn)) (fun n hn => h n (Nat.lt_succ_of_lt hn))
    simp only [iterate] at hh ⊢
    rw [Finset.sum_range_succ]
    linarith
lemma Holds.prob_compl_zero {E : Execution α} {P : α → Prop} (h : E.Holds P) : E.prob (fun x => ¬P x)=0 := by
  rw [E.prob_compl P,h.prob_eq_one,sub_self]
end PlanarL1.Execution

end



section

namespace PlanarL1.Parameters
noncomputable def targetRadius (Q : ℝ) (f n : ℕ) : ℝ := 20*Q^n/Q^f
lemma targetRadius_nonneg {Q : ℝ} (hQ : 0 < Q) (f n : ℕ) : 0 ≤ targetRadius Q f n := by
  unfold targetRadius
  positivity
lemma targetRadius_self {Q : ℝ} (hQ : 0 < Q) (f : ℕ) : targetRadius Q f f=20 := by
  unfold targetRadius
  exact mul_div_cancel_right₀ _ (pow_ne_zero _ hQ.ne')
lemma targetRadius_succ (Q : ℝ) (f n : ℕ) : targetRadius Q f (n+1)=Q*targetRadius Q f n := by
  unfold targetRadius
  rw [pow_succ]
  ring
lemma targetRadius_small {Q : ℝ} (hQ : 1 < Q) {f n : ℕ} (hn : n<f) :
    targetRadius Q f n ≤ 20/Q := by
  have hp : 0 < Q := by linarith
  apply (div_le_div_iff₀ (pow_pos hp f) hp).mpr
  have hh := pow_le_pow_right₀ hQ.le (Nat.succ_le_of_lt hn)
  rw [pow_succ] at hh
  nlinarith
lemma sum_targetRadius {Q : ℝ} (hQ : 1 < Q) (f : ℕ) :
    ∑ n ∈ Finset.range f, targetRadius Q f n ≤ 20/(Q-1) := by
  have hp : 0 < Q := by linarith
  have hm : 0 < Q-1 := by linarith
  have he : (∑ n ∈ Finset.range f, targetRadius Q f n)*(Q-1)=20*(Q^f-1)/Q^f := by
    simp only [targetRadius,← Finset.sum_div,← Finset.mul_sum]
    rw [div_mul_eq_mul_div, mul_assoc,geom_sum_mul]
  apply (le_div_iff₀ hm).mpr
  rw [he]
  apply (div_le_iff₀ (pow_pos hp f)).mpr
  linarith
lemma sum_persistenceLoss {Q : ℝ} (hQ : GoodSpacing Q) {m : ℕ} (hm : 0 < m)
    (f : ℕ) (hf : (f:ℝ)*persistenceCount/m ≤ 1/4) :
    ∑ n ∈ Finset.range f, persistenceLoss (targetRadius Q f n) m ≤ 1/2 := by
  have hs := sum_targetRadius (show 1 < Q by linarith [hQ.1]) f
  have he : (∑ n ∈ Finset.range f, persistenceLoss (targetRadius Q f n) m) =
      persistenceSlope*(∑ n ∈ Finset.range f, targetRadius Q f n)+(f:ℝ)*persistenceCount/m := by
    simp only [persistenceLoss_eq _ hm,Finset.sum_add_distrib,← Finset.mul_sum,
      Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    ring
  rw [he]
  have hh := mul_le_mul_of_nonneg_left hs persistenceSlope_nonneg
  have hb := hQ.2.2.2.1
  have he' : persistenceSlope*(20/(Q-1))=20*persistenceSlope/(Q-1) := by ring
  rw [he'] at hh
  linarith

noncomputable def survivalBudget (Q : ℝ) (t : ℕ) : ℝ :=
  Q^t*(Q*successGain-3*Q/(Q-1))+3*Q/(Q-1)
lemma survivalBudget_zero (Q : ℝ) : survivalBudget Q 0=Q*successGain := by
  unfold survivalBudget
  simp
lemma survivalBudget_succ {Q : ℝ} (hQ : 1 < Q) (t : ℕ) :
    survivalBudget Q (t+1)=Q*(survivalBudget Q t-3) := by
  unfold survivalBudget
  rw [pow_succ]
  have hd : Q-1≠0 := by linarith
  field_simp
  ring
lemma survivalBudget_lower {Q : ℝ} (hQ : GoodSpacing Q) (t : ℕ) :
    Q^(t+1)*successGain/2 ≤ survivalBudget Q t := by
  have hp : 0 < Q := by linarith [hQ.1]
  have hm : 0 < Q-1 := by linarith [hQ.1]
  have hs := mul_le_mul_of_nonneg_left hQ.2.2.2.2 hp.le
  have he : Q*(3/(Q-1))=3*Q/(Q-1) := by ring
  rw [he] at hs
  have ht := mul_le_mul_of_nonneg_left hs (pow_nonneg hp.le t)
  have hr : 0≤3*Q/(Q-1) := by positivity
  unfold survivalBudget
  rw [pow_succ]
  nlinarith
end PlanarL1.Parameters

end



section

namespace PlanarL1.Parameters.GoodSpacing
variable {Q : ℝ} (h : GoodSpacing Q)
include h
lemma pos : 0 < Q := by linarith [h.1]
lemma one : 1 ≤ Q := by linarith [h.1]
lemma gt_one : 1 < Q := by linarith [h.1]
lemma gap : 10 ≤ (R/200)*Q := h.2.1
end PlanarL1.Parameters.GoodSpacing

namespace PlanarL1.Columns.Model.World
open Parameters
variable {k : ℕ} {V : Type*} [Fintype V] {Q : ℝ}
variable (g : GoodSpacing Q) (W : World k V Q) {m : ℕ} (hm : 0 < m)
noncomputable def run (n : ℕ) : Execution (World k V Q) :=
  Execution.iterate (fun Z => Z.step g.pos g.one g.gap hm) (.pure W) n

def Distances (n : ℕ) (Z : World k V Q) : Prop := ∀ x y, Z.distance x y=Q^n*W.distance x y
omit [Fintype V] in
lemma distances_zero : W.Distances 0 W := by intro x y; simp [distance]
lemma next_distances {n : ℕ} {Z : World k V Q} (h : W.Distances n Z) :
    (Z.step g.pos g.one g.gap hm).Holds (W.Distances (n+1)) := by
  apply (Z.step_distances g.pos g.one g.gap hm).mono
  intro T hT x y
  rw [hT,h,pow_succ]
  ring
lemma run_distances (n : ℕ) : (W.run g hm n).Holds (W.Distances n) :=
  Execution.Holds.iterate (E := .pure W) (P := W.Distances) W.distances_zero
    (fun _ _ h => W.next_distances g hm h) n

def TargetGood (f : ℕ) (x : V) (n : ℕ) (Z : World k V Q) : Prop :=
  W.Distances n Z ∧ Z.Coherent x (targetRadius Q f n)
lemma target_failure {f n : ℕ} (hn : n<f) {x : V} {Z : World k V Q} (h : W.TargetGood f x n Z) :
    (Z.step g.pos g.one g.gap hm).prob (fun T => ¬W.TargetGood f x (n+1) T) ≤
      persistenceLoss (targetRadius Q f n) m := by
  have hp := Z.step_persistence g.pos g.one g.gap hm (targetRadius_nonneg g.pos f n)
    ((targetRadius_small g.gt_one hn).trans g.2.2.1) h.2
  rw [← targetRadius_succ] at hp
  apply le_trans ?_ hp
  apply Execution.Holds.prob_mono
  apply (W.next_distances g hm h.1).mono
  intro T ht hn
  exact fun hc => hn ⟨ht,hc⟩
lemma run_target_failure {f : ℕ} {x : V} (hstart : W.Coherent x (targetRadius Q f 0))
    (hmesh : (f:ℝ)*persistenceCount/m ≤ 1/4) :
    (W.run g hm f).prob (fun Z => ¬W.TargetGood f x f Z) ≤ 1/2 := by
  have h0 : (Execution.pure W).Holds (W.TargetGood f x 0) := ⟨W.distances_zero,hstart⟩
  have hh := Execution.iterate_loss (fun Z : World k V Q => Z.step g.pos g.one g.gap hm)
    (.pure W) (W.TargetGood f x) (fun n => persistenceLoss (targetRadius Q f n) m) f
    (fun n hn => by
      rw [persistenceLoss_eq _ hm]
      exact add_nonneg (mul_nonneg persistenceSlope_nonneg (targetRadius_nonneg g.pos f n))
        (div_nonneg persistenceCount_pos.le (Nat.cast_nonneg m)))
    (fun n hn Z hZ => W.target_failure g hm hn hZ)
  rw [h0.prob_compl_zero,zero_add] at hh
  exact hh.trans (sum_persistenceLoss g hm f hmesh)
lemma run_success_probability {f : ℕ} {x y : V} (hstart : W.Coherent x (targetRadius Q f 0))
    (hmesh : (f:ℝ)*persistenceCount/m ≤ 1/4) (hmany : 10000 ≤ m)
    (hlo : 1 ≤ Q^f*W.distance x y) (hhi : Q^f*W.distance x y < 2) :
    successChance/2 ≤ (W.run g hm (f+1)).prob (fun Z => Z.Successful (Q*successGain) x y) := by
  have hf := W.run_target_failure g hm hstart hmesh
  rw [Execution.prob_compl] at hf
  have hh := Execution.conditional_success (W.run g hm f)
    (fun Z : World k V Q => Z.step g.pos g.one g.gap hm) (W.TargetGood f x f)
    (fun Z => Z.Successful (Q*successGain) x y) (p := successChance) (by
      intro Z hZ
      apply Z.step_success g.pos g.one g.gap hm hmany
      · simpa only [targetRadius_self g.pos] using hZ.2
      · rw [hZ.1]; exact hlo
      · rw [hZ.1]; exact hhi)
  have hp := mul_le_mul_of_nonneg_left (show 1/2≤(W.run g hm f).prob (W.TargetGood f x f) by linarith) successChance_pos.le
  have hp' : successChance/2 ≤ successChance*(W.run g hm f).prob (W.TargetGood f x f) := by
    nlinarith
  exact hp'.trans hh
lemma run_add (a b : ℕ) : W.run g hm (a+b)=
    Execution.iterate (fun Z : World k V Q => Z.step g.pos g.one g.gap hm) (W.run g hm a) b :=
  Execution.iterate_add _ _ _ _
lemma run_survival_probability {f : ℕ} {x y : V} (hstart : W.Coherent x (targetRadius Q f 0))
    (hmesh : (f:ℝ)*persistenceCount/m ≤ 1/4) (hmany : 10000 ≤ m)
    (hlo : 1 ≤ Q^f*W.distance x y) (hhi : Q^f*W.distance x y < 2) (t : ℕ) :
    successChance/2 ≤ (W.run g hm (f+1+t)).prob (fun Z => Z.Successful (survivalBudget Q t) x y) := by
  rw [W.run_add g hm]
  apply le_trans (W.run_success_probability g hm hstart hmesh hmany hlo hhi)
  have hh := Execution.prob_iterate_monotone (fun Z : World k V Q => Z.step g.pos g.one g.gap hm)
    (W.run g hm (f+1)) (fun n Z => Z.Successful (survivalBudget Q n) x y) (by
      intro n Z hZ
      rw [survivalBudget_succ g.gt_one]
      exact Z.step_survives g.pos g.one g.gap hm hZ) t
  simpa only [survivalBudget_zero] using hh
end PlanarL1.Columns.Model.World

end



section

namespace PlanarL1.Parameters
noncomputable def scheduleGain : ℝ := successChance*successGain/8
lemma scheduleGain_pos : 0 < scheduleGain := div_pos (mul_pos successChance_pos successGain_pos) (by norm_num)
end PlanarL1.Parameters

namespace PlanarL1.Columns.Model.World
open Parameters
variable {k : ℕ} {V : Type*} [Fintype V] {Q : ℝ}
variable (g : GoodSpacing Q) (W : World k V Q) {m : ℕ} (hm : 0 < m)
noncomputable def averagedCuts (N : ℕ) : FiniteL1.CutFamily V :=
  FiniteL1.CutFamily.average (W.run g hm N) World.cuts
lemma averagedCuts_upper (N : ℕ) (x y : V) :
    (W.averagedCuts g hm N).distance x y ≤ 2*(Q^N*W.distance x y) := by
  rw [averagedCuts,FiniteL1.CutFamily.distance_average,← Execution.mean_const (W.run g hm N) (2*(Q^N*W.distance x y))]
  apply Execution.Holds.mean_mono
  apply (W.run_distances g hm N).mono
  intro Z hZ
  exact (Z.cuts_upper x y).trans_eq (by rw [hZ])
lemma averagedCuts_designated {f : ℕ} {x y : V} (hstart : W.Coherent x (targetRadius Q f 0))
    (hmesh : (f:ℝ)*persistenceCount/m ≤ 1/4) (hmany : 10000 ≤ m)
    (hlo : 1 ≤ Q^f*W.distance x y) (hhi : Q^f*W.distance x y < 2) (t : ℕ) :
    scheduleGain*(Q^(f+1+t)*W.distance x y) ≤ (W.averagedCuts g hm (f+1+t)).distance x y := by
  have hQpos := g.pos
  have hGain := successGain_pos
  have hChance := successChance_pos
  have hp := W.run_survival_probability g hm hstart hmesh hmany hlo hhi t
  have hb := survivalBudget_lower g t
  have hc : 0 ≤ Q^(t+1)*successGain/2 := by positivity
  have hh := (W.run g hm (f+1+t)).mean_lower_of_event
    (P := fun Z => Z.Successful (survivalBudget Q t) x y)
    (f := fun Z => Z.cuts.distance x y) (c := Q^(t+1)*successGain/2)
    (fun Z => FiniteL1.CutFamily.distance_nonneg _ _ _) (fun Z hZ => hb.trans hZ.cuts)
  have hprod := mul_le_mul_of_nonneg_left hp hc
  rw [averagedCuts,FiniteL1.CutFamily.distance_average]
  apply le_trans ?_ (hprod.trans hh)
  have he : Q^(f+1+t)=Q^(t+1)*Q^f := by
    rw [← pow_add]
    congr 1
    omega
  rw [he]
  calc
    _ = (Q^(t+1)*successChance*successGain/8)*(Q^f*W.distance x y) := by unfold scheduleGain; ring
    _ ≤ (Q^(t+1)*successChance*successGain/8)*2 :=
      mul_le_mul_of_nonneg_left hhi.le (by positivity)
    _ = _ := by ring
lemma averagedCuts_lower {N f : ℕ} (hf : f<N) {x y : V}
    (hstart : W.Coherent x (targetRadius Q f 0))
    (hmesh : (N:ℝ)*persistenceCount/m ≤ 1/4) (hmany : 10000 ≤ m)
    (hlo : 1 ≤ Q^f*W.distance x y) (hhi : Q^f*W.distance x y < 2) :
    scheduleGain*(Q^N*W.distance x y) ≤ (W.averagedCuts g hm N).distance x y := by
  have hfm : (f:ℝ)*persistenceCount/m ≤ 1/4 := by
    apply le_trans ?_ hmesh
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr hf.le) persistenceCount_pos.le) (Nat.cast_nonneg m)
  have hh := W.averagedCuts_designated g hm hstart hfm hmany hlo hhi (N-(f+1))
  rwa [Nat.add_sub_of_le (Nat.succ_le_of_lt hf)] at hh
end PlanarL1.Columns.Model.World

end



section

namespace PlanarL1.Columns.Model.World
open Parameters
variable {k : ℕ} {V : Type*} [Fintype V] {Q : ℝ}
variable (g : GoodSpacing Q) {M : Model (k+1)} (A : Ambient M)
variable (v : V → M.Point Set.univ A.root) {σ : ℝ} (hσ : 0 < σ) {m : ℕ} (hm : 0 < m)
noncomputable def startAt : World k V Q :=
  initial (Q := Q) (A.dilate hσ) (fun x => A.scaleEquiv hσ (v x))
omit [Fintype V] in
lemma startAt_distance (x y : V) : (startAt (Q := Q) A v hσ).distance x y=σ*dist (v x) (v y) :=
  A.scaleEquiv_dist hσ _ _
omit [Fintype V] in
lemma startAt_coherent (x : V) (ρ : ℝ) : (startAt (Q := Q) A v hσ).Coherent x ρ :=
  initial_coherent _ _ _ _
noncomputable def normalizedCuts (N : ℕ) : FiniteL1.CutFamily V :=
  FiniteL1.CutFamily.scale ((Q^N*σ)⁻¹) (inv_nonneg.mpr (mul_pos (pow_pos g.pos N) hσ).le)
    ((startAt (Q := Q) A v hσ).averagedCuts g hm N)
omit [Fintype V] in
include g hσ in
lemma normalization_cancel (N : ℕ) (c d : ℝ) :
    (Q^N*σ)⁻¹*(c*(Q^N*(σ*d)))=c*d := by
  calc
    _ = ((Q^N*σ)⁻¹*(Q^N*σ))*(c*d) := by ring
    _ = _ := by rw [inv_mul_cancel₀ (mul_pos (pow_pos g.pos N) hσ).ne',one_mul]
lemma normalizedCuts_upper (N : ℕ) (x y : V) :
    (normalizedCuts g A v hσ hm N).distance x y ≤ 2*dist (v x) (v y) := by
  rw [normalizedCuts,FiniteL1.CutFamily.distance_scale]
  have hh := (startAt (Q := Q) A v hσ).averagedCuts_upper g hm N x y
  rw [startAt_distance] at hh
  exact (mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (mul_pos (pow_pos g.pos N) hσ).le)).trans_eq
    (normalization_cancel g hσ N 2 _)
lemma normalizedCuts_lower {N f : ℕ} (hf : f<N) {x y : V}
    (hmesh : (N:ℝ)*persistenceCount/m ≤ 1/4) (hmany : 10000 ≤ m)
    (hlo : 1≤Q^f*σ*dist (v x) (v y)) (hhi : Q^f*σ*dist (v x) (v y)<2) :
    scheduleGain*dist (v x) (v y) ≤ (normalizedCuts g A v hσ hm N).distance x y := by
  have hh := (startAt (Q := Q) A v hσ).averagedCuts_lower g hm hf
    (startAt_coherent A v hσ x _) hmesh hmany
    (by rwa [startAt_distance,← mul_assoc]) (by rwa [startAt_distance,← mul_assoc])
  rw [startAt_distance] at hh
  have ht := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (mul_pos (pow_pos g.pos N) hσ).le)
  rw [normalization_cancel g hσ] at ht
  simpa only [normalizedCuts,FiniteL1.CutFamily.distance_scale] using ht
end PlanarL1.Columns.Model.World

end



section

namespace PlanarL1.Parameters
lemma first_scale {Q d : ℝ} (hQ : 1<Q) (hsmall : d<1) {T : ℕ} (hT : 1≤Q^T*d) :
    ∃ f : ℕ, f≤T ∧ 1≤Q^f*d ∧ Q^f*d<Q := by
  have hex : ∃ n : ℕ, 1≤Q^n*d := ⟨T,hT⟩
  let f := Nat.find hex
  have hf : 1≤Q^f*d := Nat.find_spec hex
  have hb : f≤T := Nat.find_min' hex hT
  refine ⟨f,hb,hf,?_⟩
  cases he : f with
  | zero => simp only [he,pow_zero,one_mul] at hf; linarith
  | succ n =>
    have hn : n<f := by omega
    have hp := lt_of_not_ge (Nat.find_min hex hn)
    have hh := mul_lt_mul_of_pos_left hp (show 0<Q by linarith)
    rw [pow_succ]
    nlinarith

lemma integer_offset {q : ℕ} {D : ℝ} (hlo : 1≤D) (hhi : D<(q:ℝ)) :
    ∃ i : Fin q, 1≤D/((i.val+1:ℕ):ℝ) ∧ D/((i.val+1:ℕ):ℝ)<2 := by
  let j : ℕ := ⌊D⌋₊
  have hj : 1≤j := by exact Nat.le_floor (by simpa using hlo)
  have hjD : (j:ℝ)≤D := Nat.floor_le (by linarith)
  have hDj : D<(j:ℝ)+1 := Nat.lt_floor_add_one D
  have hjq : j<q := by exact_mod_cast hjD.trans_lt hhi
  have hjp : 0<(j:ℝ) := by exact_mod_cast (show 0<j by omega)
  let i : Fin q := ⟨j-1,by omega⟩
  have hi : i.val+1=j := Nat.sub_add_cancel hj
  refine ⟨i,?_,?_⟩
  · rw [hi]
    exact (le_div_iff₀ hjp).mpr (by simpa using hjD)
  · rw [hi]
    apply (div_lt_iff₀ hjp).mpr
    have hjr : (1:ℝ)≤j := by exact_mod_cast hj
    linarith

/-- A finite family of Q offsets covers arbitrary positive distances. Only the
number of iterations and the initial units depend on the finite metric. -/
lemma finite_schedule_cover {V : Type*} [Fintype V] (d : V → V → ℝ)
    (hd : ∀ x y, 0≤d x y) {q : ℕ} (hq : 1<(q:ℝ)) :
    ∃ ε : ℝ, 0<ε ∧ ∃ N : ℕ, ∀ x y, 0<d x y →
      ∃ i : Fin q, ∃ f : ℕ, f<N ∧
        1≤(q:ℝ)^f*(ε/((i.val+1:ℕ):ℝ))*d x y ∧
        (q:ℝ)^f*(ε/((i.val+1:ℕ):ℝ))*d x y<2 := by
  classical
  let B : ℝ := ∑ x, ∑ y, d x y
  have hB : 0≤B := Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun y _ => hd x y))
  have hb (x y : V) : d x y≤B :=
    (Finset.single_le_sum (fun z _ => hd x z) (Finset.mem_univ y)).trans
      (Finset.single_le_sum (fun z _ => Finset.sum_nonneg (fun w _ => hd z w)) (Finset.mem_univ x))
  let ε : ℝ := 1/(B+1)
  have hε : 0<ε := by unfold ε; positivity
  have hsmall (x y : V) : ε*d x y<1 := by
    change (1/(B+1))*d x y<1
    rw [one_div,mul_comm,← div_eq_mul_inv]
    apply (div_lt_iff₀ (show 0<B+1 by linarith)).mpr
    linarith [hb x y]
  have hex : ∀ x y, ∃ n : ℕ, 0<d x y → 1≤(q:ℝ)^n*(ε*d x y) := by
    intro x y
    by_cases hp : 0<d x y
    · obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt (1/(ε*d x y)) hq
      refine ⟨n,fun _ => ?_⟩
      exact ((div_lt_iff₀ (mul_pos hε hp)).mp hn).le
    · exact ⟨0,fun hh => (hp hh).elim⟩
  choose bound hbound using hex
  let T : ℕ := ∑ x, ∑ y, bound x y
  have ht (x y : V) : bound x y≤T :=
    (Finset.single_le_sum (fun z _ => Nat.zero_le _) (Finset.mem_univ y)).trans
      (Finset.single_le_sum (f := fun z => ∑ w, bound z w) (fun z _ => Nat.zero_le _) (Finset.mem_univ x))
  refine ⟨ε,hε,T+1,?_⟩
  intro x y hxy
  have hT : 1≤(q:ℝ)^T*(ε*d x y) := (hbound x y hxy).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hq.le (ht x y)) (mul_pos hε hxy).le)
  obtain ⟨f,hf,hlo,hhi⟩ := first_scale hq (hsmall x y) hT
  obtain ⟨i,hil,hih⟩ := integer_offset hlo hhi
  refine ⟨i,f,Nat.lt_succ_of_le hf,?_,?_⟩
  · convert hil using 1; ring
  · convert hih using 1; ring
end PlanarL1.Parameters

end

end OAI
