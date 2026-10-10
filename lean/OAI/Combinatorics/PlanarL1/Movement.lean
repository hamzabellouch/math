import OAI.Combinatorics.PlanarL1.CoupledState

namespace OAI


section

namespace PlanarL1.Columns.Model.BState
open MeasureTheory Set
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {κ : ℝ} {lam : ℝ≥0}
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {S : BState M κ lam Ω μ}

namespace SecondaryStep
variable {J : Set ℝ} {root : Fin (k+1)} (U : SecondaryStep S J root)
lemma full_movement (i : Fin (k+1)) (H : U.data.band) :
    |U.fullReplacement i H-U.comparison.value i H| ≤ (51/1000:ℝ) := by
  by_cases hd : H.val ∈ SecondaryCell.domain U.seeds U.radius i
  · rw [U.fullReplacement_inside i H hd,←U.point_old hd]
    have hh := SecondaryCell.replacement_movement U.tree U.seeds U.old U.supportValue U.data.isOrdinary
      (αo := U.ordered_offset) (αh := U.shield_offset) (lo := U.lo)
      U.seeds_nonempty U.old_lipschitz U.zeta_eq U.radius_nonneg U.delta_eq U.noise_bounds
      U.seed_near (SecondaryCell.point_distance U.seeds U.radius hd)
    exact hh.trans (by linarith [U.radius_small])
  · rw [U.fullReplacement_outside i H hd,sub_self,abs_zero]
    norm_num
end SecondaryStep

namespace SecondaryBatch
variable (B : SecondaryBatch S)
lemma selected_movement (i : Fin (k+1)) (H : B.data.band) :
    |(B.selected i H).value-κ*B.comparison.value i H| ≤ κ*(51/1000:ℝ) := by
  rcases B.selected_cases i H with he|⟨a,he⟩
  · rw [he]; simp only [sub_self,abs_zero]
    exact mul_nonneg B.kappa_nonneg (by norm_num)
  · rw [he]; change |(B.groupNamed a i H).value-κ*B.comparison.value i H| ≤ _
    rw [B.groupNamed_value,←B.step_comparison a i H,←mul_sub,abs_mul,abs_of_nonneg B.kappa_nonneg]
    exact mul_le_mul_of_nonneg_left ((B.step a).full_movement i (B.groupHeight a H)) B.kappa_nonneg

lemma old_indicator_inside (w : Ω × Bool) (i : Fin (k+1)) (H : ℝ) (hd : H ∈ B.domain i) :
    (S.lift.sets.activity w).indicator i H=Threshold.chartValue H
      (κ*(B.data.offset+B.data.orientation B.positive*B.comparison.value i ⟨H,B.domain_band hd⟩))
      ((S.labels B.index).lift.value w) := by
  have hr := S.represents_named w.1 i H B.index (B.domain_name hd) (B.domain_band hd)
  have he := B.data.comparison_convert lam B.lambda_bound B.positive i ⟨H,B.domain_band hd⟩
  change (S.sets.activity w.1).active i H ↔ Threshold.active (S.labels B.index) H
    (κ*B.data.value lam i ⟨H,B.domain_band hd⟩) w.1 at hr
  rw [he] at hr
  change (S.sets.activity w.1).indicator i H=_
  simp only [Activity.indicator,Threshold.chartValue,Threshold.half,Threshold.active] at *
  exact if_congr hr rfl rfl

lemma movement_integrable (i : Fin (k+1)) (H : ℝ) : Integrable
    (fun w => (B.patch.apply.activity w).indicator i H-(S.lift.sets.activity w).indicator i H)
      (μ.prod Threshold.fair) := by
  by_cases hd : H ∈ B.domain i
  · simp_rw [B.indicator_inside _ i H hd,B.old_indicator_inside _ i H hd]
    exact (S.labels B.index).lift.integrable_difference _ _ _ _
  · have he (w : Ω × Bool) : (B.patch.apply.activity w).indicator i H=(S.lift.sets.activity w).indicator i H := by
      simp only [Activity.indicator,B.patch.unchanged hd w]
    simp only [he,sub_self]
    exact integrable_zero _ _ _

lemma movement_bound (i : Fin (k+1)) (H : ℝ) :
    (∫ w, |(B.patch.apply.activity w).indicator i H-(S.lift.sets.activity w).indicator i H| ∂μ.prod Threshold.fair)
      ≤ κ*(51/1000:ℝ) := by
  by_cases hd : H ∈ B.domain i
  · simp_rw [B.indicator_inside _ i H hd,B.old_indicator_inside _ i H hd]
    rw [(S.labels B.index).lift.distance,sub_self,abs_zero,max_eq_right (abs_nonneg _),
      B.converted_on i H (B.domain_band hd)]
    rw [show κ*B.data.offset+B.data.orientation B.positive*(B.selected i ⟨H,B.domain_band hd⟩).value-
      κ*(B.data.offset+B.data.orientation B.positive*B.comparison.value i ⟨H,B.domain_band hd⟩)=
      B.data.orientation B.positive*((B.selected i ⟨H,B.domain_band hd⟩).value-κ*B.comparison.value i ⟨H,B.domain_band hd⟩) by ring,
      abs_mul,B.data.orientation_unit,one_mul]
    exact B.selected_movement i ⟨H,B.domain_band hd⟩
  · have he (w : Ω × Bool) : (B.patch.apply.activity w).indicator i H=(S.lift.sets.activity w).indicator i H := by
      simp only [Activity.indicator,B.patch.unchanged hd w]
    simp only [he,sub_self,abs_zero,integral_zero]
    exact mul_nonneg B.kappa_nonneg (by norm_num)
end SecondaryBatch

namespace SecondaryLayer
variable (B : SecondaryLayer S)
lemma movement_integrable (i : Fin (k+1)) (H : ℝ) : Integrable
    (fun w => (B.sets.activity w).indicator i H-(S.lift.sets.activity w).indicator i H)
      (μ.prod Threshold.fair) := by
  apply SetPatch.batch_movement_integrable
  intro P hP i H
  obtain ⟨a,rfl⟩ := List.mem_ofFn.mp hP
  exact (B.batch a).movement_integrable i H
lemma movement_bound (hκ : 0 ≤ κ) (i : Fin (k+1)) (H : ℝ) :
    (∫ w, |(B.sets.activity w).indicator i H-(S.lift.sets.activity w).indicator i H| ∂μ.prod Threshold.fair)
      ≤ κ*(51/1000:ℝ) := by
  apply SetPatch.batch_movement _ _ (mul_nonneg hκ (by norm_num))
  intro P hP i H
  obtain ⟨a,rfl⟩ := List.mem_ofFn.mp hP
  exact (B.batch a).movement_bound i H
end SecondaryLayer
end PlanarL1.Columns.Model.BState

end



section

namespace PlanarL1.Columns.Model
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
namespace SetSystem
variable (S T : SetSystem M Ω μ)
lemma separation_survival {J : Set ℝ} {r : Fin (k+1)} (x y : M.Point J r)
    (hmove : ∀ i H, Integrable (fun w => (T.activity w).indicator i H-(S.activity w).indicator i H) μ) :
    S.separation x.column x.height y.column y.height ≤
      T.separation x.column x.height y.column y.height+
        S.movement T x.column x.height+S.movement T y.column y.height := by
  let p := Classical.choice (x.paths_nonempty y)
  have hi := T.unrefined_integrable p x.height y.height
  have hx := (hmove x.column x.height).abs
  have hy := (hmove y.column y.height).abs
  have hp (w : Ω) : |(S.activity w).indicator x.column x.height-(S.activity w).indicator y.column y.height| ≤
      |(T.activity w).indicator x.column x.height-(T.activity w).indicator y.column y.height|+
        |(T.activity w).indicator x.column x.height-(S.activity w).indicator x.column x.height|+
        |(T.activity w).indicator y.column y.height-(S.activity w).indicator y.column y.height| := by
    linarith [abs_sub_le ((S.activity w).indicator x.column x.height)
      ((T.activity w).indicator x.column x.height) ((S.activity w).indicator y.column y.height),
      abs_sub_le ((T.activity w).indicator x.column x.height)
      ((T.activity w).indicator y.column y.height) ((S.activity w).indicator y.column y.height),
      abs_sub_comm ((S.activity w).indicator x.column x.height) ((T.activity w).indicator x.column x.height)]
  have he := integral_mono (S.unrefined_integrable p x.height y.height) ((hi.add hx).add hy) hp
  simp only [Pi.add_apply] at he
  have he1 := integral_add (hi.add hx) hy
  have he2 := integral_add hi hx
  simp only [Pi.add_apply] at he1 he2
  rw [he1,he2] at he
  exact he
end SetSystem

namespace PairGeometry
variable {V : Type*} {A : Ambient M} {S T : OrdinaryState M Parameters.kappaA Ω μ}
variable {v : V → M.Point Set.univ A.root} {x y : V} {b B : ℝ}
lemma Certificate.survive (h : Certificate A S v (x := x) (y := y) b) (hb : 0<b)
    (hmove : ∀ i H, Integrable (fun w => (T.sets.activity w).indicator i H-(S.sets.activity w).indicator i H) μ)
    (hbound : ∀ i H, S.sets.movement T.sets i H≤B) :
    Certificate A T v (x := x) (y := y) (b-3*B) := by
  obtain ⟨a,c,H,E,hH,hac,hsep,hE,hm,hx,hy,hn⟩ := h
  have hfin : μ E<⊤ := by
    by_contra hh
    have ht : μ E=⊤ := top_unique (not_lt.mp hh)
    have hz : μ.real E=0 := by simp [Measure.real,ht]
    linarith
  let F : Set Ω := E ∩ {w | (T.sets.activity w).active (v x).column (v x).height} ∩
      {w | (T.sets.activity w).active (v y).column (v y).height} ∩
      {w | ¬(T.sets.activity w).active a H}
  have hF : MeasurableSet F := ((hE.inter (T.sets.measurable_active _ _)).inter
    (T.sets.measurable_active _ _)).inter (T.sets.measurable_active _ _).compl
  have hFE : F⊆E := fun _ h => h.1.1.1
  have hI : Integrable (E.indicator (fun _ => (1:ℝ))) μ :=
    (integrable_indicator_iff hE).mpr ((integrableOn_const_iff).mpr (Or.inr hfin))
  have hJ : Integrable (F.indicator (fun _ => (1:ℝ))) μ :=
    (integrable_indicator_iff hF).mpr ((integrableOn_const_iff).mpr (Or.inr ((measure_mono hFE).trans_lt hfin)))
  have hC (w : Ω) : E.indicator (fun _ => (1:ℝ)) w ≤
      F.indicator (fun _ => (1:ℝ)) w+
      |(T.sets.activity w).indicator (v x).column (v x).height-(S.sets.activity w).indicator (v x).column (v x).height|+
      |(T.sets.activity w).indicator (v y).column (v y).height-(S.sets.activity w).indicator (v y).column (v y).height|+
      |(T.sets.activity w).indicator a H-(S.sets.activity w).indicator a H| := by
    by_cases hw : w∈E
    · have h1 := hx w hw; have h2 := hy w hw; have h3 := hn w hw
      by_cases htx : (T.sets.activity w).active (v x).column (v x).height <;>
      by_cases hty : (T.sets.activity w).active (v y).column (v y).height <;>
      by_cases hta : (T.sets.activity w).active a H <;>
      simp [F,hw,htx,hty,hta,Activity.indicator,h1,h2,h3]
    · have hf : w∉F := fun he => hw (hFE he)
      simp only [Set.indicator_of_notMem hw,Set.indicator_of_notMem hf,zero_add]
      positivity
  have he := integral_mono hI (((hJ.add (hmove _ _).abs).add (hmove _ _).abs).add (hmove _ _).abs) hC
  simp only [Pi.add_apply] at he
  rw [integral_add,integral_add,integral_add] at he
  · rw [integral_indicator_const _ hE,integral_indicator_const _ hF,smul_eq_mul,smul_eq_mul,mul_one,mul_one] at he
    refine ⟨a,c,H,F,hH,hac,hsep,hF,?_,?_,?_,?_⟩
    · have h1 := hbound (v x).column (v x).height
      have h2 := hbound (v y).column (v y).height
      have h3 := hbound a H
      change (∫ w, |(T.sets.activity w).indicator (v x).column (v x).height-(S.sets.activity w).indicator (v x).column (v x).height| ∂μ)≤B at h1
      change (∫ w, |(T.sets.activity w).indicator (v y).column (v y).height-(S.sets.activity w).indicator (v y).column (v y).height| ∂μ)≤B at h2
      change (∫ w, |(T.sets.activity w).indicator a H-(S.sets.activity w).indicator a H| ∂μ)≤B at h3
      linarith
    · exact fun _ h => h.1.1.2
    · exact fun _ h => h.1.2
    · exact fun _ h => h.2
  all_goals first | exact hJ | exact (hmove _ _).abs | exact hJ.add (hmove _ _).abs | exact (hJ.add (hmove _ _).abs).add (hmove _ _).abs
end PairGeometry
end PlanarL1.Columns.Model

end



section

namespace PlanarL1.Execution
variable {α β : Type*}
def Holds : Execution α → (α → Prop) → Prop
  | .pure x, P => P x
  | .choose _ E, P => ∀ i, Holds (E i) P
lemma holds_of_forall (E : Execution α) {P : α → Prop} (h : ∀ x, P x) : E.Holds P := by
  induction E with
  | pure x => exact h x
  | choose n E ih => exact ih
lemma Holds.mono {E : Execution α} {P Q : α → Prop} (h : E.Holds P)
    (hp : ∀ x, P x → Q x) : E.Holds Q := by
  induction E with
  | pure x => exact hp x h
  | choose n E ih => exact fun i => ih i (h i)
lemma Holds.bind {E : Execution α} {P : α → Prop} (h : E.Holds P)
    (F : α → Execution β) {Q : β → Prop} (hf : ∀ x, P x → (F x).Holds Q) :
    (E.bind F).Holds Q := by
  induction E with
  | pure x => exact hf x h
  | choose n E ih => exact fun i => ih i (h i)
lemma holds_bind_of_forall (E : Execution α) (F : α → Execution β) {Q : β → Prop}
    (h : ∀ x, (F x).Holds Q) : (E.bind F).Holds Q :=
  (E.holds_of_forall (fun _ => True.intro)).bind F (fun x _ => h x)
lemma Holds.mean_mono {E : Execution α} {f g : α → ℝ} (h : E.Holds (fun x => f x≤g x)) :
    E.mean f≤E.mean g := by
  induction E with
  | pure x => exact h
  | choose n E ih =>
      exact div_le_div_of_nonneg_right
        (Finset.sum_le_sum (fun i _ => ih i (h i))) (by positivity)
lemma Holds.prob_mono {E : Execution α} {P Q : α → Prop} (h : E.Holds (fun x => P x → Q x)) :
    E.prob P≤E.prob Q := by
  classical
  apply Holds.mean_mono
  apply h.mono
  intro x hp
  by_cases hx : P x
  · simp [hx,hp hx]
  · simp only [hx,ite_false]; split_ifs <;> norm_num
lemma Holds.prob_eq_one {E : Execution α} {P : α → Prop} (h : E.Holds P) : E.prob P=1 := by
  have hh := h.mono (Q := fun x => True → P x) (fun _ hx _ => hx)
  apply le_antisymm (E.prob_le_one P)
  have he : E.prob (fun _ => True)=1 := by simp [prob,E.mean_const]
  simpa only [he] using hh.prob_mono
lemma Holds.mean_eq {E : Execution α} {f g : α → ℝ} (h : E.Holds (fun x => f x=g x)) :
    E.mean f=E.mean g :=
  le_antisymm (h.mono (fun _ hx => hx.le)).mean_mono (h.mono (fun _ hx => hx.ge)).mean_mono
end PlanarL1.Execution

end



section

namespace PlanarL1.Columns.Model
open MeasureTheory
open scoped NNReal
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
namespace SetSystem
lemma lift_movement (S T : SetSystem M Ω μ) (i : Fin (k+1)) (H : ℝ) :
    S.lift.movement T.lift i H=S.movement T i H := by
  let hp := measurePreserving_fst (μ := μ) (ν := Threshold.fair)
  change (∫ z : Ω × Bool, |(T.activity z.1).indicator i H-(S.activity z.1).indicator i H| ∂μ.prod Threshold.fair)=_
  have he := integral_map_of_stronglyMeasurable (μ := μ.prod Threshold.fair) hp.measurable
    (((T.measurable_indicator i H).sub (S.measurable_indicator i H)).abs.stronglyMeasurable)
  rw [hp.map_eq] at he
  exact he.symm
end SetSystem

namespace BState
variable {κ : ℝ} {lam : ℝ≥0} (S : BState M κ lam Ω μ) (A : Ambient M)
lemma increment_integrable {c r : ℝ}
    (hist : Fin (S.count+1) → A.History c) (sign : Fin (S.count+1) → Bool)
    (hc : 0<c) (hcr : c ≤ 4) (hr : 0<r)
    (hcross : ∀ a j, 10*r ≤ c*(hist a).radius j)
    (hrec : ∀ a, (S.chart a).Recorded (hist a) hc hcr)
    (hk : 0 ≤ κ) (hsmall : κ*5 ≤ 1/2) (hlam : lam ≤ (1:ℝ≥0)/100)
    (hboundary : κ*(lam:ℝ)*10 ≤ 1/8) (i : Fin (k+1)) (H : ℝ) : Integrable
      (fun w => ((S.increment A hist sign hc hcr hr hcross hrec hk hsmall hlam hboundary).sets.activity w).indicator i H-
        (S.sets.activity w).indicator i H) μ := by
  change Integrable (fun w => (S.fieldActivity (S.incrementFields A hist sign hc hcr hr hcross hlam)
    hk hsmall hlam (S.increment_boundary A hist sign hc hcr hr hcross hrec hk hlam hboundary) w).indicator i H-
    (S.sets.activity w).indicator i H) μ
  simp_rw [S.field_indicator,S.old_indicator]
  exact (S.labels (S.name i H)).integrable_difference _ _ _ _
end BState

namespace CoupledState
open Parameters SecondaryGeometry VertexBands
attribute [local instance] Classical.propDecidable
variable {Ξ : Type*} [MeasurableSpace Ξ] {ν : Measure Ξ}
variable {A : Ambient M} {t : ℝ} (S : CoupledState A Ω Ξ μ ν t)
variable {t' : ℝ}
def Moves (T : CoupledState A (Ω × Bool) (Ξ × Bool) (μ.prod Threshold.fair) (ν.prod Threshold.fair) t') (B : ℝ) : Prop :=
  (∀ i H, Integrable (fun w => (T.left.sets.activity w).indicator i H-(S.left.lift.sets.activity w).indicator i H) (μ.prod Threshold.fair)) ∧
  (∀ i H, Integrable (fun w => (T.right.sets.activity w).indicator i H-(S.right.lift.sets.activity w).indicator i H) (ν.prod Threshold.fair)) ∧
  (∀ i H, S.left.lift.sets.movement T.left.sets i H ≤ B) ∧
  (∀ i H, S.right.lift.sets.movement T.right.sets i H ≤ B)

lemma Moves.successful {T : CoupledState A (Ω × Bool) (Ξ × Bool) (μ.prod Threshold.fair) (ν.prod Threshold.fair) t'}
    {B : ℝ} (h : S.Moves T B) (hB : 0 ≤ B) {V : Type*} (v : V → M.Point Set.univ A.root)
    {b : ℝ} {x y : V} (hs : S.Successful v b x y) : T.Successful v (b-3*B) x y := by
  by_cases hb : 0<b
  · have hs' := hs.lift S v
    rcases hs' with hs'|hs'|hs'
    · change b  ≤  S.left.lift.sets.separation (v x).column (v x).height (v y).column (v y).height at hs'
      have he := S.left.lift.sets.separation_survival T.left.sets (v x) (v y) h.1
      exact Or.inl (by linarith [h.2.2.1 (v x).column (v x).height,h.2.2.1 (v y).column (v y).height])
    · change b  ≤  S.right.lift.sets.separation (v x).column (v x).height (v y).column (v y).height at hs'
      have he := S.right.lift.sets.separation_survival T.right.sets (v x) (v y) h.2.1
      exact Or.inr (Or.inl (by linarith [h.2.2.2 (v x).column (v x).height,h.2.2.2 (v y).column (v y).height]))
    · exact Or.inr (Or.inr (hs'.survive hb h.1 h.2.2.1))
  · exact Or.inl (le_trans (by linarith) (T.left.sets.separation_nonneg _ _ _ _))

variable (ht : 1 ≤ t) (hgap : 10 ≤ (R/200)*t)
lemma unchanged_moves : S.Moves (S.unchanged ht) 1 := by
  refine ⟨?_,?_,?_,?_⟩
  · intro i H; simp only [unchanged,weaken,lift,sub_self]; exact integrable_zero _ _ _
  · intro i H; simp only [unchanged,weaken,lift,sub_self]; exact integrable_zero _ _ _
  · intro i H; simp only [SetSystem.movement,Activity.movement,unchanged,weaken,lift,sub_self,abs_zero,integral_zero]; norm_num
  · intro i H; simp only [SetSystem.movement,Activity.movement,unchanged,weaken,lift,sub_self,abs_zero,integral_zero]; norm_num

variable [SFinite μ] [SFinite ν]
variable {V : Type*} [Fintype V] (v : V → M.Point Set.univ A.root) {L U : ℝ}
variable (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q : ℝ} (phaseD : MainFamily.BandComponent (M := M) q L U → ℝ)
variable {m : ℕ} (hm : 0 < m) (p : ℝ) (phaseG : MainFamily.BandComponent (M := M) q L U → ℝ)
omit [SFinite ν] [Fintype V] in
lemma main_moves (omega : MainFamily.Sample phaseD m) : S.Moves (S.main ht phaseD hm omega) 1 := by
  refine ⟨(MainFamily.batch A S.left phaseD hm omega).movement_integrable,?_,?_,?_⟩
  · intro i H; simp only [main,sub_self]; exact integrable_zero _ _ _
  · intro i H
    exact ((MainFamily.batch A S.left phaseD hm omega).movement_bound verticalA.1 i H).trans (by norm_num [kappaA,a₁])
  · intro i H; simp only [SetSystem.movement,Activity.movement,main,sub_self,abs_zero,integral_zero]; norm_num
omit [SFinite μ] in
lemma secondary_moves (omega : SecondaryGeometry.Sample (S.groups v hv phaseD p phaseG) m) :
    S.Moves (S.secondary ht v hv phaseD hm p phaseG omega) 1 := by
  refine ⟨?_,(SecondaryGeometry.layer (S.groups v hv phaseD p phaseG) hm omega).movement_integrable,?_,?_⟩
  · intro i H; simp only [secondary,sub_self]; exact integrable_zero _ _ _
  · intro i H; simp only [SetSystem.movement,Activity.movement,secondary,sub_self,abs_zero,integral_zero]; norm_num
  · intro i H
    exact ((SecondaryGeometry.layer (S.groups v hv phaseD p phaseG) hm omega).movement_bound verticalB.1 i H).trans (by norm_num [kappaB,a₂])
omit [SFinite μ] [SFinite ν] [Fintype V] in
lemma increment_moves (sign : Fin (S.right.count+1) → Bool) : S.Moves (S.increment ht hgap sign) 1 := by
  refine ⟨?_,?_,?_,?_⟩
  · intro i H; simp only [increment,sub_self]; exact integrable_zero _ _ _
  · intro i H
    have hi := S.right.increment_integrable (r := 1) A _ sign (by norm_num [R]) (by norm_num [R]) (by norm_num)
      (by simpa using S.cross hgap) S.histories.recorded verticalB.1 (by norm_num [kappaB,a₂]) Group.lam_bound
      (by change kappaB*lambda*10 ≤ 1/8; norm_num [kappaB,a₂,lambda,R]) i H
    exact (measurePreserving_fst (μ := ν) (ν := Threshold.fair)).integrable_comp_of_integrable hi
  · intro i H; simp only [SetSystem.movement,Activity.movement,increment,sub_self,abs_zero,integral_zero]; norm_num
  · intro i H
    change S.right.sets.lift.movement (IncrementStep.update A S.right S.histories.history (S.cross hgap) S.histories.recorded sign).sets.lift i H ≤ 1
    rw [SetSystem.lift_movement]
    exact (S.right.increment_movement A _ sign (by norm_num [R]) (by norm_num [R]) (by norm_num)
      (by simpa using S.cross hgap) S.histories.recorded verticalB.1 (by norm_num [kappaB,a₂]) Group.lam_bound
      (by change kappaB*lambda*10 ≤ 1/8; norm_num [kappaB,a₂,lambda,R]) i H).trans
      (by change kappaB*lambda*10*1 ≤ 1; norm_num [kappaB,a₂,lambda,R])
lemma modes_moves : (S.modes ht hgap v hv phaseD hm p phaseG).Holds (fun T => S.Moves T 1) := by
  intro i
  fin_cases i
  · exact S.unchanged_moves ht
  · apply Execution.holds_bind_of_forall
    intro omega
    exact S.main_moves ht phaseD hm omega
  · apply Execution.holds_bind_of_forall
    intro omega
    exact S.secondary_moves ht v hv phaseD hm p phaseG omega
  · apply Execution.holds_bind_of_forall
    intro sign
    exact S.increment_moves ht hgap sign
lemma step_moves : (S.step ht hgap v hv hm).Holds (fun T => S.Moves T 1) := by
  apply Execution.holds_bind_of_forall
  intro c
  exact S.modes_moves ht hgap v hv (phase D c.2.1) hm (shift m a₂ c.1.2) (phase g c.2.2)
end CoupledState
end PlanarL1.Columns.Model

end



section

namespace PlanarL1.FiniteRandom
lemma prob_eq_instances {Ω : Type*} (F F' : Fintype Ω) (P : Ω → Prop) :
    @prob Ω F P = @prob Ω F' P := by
  cases Subsingleton.elim F' F
  rfl
lemma prob_bound_of_instances {Ω : Type*} {F F' : Fintype Ω} (P : Ω → Prop) {b : ℝ}
    (h : @prob Ω F' P ≤ b) : @prob Ω F P ≤ b :=
  (prob_eq_instances F F' P).trans_le h
lemma prob_prod_bound_any {Ω Λ : Type*} [Fintype Ω] [Nonempty Ω] [Fintype Λ]
    (F : Fintype (Ω × Λ)) (P : Ω × Λ → Prop) {b : ℝ}
    (h : ∀ w, prob (fun z : Λ => P (w,z)) ≤ b) : @prob (Ω × Λ) F P ≤ b := by
  rw [prob_eq_instances F (instFintypeProd Ω Λ) P]
  exact prob_prod_bound P h
end PlanarL1.FiniteRandom

end

end OAI
