import OAI.Combinatorics.PlanarL1.SecondaryStep
import OAI.Combinatorics.PlanarL1.MainStep

namespace OAI

section

namespace PlanarL1.Columns.Model.BState
open MeasureTheory Set
open scoped NNReal
open PlanarL1.Interpolation
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {κ : ℝ} {lam : ℝ≥0}
  {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- All kept groups with one old identifier and one common orientation. Their
closed domains may overlap in regions where several clippings act. -/
structure SecondaryBatch (S : BState M κ lam Ω μ) where
  index : Fin (S.count+1)
  positive : Bool
  lambda_bound : lam ≤ (1:ℝ≥0)/100
  count : ℕ
  band : Fin count → Set ℝ
  root : Fin count → Fin (k+1)
  step : ∀ q, SecondaryStep S (band q) (root q)
  same_index : ∀ q, (step q).index=index
  same_positive : ∀ q, (step q).positive=positive
  kappa_nonneg : 0 ≤ κ
  kappa_five : κ*5 ≤ 1

namespace SecondaryBatch
variable {S : BState M κ lam Ω μ} (B : SecondaryBatch S)

noncomputable def data : BData M := S.chart B.index
noncomputable def comparison : M.Field B.data.band 5 := B.data.comparison lam B.lambda_bound B.positive

lemma step_data (q : Fin B.count) : (B.step q).data=B.data := by
  simp only [SecondaryStep.data,data,B.same_index]

noncomputable def groupHeight (q : Fin B.count) (H : B.data.band) : (B.step q).data.band :=
  ⟨H.val,by rw [B.step_data]; exact H.property⟩

lemma step_comparison (q : Fin B.count) (i : Fin (k+1)) (H : B.data.band) :
    (B.step q).comparison.value i (B.groupHeight q H)=B.comparison.value i H := by
  have transport (D E : BData M) (he : D=E) (p r : Bool) (hp : p=r)
      (hl hl' : lam ≤ (1:ℝ≥0)/100) (T : E.band) :
      (D.comparison lam hl p).value i ⟨T.val,by rw [he]; exact T.property⟩ =
        (E.comparison lam hl' r).value i T := by
    subst E
    subst r
    rfl
  exact transport (B.step q).data B.data (B.step_data q)
    (B.step q).positive B.positive (B.same_positive q) (B.step q).lambda_bound B.lambda_bound H

noncomputable def groupNamed (q : Fin B.count) (i : Fin (k+1)) (H : B.data.band) : NamedValue :=
  ⟨((B.step q).fullNamed i (B.groupHeight q H)).name,
    κ*((B.step q).fullNamed i (B.groupHeight q H)).value⟩

noncomputable def selected (i : Fin (k+1)) : B.data.band → NamedValue :=
  familySelection (fun H => κ*B.comparison.value i H) (fun q => B.groupNamed q i)

lemma groupNamed_value (q : Fin B.count) (i : Fin (k+1)) (H : B.data.band) :
    (B.groupNamed q i H).value=κ*(B.step q).fullReplacement i (B.groupHeight q H) := by
  simp only [groupNamed,SecondaryStep.fullNamed_value]

lemma comparison_scaled (i : Fin (k+1)) :
    LipschitzWith 1 (fun H : B.data.band => κ*B.comparison.value i H) := by
  apply LipschitzWith.of_dist_le_mul
  intro H T
  have h := (B.comparison.vertical i).dist_le_mul H T
  rw [Real.dist_eq] at h ⊢
  rw [← mul_sub,abs_mul,abs_of_nonneg B.kappa_nonneg]
  calc
    _ ≤ κ*(5*dist H T) := mul_le_mul_of_nonneg_left h B.kappa_nonneg
    _ = (κ*5)*dist H T := by ring
    _ ≤ 1*dist H T := mul_le_mul_of_nonneg_right B.kappa_five dist_nonneg
    _ = _ := by simp

lemma groupNamed_vertical (q : Fin B.count) (i : Fin (k+1)) :
    LipschitzWith 1 (fun H : B.data.band => (B.groupNamed q i H).value) := by
  apply LipschitzWith.of_dist_le_mul
  intro H T
  simp only [B.groupNamed_value]
  exact ((B.step q).fullReplacement_scaled_vertical i).dist_le_mul (B.groupHeight q H) (B.groupHeight q T)

lemma selected_vertical (i : Fin (k+1)) :
    LipschitzWith 1 (fun H : B.data.band => (B.selected i H).value) :=
  familySelection_lipschitz _ _ (B.comparison_scaled i) (fun q => B.groupNamed_vertical q i)

lemma groupNamed_switch (q : Fin B.count) (i j : Fin (k+1)) (H : B.data.band)
    (hs : H.val ∈ M.heights i j) : B.groupNamed q i H=B.groupNamed q j H := by
  unfold groupNamed
  rw [(B.step q).fullNamed_switch i j (B.groupHeight q H) hs]

lemma selected_switch (i j : Fin (k+1)) (H : B.data.band)
    (hs : H.val ∈ M.heights i j) : B.selected i H=B.selected j H := by
  have hm (old : B.data.band → NamedValue) (L : List (B.data.band → NamedValue)) :
      maxSelection old L H=(L.map (fun f => f H)).foldr maxNamed (old H) := by
    induction L with
    | nil => rfl
    | cons f L ih => simp only [maxSelection,List.map_cons,List.foldr_cons,ih]
  unfold selected familySelection
  rw [hm,hm]
  simp only [List.map_ofFn,Function.comp_def,B.comparison.switch i j H hs]
  congr 2
  funext q
  rw [B.groupNamed_switch q i j H hs]

noncomputable def domain (i : Fin (k+1)) : Set ℝ :=
  ⋃ q : Fin B.count, SecondaryCell.domain (B.step q).seeds (B.step q).radius i

lemma mem_domain {i : Fin (k+1)} {H : ℝ} : H ∈ B.domain i ↔
    ∃ q, H ∈ SecondaryCell.domain (B.step q).seeds (B.step q).radius i := mem_iUnion

lemma domain_closed (i : Fin (k+1)) : IsClosed (B.domain i) :=
  isClosed_iUnion_of_finite (fun q => (SecondaryCell.compact_domain (B.step q).seeds
    (B.step q).radius (B.step q).compact_band i).isClosed)

lemma domain_band {i : Fin (k+1)} {H : ℝ} (hd : H ∈ B.domain i) : H ∈ B.data.band := by
  obtain ⟨q,hq⟩ := B.mem_domain.mp hd
  rw [← B.step_data q]
  exact (B.step q).sub_old (SecondaryCell.inBand_of_mem _ _ hq)

lemma domain_name {i : Fin (k+1)} {H : ℝ} (hd : H ∈ B.domain i) : S.name i H=B.index := by
  obtain ⟨q,hq⟩ := B.mem_domain.mp hd
  exact ((B.step q).same_name i H hq).trans (B.same_index q)

lemma domain_switch {i j : Fin (k+1)} {H : ℝ} (hs : H ∈ M.heights i j)
    (hd : H ∈ B.domain i) : H ∈ B.domain j := by
  obtain ⟨q,hq⟩ := B.mem_domain.mp hd
  exact B.mem_domain.mpr ⟨q,SecondaryCell.switch_mem _ _ hs hq⟩

lemma group_frontier {i : Fin (k+1)} {H : ℝ} (hf : H ∈ frontier (B.domain i))
    (q : Fin B.count) (hq : H ∈ SecondaryCell.domain (B.step q).seeds (B.step q).radius i) :
    H ∈ frontier (SecondaryCell.domain (B.step q).seeds (B.step q).radius i) := by
  refine ⟨subset_closure hq,?_⟩
  intro ht
  exact hf.2 (interior_mono (subset_iUnion (fun q : Fin B.count =>
    SecondaryCell.domain (B.step q).seeds (B.step q).radius i) q) ht)

lemma selected_same {i : Fin (k+1)} (H : B.data.band)
    (h : ∀ q, (B.groupNamed q i H).value=κ*B.comparison.value i H) :
    (B.selected i H).value=κ*B.comparison.value i H := by
  rcases maxSelection_mem (fun H => ⟨0,κ*B.comparison.value i H⟩)
    (List.ofFn (fun q => fun H => ⟨familyName q (B.groupNamed q i H).name,(B.groupNamed q i H).value⟩)) H with ho | ⟨F,hF,hFv⟩
  · exact congrArg NamedValue.value ho
  · obtain ⟨q,rfl⟩ := List.mem_ofFn.mp hF
    exact (congrArg NamedValue.value hFv).trans (h q)

lemma selected_frontier {i : Fin (k+1)} {H : ℝ} (hf : H ∈ frontier (B.domain i)) :
    (B.selected i ⟨H,B.domain_band ((B.domain_closed i).frontier_subset hf)⟩).value=
      κ*B.comparison.value i ⟨H,B.domain_band ((B.domain_closed i).frontier_subset hf)⟩ := by
  apply B.selected_same
  intro q
  rw [B.groupNamed_value]
  by_cases hq : H ∈ SecondaryCell.domain (B.step q).seeds (B.step q).radius i
  · rw [(B.step q).fullReplacement_inside _ _ hq]
    change κ*(B.step q).replacement (SecondaryCell.point (B.step q).seeds (B.step q).radius i H hq)=_
    rw [(B.step q).replacement_frontier (B.group_frontier hf q hq) hq,(B.step q).point_old hq]
    congr 1
    exact B.step_comparison q i ⟨H,B.domain_band ((B.domain_closed i).frontier_subset hf)⟩
  · rw [(B.step q).fullReplacement_outside _ _ hq,B.step_comparison]

noncomputable def converted (i : Fin (k+1)) (H : ℝ) : ℝ :=
  if h : H ∈ B.data.band then κ*B.data.offset+B.data.orientation B.positive*(B.selected i ⟨H,h⟩).value else 0

lemma converted_on (i : Fin (k+1)) (H : ℝ) (h : H ∈ B.data.band) :
    B.converted i H=κ*B.data.offset+B.data.orientation B.positive*(B.selected i ⟨H,h⟩).value := dite_eq_left h

lemma converted_vertical (i : Fin (k+1)) : LipschitzOnWith 1 (B.converted i) (B.domain i) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro H hH T hT
  rw [B.converted_on i H (B.domain_band hH),B.converted_on i T (B.domain_band hT)]
  have h := (B.selected_vertical i).dist_le_mul ⟨H,B.domain_band hH⟩ ⟨T,B.domain_band hT⟩
  rw [Real.dist_eq] at h ⊢
  simp only [add_sub_add_left_eq_sub,← mul_sub,abs_mul,B.data.orientation_unit,one_mul]
  exact h

noncomputable def patch : SetPatch S.lift.sets := by
  apply Threshold.chartPatch S.lift.sets (S.labels B.index).lift B.domain B.domain_closed
    B.converted B.converted_vertical
  · intro ω i H hf
    have hd := (B.domain_closed i).frontier_subset hf
    have hb := B.domain_band hd
    rw [B.converted_on i H hb,B.selected_frontier hf]
    have he := B.data.comparison_convert lam B.lambda_bound B.positive i ⟨H,hb⟩
    have hr := S.represents_named ω.1 i H B.index (B.domain_name hd) hb
    change Threshold.active (S.labels B.index) H _ ω.1 ↔ (S.sets.activity ω.1).active i H
    have hv : κ*B.data.offset+B.data.orientation B.positive*(κ*B.comparison.value i ⟨H,hb⟩)=
        κ*B.data.value lam i ⟨H,hb⟩ := by
      rw [he]
      change _=κ*(B.data.offset+B.data.orientation B.positive*B.comparison.value i ⟨H,hb⟩)
      ring
    rw [hv]
    exact hr.symm
  · intro i j H hs hi hj
    rw [B.converted_on i H (B.domain_band hi),B.converted_on j H (B.domain_band hj),B.selected_switch i j _ hs]
  · intro ω i j H hs hi hj
    exact (hj (B.domain_switch hs hi)).elim

lemma selected_cases (i : Fin (k+1)) (H : B.data.band) :
    B.selected i H=⟨0,κ*B.comparison.value i H⟩ ∨
      ∃ q, B.selected i H=⟨familyName q (B.groupNamed q i H).name,(B.groupNamed q i H).value⟩ := by
  rcases maxSelection_mem (fun H => ⟨0,κ*B.comparison.value i H⟩)
    (List.ofFn (fun q => fun H => ⟨familyName q (B.groupNamed q i H).name,(B.groupNamed q i H).value⟩)) H with ho | ⟨F,hF,hFv⟩
  · exact Or.inl ho
  · obtain ⟨q,rfl⟩ := List.mem_ofFn.mp hF
    exact Or.inr ⟨q,hFv⟩

lemma selected_zero (i : Fin (k+1)) (H : B.data.band) (hz : (B.selected i H).name=0) :
    (B.selected i H).value=κ*B.comparison.value i H := by
  rcases B.selected_cases i H with ho | ⟨q,hq⟩
  · exact congrArg NamedValue.value ho
  · have hn : (B.groupNamed q i H).name=0 := by
      by_contra hn
      exact familyName_ne_zero q hn ((congrArg NamedValue.name hq).symm.trans hz)
    have hv := (B.step q).fullNamed_zero i (B.groupHeight q H) hn
    have hm := congrArg NamedValue.value hq
    change (B.selected i H).value=κ*((B.step q).fullNamed i (B.groupHeight q H)).value at hm
    rw [hm,hv,B.step_comparison]

abbrev NewIndex := Σ q : Fin B.count, Fin (3*(k+1)*(B.step q).tree.depthCap+2)
noncomputable instance : Fintype B.NewIndex := inferInstanceAs (Fintype (Sigma _))

noncomputable def chosen (i : Fin (k+1)) (H : ℝ) (a : B.NewIndex) : Prop :=
  ∃ hb : H ∈ B.data.band, (B.step a.1).choose i H=some a.2 ∧
    B.selected i ⟨H,hb⟩=⟨familyName a.1 (a.2.val+1),(B.groupNamed a.1 i ⟨H,hb⟩).value⟩

noncomputable def choose (i : Fin (k+1)) (H : ℝ) : Option B.NewIndex :=
  if h : ∃ a, B.chosen i H a then some h.choose else none

lemma choose_some (i : Fin (k+1)) (H : ℝ) (a : B.NewIndex)
    (ha : B.choose i H=some a) : B.chosen i H a := by
  unfold choose at ha
  split_ifs at ha with h
  · have he : h.choose=a := Option.some.inj ha
    exact he ▸ h.choose_spec

lemma none_no_chosen (i : Fin (k+1)) (H : ℝ) (hn : B.choose i H=none) :
    ¬∃ a, B.chosen i H a := by
  intro h
  simp only [choose,dite_eq_left h] at hn
  cases hn

lemma exists_chosen (i : Fin (k+1)) (H : B.data.band) (hn : (B.selected i H).name ≠ 0) :
    ∃ a, B.chosen i H.val a := by
  rcases B.selected_cases i H with ho | ⟨q,hq⟩
  · exact (hn (congrArg NamedValue.name ho)).elim
  · have hqn : ((B.step q).fullNamed i (B.groupHeight q H)).name ≠ 0 := by
      intro hz
      have hn' := congrArg NamedValue.name hq
      change (B.selected i H).name=familyName q ((B.step q).fullNamed i (B.groupHeight q H)).name at hn'
      rw [hz,familyName_zero] at hn'
      exact hn hn'
    obtain ⟨a,ha,hname,hd⟩ := (B.step q).fullNamed_choice i (B.groupHeight q H) hqn
    refine ⟨(⟨q,a⟩ : B.NewIndex),H.property,ha,?_⟩
    change B.selected i H=⟨familyName q (a.val+1),(B.groupNamed q i H).value⟩
    rw [hq]
    change (NamedValue.mk (familyName q ((B.step q).fullNamed i (B.groupHeight q H)).name)
      (B.groupNamed q i H).value)=_
    rw [hname]

lemma chosen_switch (i j : Fin (k+1)) (H : ℝ) (hs : H ∈ M.heights i j) (a : B.NewIndex) :
    B.chosen i H a ↔ B.chosen j H a := by
  unfold chosen
  apply exists_congr
  intro hb
  rw [(B.step a.1).choose_switch i j H hs,B.selected_switch i j ⟨H,hb⟩ hs,
    B.groupNamed_switch a.1 i j ⟨H,hb⟩ hs]

lemma choose_switch (i j : Fin (k+1)) (H : ℝ) (hs : H ∈ M.heights i j) :
    B.choose i H=B.choose j H := by
  have he : B.chosen i H=B.chosen j H := funext fun a => propext (B.chosen_switch i j H hs a)
  unfold choose
  simp only [he]

noncomputable def newData (a : B.NewIndex) : BData M := (B.step a.1).newData a.2
noncomputable def newLabels [SFinite μ] (a : B.NewIndex) :
    Threshold.Variables (Ω × Bool) (μ.prod Threshold.fair) := (B.step a.1).newLabels a.2

lemma chosen_domain (i : Fin (k+1)) (H : ℝ) (a : B.NewIndex) (ha : B.chosen i H a) :
    H ∈ SecondaryCell.domain (B.step a.1).seeds (B.step a.1).radius i := by
  obtain ⟨hb,hc,he⟩ := ha
  obtain ⟨hd,-⟩ := SecondaryCell.choose_spec (B.step a.1).tree (B.step a.1).seeds
    (B.step a.1).old (B.step a.1).supportValue (B.step a.1).data.isOrdinary
    (B.step a.1).pc (B.step a.1).radius (B.step a.1).ordered_offset (B.step a.1).shield_offset
    (B.step a.1).lo (B.step a.1).noise i H a.2 hc
  exact hd

lemma converted_chosen (i : Fin (k+1)) (H : ℝ) (a : B.NewIndex) (ha : B.chosen i H a) :
    B.converted i H=κ*((B.step a.1).data.offset+(B.step a.1).data.orientation (B.step a.1).positive*
      (B.step a.1).replacement (SecondaryCell.point (B.step a.1).seeds (B.step a.1).radius i H
        (B.chosen_domain i H a ha))) := by
  obtain ⟨hb,hc,he⟩ := ha
  have hv : (B.selected i ⟨H,hb⟩).value=κ*(B.step a.1).replacement
      (SecondaryCell.point (B.step a.1).seeds (B.step a.1).radius i H
        (B.chosen_domain i H a ⟨hb,hc,he⟩)) := by
    calc
      _ = (B.groupNamed a.1 i ⟨H,hb⟩).value := by
        have h := congrArg NamedValue.value he
        exact h
      _ = κ*(B.step a.1).fullReplacement i (B.groupHeight a.1 ⟨H,hb⟩) :=
        B.groupNamed_value a.1 i ⟨H,hb⟩
      _ = _ := congrArg (κ*·) ((B.step a.1).fullReplacement_inside i
        (B.groupHeight a.1 ⟨H,hb⟩) (B.chosen_domain i H a ⟨hb,hc,he⟩))
  simp only [B.converted_on i H hb,hv]
  have hoff := congrArg BData.offset (B.step_data a.1)
  have hor : (B.step a.1).data.orientation (B.step a.1).positive=B.data.orientation B.positive := by
    rw [B.same_positive,B.step_data]
  rw [hoff,hor]
  change κ*B.data.offset+B.data.orientation B.positive*(κ*(B.step a.1).replacement _)=_
  ring

lemma chosen_agreement (ω : Ω × Bool) (i : Fin (k+1)) (H : ℝ) (a : B.NewIndex)
    (ha : B.chosen i H a) :
    (B.patch.apply.activity ω).active i H ↔ ((B.step a.1).patch.apply.activity ω).active i H := by
  have hd := B.chosen_domain i H a ha
  apply (B.patch.inside (B.mem_domain.mpr ⟨a.1,hd⟩) ω).trans
  change Threshold.active (S.labels B.index).lift H (B.converted i H) ω ↔ _
  rw [B.converted_chosen i H a ha]
  have hp := (B.step a.1).patch_inside ω i H hd
  rw [B.same_index] at hp
  exact hp.symm

lemma chosen_description [SFinite μ] (i : Fin (k+1)) (H : ℝ) (a : B.NewIndex)
    (ha : B.chosen i H a) :
    (H ∈ (B.newData a).band ∧ (B.newData a).Uses i) ∧
      ∀ (ω : Ω × Bool) (hi : H ∈ (B.newData a).band),
        (B.patch.apply.activity ω).active i H ↔
          Threshold.active (B.newLabels a) H (κ*(B.newData a).value lam i ⟨H,hi⟩) ω := by
  obtain ⟨hb,hc,he⟩ := ha
  have h := (B.step a.1).chosen_description i H a.2 hc
  refine ⟨h.1,fun ω hi => ?_⟩
  exact (B.chosen_agreement ω i H a ⟨hb,hc,he⟩).trans (h.2 ω hi)

lemma unchosen (ω : Ω × Bool) (i : Fin (k+1)) (H : ℝ) (hn : B.choose i H=none) :
    (B.patch.apply.activity ω).active i H ↔ (S.lift.sets.activity ω).active i H := by
  by_cases hd : H ∈ B.domain i
  · have hb := B.domain_band hd
    have hz : (B.selected i ⟨H,hb⟩).name=0 := by
      by_contra hz
      exact B.none_no_chosen i H hn (B.exists_chosen i ⟨H,hb⟩ hz)
    apply (B.patch.inside hd ω).trans
    change Threshold.active (S.labels B.index).lift H (B.converted i H) ω ↔ _
    rw [B.converted_on i H hb,B.selected_zero i ⟨H,hb⟩ hz]
    have he := B.data.comparison_convert lam B.lambda_bound B.positive i ⟨H,hb⟩
    have hr := S.represents_named ω.1 i H B.index (B.domain_name hd) hb
    change Threshold.active (S.labels B.index) H _ ω.1 ↔ (S.sets.activity ω.1).active i H
    have hv : κ*B.data.offset+B.data.orientation B.positive*(κ*B.comparison.value i ⟨H,hb⟩)=
        κ*B.data.value lam i ⟨H,hb⟩ := by
      rw [he]
      change _=κ*(B.data.offset+B.data.orientation B.positive*B.comparison.value i ⟨H,hb⟩)
      ring
    rw [hv]
    exact hr.symm
  · exact B.patch.unchanged hd ω

/-- Literal finite maximum of overlapping secondary proposals, with the exact
winning chart table and label variables. No sum over group movements is used. -/
noncomputable def apply [SFinite μ] : BState M κ lam (Ω × Bool) (μ.prod Threshold.fair) := by
  let e := Fintype.equivFin B.NewIndex
  let pick : Fin (k+1) → ℝ → Option (Fin (Fintype.card B.NewIndex)) :=
    fun i H => (B.choose i H).map e
  have hpick (i H a) (ha : pick i H=some a) : B.chosen i H (e.symm a) := by
    obtain ⟨b,hb,hba⟩ := Option.map_eq_some_iff.mp ha
    have he : b=e.symm a := by rw [← hba]; simp
    exact he ▸ B.choose_some i H b hb
  exact S.lift.append B.patch.apply (Fintype.card B.NewIndex)
    (B.newData ∘ e.symm) (B.newLabels ∘ e.symm) pick
    (fun i H a ha => (B.chosen_description i H (e.symm a) (hpick i H a ha)).1.1)
    (fun i H a ha => (B.chosen_description i H (e.symm a) (hpick i H a ha)).1.2)
    (fun i j H hs => congrArg (Option.map e) (B.choose_switch i j H hs))
    (fun ω i H ha => B.unchosen ω i H (Option.map_eq_none_iff.mp ha))
    (fun ω i H a ha => (B.chosen_description i H (e.symm a) (hpick i H a ha)).2 ω _)

end SecondaryBatch
end PlanarL1.Columns.Model.BState


end

section

namespace PlanarL1.Columns.Model.BState
open MeasureTheory
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {κ : ℝ} {lam : ℝ≥0}
  {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The simultaneous secondary update, grouped by its actual old identifier.
Within an identifier we take a maximum, not disjoint patching. Distinct old
identifiers have disjoint domains because the old chart name is a function. -/
structure SecondaryLayer (S : BState M κ lam Ω μ) where
  batch : Fin (S.count+1) → SecondaryBatch S
  same_index : ∀ q, (batch q).index=q

namespace SecondaryLayer
variable {S : BState M κ lam Ω μ} (B : SecondaryLayer S)

lemma overlap : (List.ofFn (fun q => (B.batch q).patch)).Pairwise SetPatch.UnchangedOverlap := by
  apply List.pairwise_ofFn.mpr
  intro q r hqr ω i H hq hr
  have hq' := (B.batch q).domain_name hq
  have hr' := (B.batch r).domain_name hr
  rw [B.same_index] at hq' hr'
  exact ((ne_of_lt hqr) (hq'.symm.trans hr')).elim

abbrev NewIndex := Σ q : Fin (S.count+1), (B.batch q).NewIndex
noncomputable instance : Fintype B.NewIndex := inferInstanceAs (Fintype (Sigma _))

noncomputable def newData (a : B.NewIndex) : BData M := (B.batch a.1).newData a.2
noncomputable def newLabels [SFinite μ] (a : B.NewIndex) :
    Threshold.Variables (Ω × Bool) (μ.prod Threshold.fair) := (B.batch a.1).newLabels a.2

noncomputable def chosen (i : Fin (k+1)) (H : ℝ) (a : B.NewIndex) : Prop :=
  (B.batch a.1).choose i H=some a.2

noncomputable def choose (i : Fin (k+1)) (H : ℝ) : Option B.NewIndex :=
  if h : ∃ a, B.chosen i H a then some h.choose else none

lemma choose_some (i : Fin (k+1)) (H : ℝ) (a : B.NewIndex)
    (ha : B.choose i H=some a) : B.chosen i H a := by
  unfold choose at ha
  split_ifs at ha with h
  · have he : h.choose=a := Option.some.inj ha
    exact he ▸ h.choose_spec

lemma choose_none (i : Fin (k+1)) (H : ℝ) (ha : B.choose i H=none) (q : Fin (S.count+1)) :
    (B.batch q).choose i H=none := by
  cases he : (B.batch q).choose i H with
  | none => rfl
  | some a =>
    have hex : ∃ a, B.chosen i H a := ⟨⟨q,a⟩,he⟩
    simp [choose,hex] at ha

lemma choose_switch (i j : Fin (k+1)) (H : ℝ) (hs : H ∈ M.heights i j) :
    B.choose i H=B.choose j H := by
  have he : B.chosen i H=B.chosen j H := by
    funext a
    simp only [chosen,(B.batch a.1).choose_switch i j H hs]
  unfold choose
  simp only [he]

noncomputable def sets : SetSystem M (Ω × Bool) (μ.prod Threshold.fair) :=
  SetPatch.batch (List.ofFn (fun q => (B.batch q).patch)) B.overlap

lemma chosen_description [SFinite μ] (i : Fin (k+1)) (H : ℝ) (a : B.NewIndex)
    (ha : B.chosen i H a) :
    (H ∈ (B.newData a).band ∧ (B.newData a).Uses i) ∧
    ∀ (ω : Ω × Bool) (hi : H ∈ (B.newData a).band),
      (B.sets.activity ω).active i H ↔
        Threshold.active (B.newLabels a) H (κ*(B.newData a).value lam i ⟨H,hi⟩) ω := by
  have ha' := (B.batch a.1).choose_some i H a.2 ha
  have hd := (B.batch a.1).chosen_domain i H a.2 ha'
  have h := (B.batch a.1).chosen_description i H a.2 ha'
  refine ⟨h.1,fun ω hi => ?_⟩
  apply (SetPatch.batch_inside _ B.overlap (List.mem_ofFn.mpr ⟨a.1,rfl⟩) ω i H
    ((B.batch a.1).mem_domain.mpr ⟨a.2.1,hd⟩)).trans
  exact h.2 ω hi

lemma unchosen (ω : Ω × Bool) (i : Fin (k+1)) (H : ℝ) (ha : B.choose i H=none) :
    (B.sets.activity ω).active i H ↔ (S.lift.sets.activity ω).active i H := by
  apply SetPatch.batch_old _ B.overlap ω i H
  intro P hP
  obtain ⟨q,rfl⟩ := List.mem_ofFn.mp hP
  exact (B.batch q).unchosen ω i H (B.choose_none i H ha q)

/-- The actual simultaneous layer and selected ordinary/ordered chart table. -/
noncomputable def apply [SFinite μ] : BState M κ lam (Ω × Bool) (μ.prod Threshold.fair) := by
  let e := Fintype.equivFin B.NewIndex
  let pick : Fin (k+1) → ℝ → Option (Fin (Fintype.card B.NewIndex)) :=
    fun i H => (B.choose i H).map e
  have hpick (i H a) (ha : pick i H=some a) : B.chosen i H (e.symm a) := by
    obtain ⟨b,hb,hba⟩ := Option.map_eq_some_iff.mp ha
    have he : b=e.symm a := by rw [← hba]; simp
    exact he ▸ B.choose_some i H b hb
  exact S.lift.append B.sets (Fintype.card B.NewIndex)
    (B.newData ∘ e.symm) (B.newLabels ∘ e.symm) pick
    (fun i H a ha => (B.chosen_description i H (e.symm a) (hpick i H a ha)).1.1)
    (fun i H a ha => (B.chosen_description i H (e.symm a) (hpick i H a ha)).1.2)
    (fun i j H hs => congrArg (Option.map e) (B.choose_switch i j H hs))
    (fun ω i H ha => B.unchosen ω i H (Option.map_eq_none_iff.mp ha))
    (fun ω i H a ha => (B.chosen_description i H (e.symm a) (hpick i H a ha)).2 ω _)

end SecondaryLayer
end PlanarL1.Columns.Model.BState



end

end OAI
