import OAI.Combinatorics.PlanarL1.OrdinaryState
import OAI.Combinatorics.PlanarL1.FiniteL1

namespace OAI

section

namespace PlanarL1.Columns.Model
open MeasureTheory
open scoped NNReal
attribute [local instance] Classical.propDecidable

namespace OrdinaryState
variable {n : ℕ} {M : Model n} {κ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma represents_named (S : OrdinaryState M κ Ω μ) (ω : Ω) (i : Fin n) (H : ℝ)
    (a : Fin (S.count+1)) (he : S.name i H=a) (hi : H ∈ (S.chart a).band) :
    (S.sets.activity ω).active i H ↔
      Threshold.active (S.labels a) H (κ*(S.chart a).value i ⟨H,hi⟩) ω := by
  subst a
  exact S.represents ω i H

lemma contains_named (S : OrdinaryState M κ Ω μ) (i : Fin n) (H : ℝ)
    (a : Fin (S.count+1)) (he : S.name i H=a) : (S.chart a).Contains i H := by
  subst a
  exact ⟨S.height_in i H,S.component_in i H⟩

/-- Literal deterministic data of a kept eligible main cell. Fresh signs are
label coordinates, not assumptions of independence between existing labels. -/
structure MainStep (S : OrdinaryState M κ Ω μ) (J : Set ℝ) (root : Fin n) where
  index : Fin (S.count+1)
  tree : Point.RadialTree (M := M) (J := J) (root := root)
  phase : ℝ
  cell : MainCell.Cell tree phase
  anchor : M.Point J root
  anchor_mem : anchor.column ∈ ColumnOrder.componentColumns cell
  lo : ℝ
  band_eq : J=Set.Icc lo (lo+tree.a)
  thin : tree.a ≤ (1/1000:ℝ)/1000
  sub_old : J ⊆ (S.chart index).band
  same_name : ∀ i H, H ∈ MainCell.domain tree phase cell i → S.name i H=index
  noise : Point.RadialTree.Noise (n := n)
  noise_bounds : tree.NoiseBounds noise
  error : ℝ
  error_pos : 0<error
  delta_eq : tree.δ=error/8
  shield_offset : ℝ
  shield_bound : shield_offset ≤ (1:ℝ)/100
  kappa_nonneg : 0≤κ
  vertical_bound : κ*(MainCell.replacementConstant tree : ℝ) ≤ 1
  shield_strict : κ*(3/(9*tree.a/100)) < 1

namespace MainStep
variable {S : OrdinaryState M κ Ω μ} {J : Set ℝ} {root : Fin n}
variable (U : MainStep S J root)

noncomputable def data : OrdinaryData M := S.chart U.index
noncomputable def comparison : M.Field U.data.band 1 := U.data.comparison

include U in
lemma compact_band : IsCompact J := by rw [U.band_eq]; exact isCompact_Icc

lemma old_agreement (ω : Ω × Bool) (i : Fin n) (H : ℝ)
    (hi : H ∈ MainCell.domain U.tree U.phase U.cell i) :
    Threshold.active ((S.labels U.index).lift) H
      (κ*(U.data.constant+U.data.orientation*MainCell.old U.comparison U.sub_old
        (MainCell.cellPoint U.tree U.phase U.cell i H hi))) ω ↔
      (S.lift.sets.activity ω).active i H := by
  exact (S.represents_named ω.1 i H U.index (U.same_name i H hi)
    (U.sub_old ((MainCell.mem_domain U.tree U.phase U.cell).mp hi).2)).symm

noncomputable def patch : SetPatch S.lift.sets :=
  MainCell.patch U.comparison U.sub_old U.tree U.phase U.cell
    S.lift.sets (S.labels U.index).lift U.compact_band U.lo U.band_eq U.thin
    U.anchor U.anchor_mem U.noise_bounds U.error U.shield_offset U.data.constant
    U.data.orientation κ U.error_pos.le U.delta_eq U.shield_bound
    U.data.unit_orientation U.kappa_nonneg U.vertical_bound U.old_agreement

noncomputable def input : M.Point J root → ℝ :=
  MainCell.input U.comparison U.sub_old U.tree U.phase U.cell U.anchor

noncomputable def shield (H : ℝ) : ℝ :=
  κ*(U.data.constant+U.data.orientation*Clipping.heightShield U.lo U.tree.a
    (MainCell.old U.comparison U.sub_old U.anchor) U.shield_offset H)

noncomputable def shieldConstant : ℝ≥0 :=
  ⟨κ*(3/(9*U.tree.a/100)),mul_nonneg U.kappa_nonneg (by positivity [U.tree.width_pos])⟩

lemma shield_lipschitz : LipschitzWith U.shieldConstant U.shield := by
  apply LipschitzWith.of_dist_le_mul
  intro H T
  have ht := (Clipping.heightShield_lipschitz U.lo
    (MainCell.old U.comparison U.sub_old U.anchor) U.shield_offset U.tree.width_pos).dist_le_mul H T
  rw [Real.dist_eq] at ht
  change |shield U H-shield U T| ≤ (κ*(3/(9*U.tree.a/100)))*dist H T
  unfold shield
  rw [show κ*(U.data.constant+U.data.orientation*Clipping.heightShield U.lo U.tree.a
      (MainCell.old U.comparison U.sub_old U.anchor) U.shield_offset H)-
    κ*(U.data.constant+U.data.orientation*Clipping.heightShield U.lo U.tree.a
      (MainCell.old U.comparison U.sub_old U.anchor) U.shield_offset T) =
    κ*U.data.orientation*(Clipping.heightShield U.lo U.tree.a
      (MainCell.old U.comparison U.sub_old U.anchor) U.shield_offset H-
    Clipping.heightShield U.lo U.tree.a
      (MainCell.old U.comparison U.sub_old U.anchor) U.shield_offset T) by ring,
    abs_mul,abs_mul,abs_of_nonneg U.kappa_nonneg,U.data.unit_orientation,mul_one]
  exact (mul_le_mul_of_nonneg_left ht U.kappa_nonneg).trans_eq (mul_assoc _ _ _).symm

noncomputable def newData (a : Fin (3*n*U.tree.depthCap+1)) : OrdinaryData M :=
  if a.val=0 then OrdinaryData.initial M else U.tree.atomChart U.data U.input U.noise U.error (a.val-1)

noncomputable def newLabels [SFinite μ] (a : Fin (3*n*U.tree.depthCap+1)) :
    Threshold.Variables (Ω × Bool) (μ.prod Threshold.fair) :=
  if a.val=0 then (S.labels U.index).rebase (K := U.shieldConstant) U.shield_strict U.shield_lipschitz
    else (S.labels U.index).lift

noncomputable def choose : Fin n → ℝ → Option (Fin (3*n*U.tree.depthCap+1)) :=
  MainCell.choose U.comparison U.sub_old U.tree U.phase U.cell U.anchor U.noise
    U.error U.shield_offset U.lo

lemma patch_inside (ω : Ω × Bool) (i : Fin n) (H : ℝ)
    (hi : H ∈ MainCell.domain U.tree U.phase U.cell i) :
    (U.patch.apply.activity ω).active i H ↔
      Threshold.active (S.labels U.index).lift H
        (κ*(U.data.constant+U.data.orientation*MainCell.replacement U.comparison U.sub_old
          U.tree U.phase U.cell U.anchor U.noise U.error U.shield_offset U.lo
            (MainCell.cellPoint U.tree U.phase U.cell i H hi))) ω := by
  apply (U.patch.inside hi ω).trans
  change Threshold.active _ H (MainCell.converted U.comparison U.sub_old U.tree U.phase
    U.cell U.anchor U.noise U.error U.shield_offset U.lo U.data.constant U.data.orientation κ i H) ω ↔ _
  rw [MainCell.converted_on U.comparison U.sub_old U.tree U.phase U.cell U.anchor U.noise
    U.error U.shield_offset U.lo U.data.constant U.data.orientation κ hi]

lemma chosen_description [SFinite μ] (i : Fin n) (H : ℝ)
    (a : Fin (3*n*U.tree.depthCap+1)) (hc : U.choose i H=some a) :
    (U.newData a).Contains i H ∧ ∀ (ω : Ω × Bool) (hi : H ∈ (U.newData a).band),
      (U.patch.apply.activity ω).active i H ↔
        Threshold.active (U.newLabels a) H (κ*(U.newData a).value i ⟨H,hi⟩) ω := by
  let Q (D : OrdinaryData M) (Z : Threshold.Variables (Ω × Bool) (μ.prod Threshold.fair)) : Prop :=
    D.Contains i H ∧ ∀ (ω : Ω × Bool) (hi : H ∈ D.band),
      (U.patch.apply.activity ω).active i H ↔ Threshold.active Z H (κ*D.value i ⟨H,hi⟩) ω
  change Q (U.newData a) (U.newLabels a)
  obtain ⟨hd,hn⟩ := MainCell.choose_spec U.comparison U.sub_old U.tree U.phase U.cell U.anchor
    U.noise U.error U.shield_offset U.lo i H a hc
  let x := MainCell.cellPoint U.tree U.phase U.cell i H hd
  change (MainCell.namedReplacement U.comparison U.sub_old U.tree U.phase U.cell U.anchor
    U.noise U.error U.shield_offset U.lo x).name=a.val+1 at hn
  rcases MainCell.namedReplacement_cases U.comparison U.sub_old U.tree U.phase U.cell U.anchor
    U.noise U.error U.shield_offset U.lo x with ho | hh | hp
  · have hn' := congrArg PlanarL1.Interpolation.NamedValue.name ho
    change _=0 at hn'
    omega
  · have hn' := congrArg PlanarL1.Interpolation.NamedValue.name hh
    change _=1 at hn'
    have ha0 : a.val=0 := by omega
    simp only [newData,newLabels,ite_eq_left ha0]
    refine ⟨OrdinaryData.initial_contains i H,?_⟩
    intro ω hi
    have hv : MainCell.replacement U.comparison U.sub_old U.tree U.phase U.cell U.anchor
        U.noise U.error U.shield_offset U.lo x =
        Clipping.heightShield U.lo U.tree.a (MainCell.old U.comparison U.sub_old U.anchor)
          U.shield_offset H := by
      rw [← MainCell.namedReplacement_value U.comparison U.sub_old U.tree U.phase U.cell
        U.anchor U.noise U.error U.shield_offset U.lo x,hh]
      rfl
    have h0 := U.patch_inside ω i H hd
    change _ ↔ Threshold.active _ H (κ*(U.data.constant+U.data.orientation*
      MainCell.replacement U.comparison U.sub_old U.tree U.phase U.cell U.anchor U.noise
        U.error U.shield_offset U.lo x)) ω at h0
    rw [hv] at h0
    simpa only [OrdinaryData.initial_value,mul_zero] using
      h0.trans ((S.labels U.index).active_rebase (K := U.shieldConstant) U.shield_strict U.shield_lipschitz H ω)
  · have hn' := congrArg PlanarL1.Interpolation.NamedValue.name hp
    change _=(U.tree.pasted U.input U.noise x).name+2 at hn'
    have ha0 : a.val≠0 := by omega
    have ha1 : a.val-1=(U.tree.pasted U.input U.noise x).name := by omega
    simp only [newData,newLabels,ite_eq_right ha0,ha1]
    refine ⟨U.tree.atomChart_contains U.data U.input U.noise U.error x,?_⟩
    intro ω hi
    obtain ⟨hb,hvalue⟩ := U.tree.atomChart_value U.data U.input U.noise U.error x
    have hv : MainCell.replacement U.comparison U.sub_old U.tree U.phase U.cell U.anchor
        U.noise U.error U.shield_offset U.lo x = (U.tree.pasted U.input U.noise x).value-4*U.error := by
      rw [← MainCell.namedReplacement_value U.comparison U.sub_old U.tree U.phase U.cell
        U.anchor U.noise U.error U.shield_offset U.lo x,hp]
      rfl
    have h0 := U.patch_inside ω i H hd
    change _ ↔ Threshold.active _ H (κ*(U.data.constant+U.data.orientation*
      MainCell.replacement U.comparison U.sub_old U.tree U.phase U.cell U.anchor U.noise
        U.error U.shield_offset U.lo x)) ω at h0
    rw [hv] at h0
    exact h0.trans (Iff.of_eq (congrArg (fun p => Threshold.active (S.labels U.index).lift H (κ*p) ω)
      hvalue.symm))


lemma unchosen (ω : Ω × Bool) (i : Fin n) (H : ℝ) (hc : U.choose i H=none) :
    (U.patch.apply.activity ω).active i H ↔ (S.lift.sets.activity ω).active i H := by
  by_cases hd : H ∈ MainCell.domain U.tree U.phase U.cell i
  · have hn := MainCell.choose_none_inside U.comparison U.sub_old U.tree U.phase U.cell
      U.anchor U.noise U.error U.shield_offset U.lo i H hd hc
    have hv := (PlanarL1.Interpolation.namedClip_eq_old_iff _ _ _ _).mp hn
    change (MainCell.namedReplacement U.comparison U.sub_old U.tree U.phase U.cell
      U.anchor U.noise U.error U.shield_offset U.lo
        (MainCell.cellPoint U.tree U.phase U.cell i H hd)).value = _ at hv
    rw [MainCell.namedReplacement_value U.comparison U.sub_old U.tree U.phase U.cell
      U.anchor U.noise U.error U.shield_offset U.lo] at hv
    have hp := U.patch_inside ω i H hd
    rw [hv] at hp
    exact hp.trans (U.old_agreement ω i H hd)
  · exact U.patch.unchanged hd ω

lemma choose_switch (i j : Fin n) (H : ℝ) (hh : H ∈ M.heights i j) :
    U.choose i H=U.choose j H :=
  MainCell.choose_switch U.comparison U.sub_old U.tree U.phase U.cell U.compact_band
    U.anchor U.noise_bounds U.error_pos U.delta_eq U.shield_offset U.lo i j H hh

/-- The exact single kept main-cell update, including the fresh shield label
rebase and retention of every old identifier wherever the scalar clip is old. -/
noncomputable def apply [SFinite μ] : OrdinaryState M κ (Ω × Bool) (μ.prod Threshold.fair) :=
  S.lift.append U.patch.apply (3*n*U.tree.depthCap+1) U.newData U.newLabels U.choose
    (fun i H a hc => (U.chosen_description i H a hc).1.1)
    (fun i H a hc => (U.chosen_description i H a hc).1.2)
    U.choose_switch U.unchosen
    (fun ω i H a hc => (U.chosen_description i H a hc).2 ω _)

lemma apply_sets [SFinite μ] : U.apply.sets=U.patch.apply := rfl

end MainStep
end OrdinaryState
end PlanarL1.Columns.Model


namespace PlanarL1.Columns.Model
open MeasureTheory
open scoped NNReal
attribute [local instance] Classical.propDecidable
namespace OrdinaryState.MainStep
variable {n : ℕ} {M : Model n} {κ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {S : OrdinaryState M κ Ω μ} {J : Set ℝ} {root : Fin n}
variable (U : MainStep S J root)

lemma indicator_inside (ω : Ω × Bool) (i : Fin n) (H : ℝ)
    (hi : H ∈ MainCell.domain U.tree U.phase U.cell i) :
    (U.patch.apply.activity ω).indicator i H =
      Threshold.chartValue H (κ*(U.data.constant+U.data.orientation*
        MainCell.replacement U.comparison U.sub_old U.tree U.phase U.cell U.anchor
          U.noise U.error U.shield_offset U.lo (MainCell.cellPoint U.tree U.phase U.cell i H hi)))
        ((S.labels U.index).lift.value ω) := by
  simp only [Activity.indicator,U.patch_inside ω i H hi,Threshold.active,
    Threshold.chartValue,Threshold.half]

lemma old_indicator (ω : Ω × Bool) (i : Fin n) (H : ℝ)
    (hi : H ∈ MainCell.domain U.tree U.phase U.cell i) :
    (S.lift.sets.activity ω).indicator i H =
      Threshold.chartValue H (κ*(U.data.constant+U.data.orientation*
        MainCell.old U.comparison U.sub_old (MainCell.cellPoint U.tree U.phase U.cell i H hi)))
        ((S.labels U.index).lift.value ω) := by
  simp only [Activity.indicator,← U.old_agreement ω i H hi,Threshold.active,
    Threshold.chartValue,Threshold.half]

/-- Actual label mass moved by one kept main cell equals the oriented scalar
raise times κ. This compares the new sets with the lifted old sets. -/
lemma movement_exact (i : Fin n) (H : ℝ)
    (hi : H ∈ MainCell.domain U.tree U.phase U.cell i) :
    (∫ ω, |(U.patch.apply.activity ω).indicator i H-
      (S.lift.sets.activity ω).indicator i H| ∂(μ.prod Threshold.fair)) =
      κ*(MainCell.replacement U.comparison U.sub_old U.tree U.phase U.cell U.anchor
          U.noise U.error U.shield_offset U.lo (MainCell.cellPoint U.tree U.phase U.cell i H hi)-
        MainCell.old U.comparison U.sub_old (MainCell.cellPoint U.tree U.phase U.cell i H hi)) := by
  simp_rw [U.indicator_inside _ i H hi,U.old_indicator _ i H hi]
  rw [(S.labels U.index).lift.distance]
  rw [sub_self,abs_zero,max_eq_right (abs_nonneg _)]
  have hm := MainCell.movement U.comparison U.sub_old U.tree U.phase U.cell
    U.compact_band U.thin U.anchor (MainCell.cellPoint U.tree U.phase U.cell i H hi)
      U.anchor_mem ((MainCell.mem_domain U.tree U.phase U.cell).mp hi).1
      U.noise_bounds U.error_pos.le U.delta_eq
        (fun x => Clipping.heightShield U.lo U.tree.a (MainCell.old U.comparison U.sub_old U.anchor)
          U.shield_offset x.height)
  rw [show κ*(U.data.constant+U.data.orientation*MainCell.replacement U.comparison U.sub_old
      U.tree U.phase U.cell U.anchor U.noise U.error U.shield_offset U.lo
        (MainCell.cellPoint U.tree U.phase U.cell i H hi))-
    κ*(U.data.constant+U.data.orientation*MainCell.old U.comparison U.sub_old
        (MainCell.cellPoint U.tree U.phase U.cell i H hi)) =
    κ*U.data.orientation*(MainCell.replacement U.comparison U.sub_old U.tree U.phase U.cell
      U.anchor U.noise U.error U.shield_offset U.lo (MainCell.cellPoint U.tree U.phase U.cell i H hi)-
      MainCell.old U.comparison U.sub_old (MainCell.cellPoint U.tree U.phase U.cell i H hi)) by ring,
    abs_mul,abs_mul,abs_of_nonneg U.kappa_nonneg,U.data.unit_orientation,mul_one]
  congr 1
  exact abs_of_nonneg hm.1

lemma movement_integrable (i : Fin n) (H : ℝ) :
    Integrable (fun ω => (U.patch.apply.activity ω).indicator i H-
      (S.lift.sets.activity ω).indicator i H) (μ.prod Threshold.fair) := by
  by_cases hi : H ∈ MainCell.domain U.tree U.phase U.cell i
  · simp_rw [U.indicator_inside _ i H hi,U.old_indicator _ i H hi]
    exact (S.labels U.index).lift.integrable_difference _ _ _ _
  · have he : (fun ω => (U.patch.apply.activity ω).indicator i H-
        (S.lift.sets.activity ω).indicator i H) = fun _ => 0 := by
      funext ω
      simp only [Activity.indicator,U.patch.unchanged hi ω,sub_self]
    rw [he]
    exact integrable_zero _ _ _

lemma movement_bound (i : Fin n) (H : ℝ) :
    (∫ ω, |(U.patch.apply.activity ω).indicator i H-
      (S.lift.sets.activity ω).indicator i H| ∂(μ.prod Threshold.fair)) ≤ κ*(1+(1:ℝ)/100) := by
  by_cases hi : H ∈ MainCell.domain U.tree U.phase U.cell i
  · rw [U.movement_exact i H hi]
    apply mul_le_mul_of_nonneg_left _ U.kappa_nonneg
    exact (MainCell.movement U.comparison U.sub_old U.tree U.phase U.cell
      U.compact_band U.thin U.anchor (MainCell.cellPoint U.tree U.phase U.cell i H hi)
      U.anchor_mem ((MainCell.mem_domain U.tree U.phase U.cell).mp hi).1
      U.noise_bounds U.error_pos.le U.delta_eq _).2
  · have he : (fun ω => |(U.patch.apply.activity ω).indicator i H-
        (S.lift.sets.activity ω).indicator i H|) = fun _ => 0 := by
      funext ω
      simp only [Activity.indicator,U.patch.unchanged hi ω,sub_self,abs_zero]
    rw [he,integral_zero]
    positivity [U.kappa_nonneg]

/-- Under the literal padded-cell main test, either there is an actual shortest
band descent or the kept-cell movement has the claimed strict positive mass. -/
lemma movement_or_descent (w : M.Point J root)
    (hw : w.column ∈ ColumnOrder.componentColumns U.cell)
    {ε : ℝ} (hε : 0<ε) (hεsmall : ε ≤ (1:ℝ)/100)
    (hζ : U.tree.ζ=ε/100) (hE : U.error=ε/1000)
    (hκ : 0<κ)
    (hshield : MainCell.old U.comparison U.sub_old U.anchor+2 ≤
      Clipping.heightShield U.lo U.tree.a (MainCell.old U.comparison U.sub_old U.anchor)
        U.shield_offset w.height)
    (hlow : U.phase+(1:ℝ)/100000+2*U.tree.a <
      dist U.tree.base (w.withHeight U.tree.base.height U.tree.base.inBand))
    (hupp : dist U.tree.base (w.withHeight U.tree.base.height U.tree.base.inBand) <
      U.phase+(1:ℝ)/1000-(1:ℝ)/100000-2*U.tree.a) :
    2*κ*U.error < (∫ ω, |(U.patch.apply.activity ω).indicator w.column w.height-
      (S.lift.sets.activity ω).indicator w.column w.height| ∂(μ.prod Threshold.fair)) ∨
      Nonempty (U.comparison.BandDescent J (w.widen U.sub_old) ε) := by
  have hδ : U.tree.δ=(ε/1000)/8 := by rw [U.delta_eq,hE]
  have hh := MainCell.raise_or_descent U.comparison U.sub_old U.tree U.phase U.cell
    U.compact_band U.anchor w U.anchor_mem hw hε hεsmall hζ hδ U.noise_bounds
      (fun x => Clipping.heightShield U.lo U.tree.a (MainCell.old U.comparison U.sub_old U.anchor)
        U.shield_offset x.height) hshield hlow hupp
  rcases hh with hh | hh
  · left
    have hi := (MainCell.mem_domain U.tree U.phase U.cell).mpr ⟨hw,w.inBand⟩
    rw [U.movement_exact _ _ hi]
    have he : MainCell.cellPoint U.tree U.phase U.cell w.column w.height hi=w := by
      cases w
      rfl
    rw [he]
    change MainCell.old U.comparison U.sub_old w+2*(ε/1000) <
      MainCell.replacement U.comparison U.sub_old U.tree U.phase U.cell U.anchor
        U.noise (ε/1000) U.shield_offset U.lo w at hh
    rw [← hE] at hh
    nlinarith
  · exact Or.inr hh

end OrdinaryState.MainStep
end PlanarL1.Columns.Model



end

section



namespace PlanarL1.Columns.Model
open MeasureTheory
attribute [local instance] Classical.propDecidable
namespace OrdinaryState.MainStep
variable {n : ℕ} {M : Model n} {κ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {S : OrdinaryState M κ Ω μ} {J : Set ℝ} {root : Fin n}
variable (U : MainStep S J root)

lemma old_indicator_named (ω : Ω × Bool) (y : M.Point J root)
    (hy : S.name y.column y.height=U.index) :
    (S.lift.sets.activity ω).indicator y.column y.height =
      Threshold.chartValue y.height (κ*(U.data.constant+U.data.orientation*
        MainCell.old U.comparison U.sub_old y)) ((S.labels U.index).lift.value ω) := by
  have he := S.represents_named ω.1 y.column y.height U.index hy (U.sub_old y.inBand)
  simp only [Activity.indicator,Threshold.chartValue,Threshold.half,Threshold.active] at *
  exact if_congr he rfl rfl

/-- Actual common-label pair distance when one cell is kept and the other
endpoint is outside it. The comparison uses old labels, not new chart names. -/
lemma pair_distance (x y : M.Point J root)
    (hx : x.column ∈ ColumnOrder.componentColumns U.cell)
    (hy : y.column ∉ ColumnOrder.componentColumns U.cell)
    (hyn : S.name y.column y.height=U.index) :
    (∫ ω, |(U.patch.apply.activity ω).indicator x.column x.height-
        (U.patch.apply.activity ω).indicator y.column y.height| ∂(μ.prod Threshold.fair)) =
      max |x.height-y.height|
        (κ*|MainCell.replacement U.comparison U.sub_old U.tree U.phase U.cell U.anchor
          U.noise U.error U.shield_offset U.lo x-MainCell.old U.comparison U.sub_old y|) := by
  have hxi := (MainCell.mem_domain U.tree U.phase U.cell).mpr ⟨hx,x.inBand⟩
  have hyi : y.height ∉ MainCell.domain U.tree U.phase U.cell y.column := by
    intro h
    exact hy ((MainCell.mem_domain U.tree U.phase U.cell).mp h).1
  have he : MainCell.cellPoint U.tree U.phase U.cell x.column x.height hxi=x := by
    cases x
    rfl
  have hid (ω : Ω × Bool) :
      (U.patch.apply.activity ω).indicator y.column y.height =
        (S.lift.sets.activity ω).indicator y.column y.height := by
    simp only [Activity.indicator,U.patch.unchanged hyi ω]
  simp_rw [U.indicator_inside _ _ _ hxi,he,hid,U.old_indicator_named _ y hyn]
  rw [(S.labels U.index).lift.distance]
  congr 1
  rw [show κ*(U.data.constant+U.data.orientation*MainCell.replacement U.comparison U.sub_old
      U.tree U.phase U.cell U.anchor U.noise U.error U.shield_offset U.lo x)-
      κ*(U.data.constant+U.data.orientation*MainCell.old U.comparison U.sub_old y) =
      κ*U.data.orientation*(MainCell.replacement U.comparison U.sub_old U.tree U.phase U.cell
        U.anchor U.noise U.error U.shield_offset U.lo x-MainCell.old U.comparison U.sub_old y) by ring,
    abs_mul,abs_mul,abs_of_nonneg U.kappa_nonneg,U.data.unit_orientation,mul_one]

lemma separation_of_raise (x y : M.Point J root)
    (hx : x.column ∈ ColumnOrder.componentColumns U.cell)
    (hy : y.column ∉ ColumnOrder.componentColumns U.cell)
    (hyn : S.name y.column y.height=U.index) (hκ : 0<κ)
    (hclose : |MainCell.old U.comparison U.sub_old x-MainCell.old U.comparison U.sub_old y| ≤ U.error)
    (hraise : MainCell.old U.comparison U.sub_old x+2*U.error <
      MainCell.replacement U.comparison U.sub_old U.tree U.phase U.cell U.anchor
        U.noise U.error U.shield_offset U.lo x) :
    κ*U.error < (∫ ω, |(U.patch.apply.activity ω).indicator x.column x.height-
        (U.patch.apply.activity ω).indicator y.column y.height| ∂(μ.prod Threshold.fair)) := by
  rw [U.pair_distance x y hx hy hyn]
  apply lt_of_lt_of_le _ (le_max_right _ _)
  apply mul_lt_mul_of_pos_left _ hκ
  have hb := (abs_le.mp hclose).1
  have ha := le_abs_self (MainCell.replacement U.comparison U.sub_old U.tree U.phase U.cell
    U.anchor U.noise U.error U.shield_offset U.lo x-MainCell.old U.comparison U.sub_old y)
  linarith

/-- Literal deterministic favorable branch in the main pair-separation test. -/
lemma pair_separation_of_no_descent (x y : M.Point J root)
    (hx : x.column ∈ ColumnOrder.componentColumns U.cell)
    (hy : y.column ∉ ColumnOrder.componentColumns U.cell)
    (hyn : S.name y.column y.height=U.index) (hκ : 0<κ)
    {ε : ℝ} (hε : 0<ε) (hεsmall : ε ≤ (1:ℝ)/100)
    (hζ : U.tree.ζ=ε/100) (hE : U.error=ε/1000)
    (hclose : |MainCell.old U.comparison U.sub_old x-MainCell.old U.comparison U.sub_old y| ≤ U.error)
    (hshield : MainCell.old U.comparison U.sub_old U.anchor+2 ≤
      Clipping.heightShield U.lo U.tree.a (MainCell.old U.comparison U.sub_old U.anchor)
        U.shield_offset x.height)
    (hlow : U.phase+(1:ℝ)/100000+2*U.tree.a <
      dist U.tree.base (x.withHeight U.tree.base.height U.tree.base.inBand))
    (hupp : dist U.tree.base (x.withHeight U.tree.base.height U.tree.base.inBand) <
      U.phase+(1:ℝ)/1000-(1:ℝ)/100000-2*U.tree.a)
    (hno : ¬Nonempty (U.comparison.BandDescent J (x.widen U.sub_old) ε)) :
    κ*U.error < (∫ ω, |(U.patch.apply.activity ω).indicator x.column x.height-
        (U.patch.apply.activity ω).indicator y.column y.height| ∂(μ.prod Threshold.fair)) := by
  apply U.separation_of_raise x y hx hy hyn hκ hclose
  have hδ : U.tree.δ=(ε/1000)/8 := by rw [U.delta_eq,hE]
  have hh := MainCell.raise_or_descent U.comparison U.sub_old U.tree U.phase U.cell
    U.compact_band U.anchor x U.anchor_mem hx hε hεsmall hζ hδ U.noise_bounds
      (fun z => Clipping.heightShield U.lo U.tree.a (MainCell.old U.comparison U.sub_old U.anchor)
        U.shield_offset z.height) hshield hlow hupp
  rcases hh with hh | hh
  · simpa only [hE,MainCell.replacement] using hh
  · exact (hno hh).elim

end OrdinaryState.MainStep
end PlanarL1.Columns.Model





end

section

namespace PlanarL1.Columns.Model.OrdinaryState
open MeasureTheory
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {M : Model n} {κ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {S : OrdinaryState M κ Ω μ}

/-- A finite family of the actual main-cell proposals. Distinct cells may meet
at unchanged boundary points; no disjointness of their closed domains is assumed. -/
structure MainBatch (S : OrdinaryState M κ Ω μ) where
  count : ℕ
  band : Fin count → Set ℝ
  root : Fin count → Fin n
  step : ∀ q, MainStep S (band q) (root q)
  overlap : (List.ofFn (fun q => (step q).patch)).Pairwise SetPatch.UnchangedOverlap

namespace MainBatch
variable (B : MainBatch S)

def NewIndex := Σ q : Fin B.count, Fin (3*n*(B.step q).tree.depthCap+1)
noncomputable instance : Fintype B.NewIndex := inferInstanceAs (Fintype (Sigma _))

noncomputable def newData (a : B.NewIndex) : OrdinaryData M :=
  (B.step a.1).newData a.2
noncomputable def newLabels [SFinite μ] (a : B.NewIndex) :
    Threshold.Variables (Ω × Bool) (μ.prod Threshold.fair) :=
  (B.step a.1).newLabels a.2

noncomputable def chosen (i : Fin n) (H : ℝ) (a : B.NewIndex) : Prop :=
  (B.step a.1).choose i H = some a.2

noncomputable def choose (i : Fin n) (H : ℝ) : Option B.NewIndex :=
  if h : ∃ a, B.chosen i H a then some h.choose else none

lemma choose_some (i : Fin n) (H : ℝ) (a : B.NewIndex)
    (ha : B.choose i H=some a) : B.chosen i H a := by
  unfold choose at ha
  split_ifs at ha with h
  · have he : h.choose=a := Option.some.inj ha
    exact he ▸ h.choose_spec

lemma choose_none (i : Fin n) (H : ℝ) (ha : B.choose i H=none) (q : Fin B.count) :
    (B.step q).choose i H=none := by
  cases he : (B.step q).choose i H with
  | none => rfl
  | some a =>
    have hex : ∃ a, B.chosen i H a := ⟨⟨q,a⟩,he⟩
    simp [choose,hex] at ha

lemma choose_switch (i j : Fin n) (H : ℝ) (hs : H ∈ M.heights i j) :
    B.choose i H=B.choose j H := by
  have he : B.chosen i H=B.chosen j H := by
    funext a
    simp only [chosen,(B.step a.1).choose_switch i j H hs]
  unfold choose
  simp only [he]

noncomputable def sets : SetSystem M (Ω × Bool) (μ.prod Threshold.fair) :=
  SetPatch.batch (List.ofFn (fun q => (B.step q).patch)) B.overlap

lemma chosen_description [SFinite μ] (i : Fin n) (H : ℝ) (a : B.NewIndex)
    (ha : B.chosen i H a) : (B.newData a).Contains i H ∧
    ∀ (ω : Ω × Bool) (hi : H ∈ (B.newData a).band),
      (B.sets.activity ω).active i H ↔
        Threshold.active (B.newLabels a) H (κ*(B.newData a).value i ⟨H,hi⟩) ω := by
  have h := (B.step a.1).chosen_description i H a.2 ha
  refine ⟨h.1,?_⟩
  intro ω hi
  obtain ⟨hd,-⟩ := MainCell.choose_spec (B.step a.1).comparison (B.step a.1).sub_old
    (B.step a.1).tree (B.step a.1).phase (B.step a.1).cell (B.step a.1).anchor
    (B.step a.1).noise (B.step a.1).error (B.step a.1).shield_offset (B.step a.1).lo i H a.2 ha
  apply (SetPatch.batch_inside _ B.overlap (List.mem_ofFn.mpr ⟨a.1,rfl⟩) ω i H hd).trans
  exact h.2 ω hi

lemma unchosen (ω : Ω × Bool) (i : Fin n) (H : ℝ) (ha : B.choose i H=none) :
    (B.sets.activity ω).active i H ↔ (S.lift.sets.activity ω).active i H := by
  apply SetPatch.batch_old _ B.overlap ω i H
  intro P hP
  obtain ⟨q,rfl⟩ := List.mem_ofFn.mp hP
  exact (B.step q).unchosen ω i H (B.choose_none i H ha q)

/-- Actual finite main update, with the chart table containing every ancestor
formula and each shield's rebased label variables. -/
noncomputable def apply [SFinite μ] : OrdinaryState M κ (Ω × Bool) (μ.prod Threshold.fair) := by
  let e := Fintype.equivFin B.NewIndex
  let pick : Fin n → ℝ → Option (Fin (Fintype.card B.NewIndex)) :=
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

end MainBatch
end PlanarL1.Columns.Model.OrdinaryState



end

end OAI
