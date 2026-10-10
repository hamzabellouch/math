import OAI.Combinatorics.PlanarL1.Separation

namespace OAI


section

namespace PlanarL1.Columns.Model
open MeasureTheory
namespace Activity
variable {n : ℕ} {M : Model n}
lemma terminal_certificate_circular (A : Activity M) {a b x y : Fin n} {H s t : ℝ}
    (hH : H ∈ M.heights a b) (hn : ¬Consecutive a b) (hA : ¬A.active a H)
    (hs : Field.CircularTipSeparates a b x y)
    (hx : A.active x s) (hy : A.active y t) : A.cost x y s t=2 := by
  have hb : H ∈ M.heights b a := M.symm a b ▸ hH
  have hn' : ¬Consecutive b a := by simpa only [Consecutive,or_comm,or_left_comm,or_assoc] using hn
  have hB : ¬A.active b H := fun h => hA ((A.switch a b H hH).mpr h)
  rcases hs with (⟨hax,hxb,hyy⟩ | ⟨hay,hyb,hxx⟩) | (⟨hbx,hxa,hyy⟩ | ⟨hby,hya,hxx⟩)
  · exact A.terminal_certificate hH hn hA ⟨hax,hxb⟩ hyy hx hy
  · rw [A.cost_comm]
    exact A.terminal_certificate hH hn hA ⟨hay,hyb⟩ hxx hy hx
  · exact A.terminal_certificate hb hn' hB ⟨hbx,hxa⟩ hyy hx hy
  · rw [A.cost_comm]
    exact A.terminal_certificate hb hn' hB ⟨hby,hya⟩ hxx hy hx

lemma terminal_survival_circular (A B : Activity M) {a b x y : Fin n} {H s t : ℝ}
    (hH : H ∈ M.heights a b) (hn : ¬Consecutive a b)
    (hs : Field.CircularTipSeparates a b x y)
    (ha : ¬A.active a H) (hax : A.active x s) (hay : A.active y t) :
    2≤B.cost x y s t+2*(A.movement B x s+A.movement B y t+A.movement B a H) := by
  by_cases hba : B.active a H
  · have hm : A.movement B a H=1 := by simp [movement,indicator,ha,hba]
    linarith [A.movement_nonneg B x s,A.movement_nonneg B y t,B.cost_nonneg x y s t]
  by_cases hbx : B.active x s
  · by_cases hby : B.active y t
    · rw [B.terminal_certificate_circular hH hn hba hs hbx hby]
      linarith [A.movement_nonneg B x s,A.movement_nonneg B y t,A.movement_nonneg B a H]
    · have hm : A.movement B y t=1 := by simp [movement,indicator,hay,hby]
      linarith [A.movement_nonneg B x s,A.movement_nonneg B a H,B.cost_nonneg x y s t]
  · have hm : A.movement B x s=1 := by simp [movement,indicator,hax,hbx]
    linarith [A.movement_nonneg B y t,A.movement_nonneg B a H,B.cost_nonneg x y s t]
end Activity

namespace SetSystem
variable {n : ℕ} {M : Model n} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable (A B : SetSystem M Ω μ)
lemma refinedMap_terminal_circular [SFinite μ] {J : Set ℝ} {root : Fin n} (o x y : M.Point J root)
    {a b : Fin n} {H : ℝ} (hH : H ∈ M.heights a b) (hn : ¬Consecutive a b)
    (hs : Field.CircularTipSeparates a b x.column y.column)
    (E : Set Ω) (hE : MeasurableSet E)
    (hA : ∀ ω ∈ E, ¬(A.activity ω).active a H)
    (hX : ∀ ω ∈ E, (A.activity ω).active x.column x.height)
    (hY : ∀ ω ∈ E, (A.activity ω).active y.column y.height) :
    μ E<⊤ ∧ 2*μ.real E≤‖A.refinedMap o x-A.refinedMap o y‖ := by
  have hbnd : ∀ ω, ‖E.indicator (fun _ => (2:ℝ)) ω‖≤
      (A.activity ω).cost x.column y.column x.height y.height := by
    intro ω
    by_cases hω : ω ∈ E
    · rw [Set.indicator_of_mem hω,
        (A.activity ω).terminal_certificate_circular hH hn (hA ω hω) hs (hX ω hω) (hY ω hω)]
      norm_num
    · rw [Set.indicator_of_notMem hω,norm_zero]
      exact (A.activity ω).cost_nonneg _ _ _ _
  have hi : Integrable (E.indicator (fun _ => (2:ℝ))) μ :=
    (A.cost_integrable (Classical.choice (x.paths_nonempty y)) x.height y.height).mono'
      (measurable_const.indicator hE).aestronglyMeasurable (Filter.Eventually.of_forall hbnd)
  constructor
  · have ht := (integrableOn_const_iff (C := (2:ℝ))).mp ((integrable_indicator_iff hE).mp hi)
    simpa using ht
  · rw [A.norm_refinedMap_sub]
    calc
      2*μ.real E = ∫ ω, E.indicator (fun _ => (2:ℝ)) ω ∂μ := by
        rw [integral_indicator_const _ hE,smul_eq_mul,mul_comm]
      _ ≤ _ := integral_mono hi
        (A.cost_integrable (Classical.choice (x.paths_nonempty y)) x.height y.height)
        (fun ω => (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hbnd ω))

lemma refined_certificate_survival_circular [SFinite μ] {J : Set ℝ} {root : Fin n}
    (o x y : M.Point J root) {a b : Fin n} {H : ℝ}
    (hH : H ∈ M.heights a b) (hn : ¬Consecutive a b)
    (hs : Field.CircularTipSeparates a b x.column y.column)
    (E : Set Ω) (hE : MeasurableSet E)
    (ha : ∀ ω ∈ E, ¬(A.activity ω).active a H)
    (hax : ∀ ω ∈ E, (A.activity ω).active x.column x.height)
    (hay : ∀ ω ∈ E, (A.activity ω).active y.column y.height)
    (hmove : ∀ i H, Integrable (fun ω => (B.activity ω).indicator i H-
      (A.activity ω).indicator i H) μ) :
    2*μ.real E≤‖B.refinedMap o x-B.refinedMap o y‖+
      2*(A.movement B x.column x.height+A.movement B y.column y.height+A.movement B a H) := by
  have hfin := (A.refinedMap_terminal_circular o x y hH hn hs E hE ha hax hay).1
  have hEI : Integrable (E.indicator (fun _ => (2:ℝ))) μ := by
    apply (integrable_indicator_iff hE).mpr
    exact (integrableOn_const_iff (C := (2:ℝ))).mpr (Or.inr hfin)
  have hmI (i : Fin n) (z : ℝ) : Integrable (fun ω => (A.activity ω).movement (B.activity ω) i z) μ := by
    simpa only [Activity.movement,Real.norm_eq_abs] using (hmove i z).norm
  have hxI := hmI x.column x.height
  have hyI := hmI y.column y.height
  have haI := hmI a H
  let path := Classical.choice (x.paths_nonempty y)
  have hcost := B.cost_integrable path x.height y.height
  have hg := integral_mono hEI (hcost.add (((hxI.add hyI).add haI).const_mul 2))
    (fun ω => show E.indicator (fun _ => (2:ℝ)) ω≤
      (B.activity ω).cost x.column y.column x.height y.height+
      2*((A.activity ω).movement (B.activity ω) x.column x.height+
        (A.activity ω).movement (B.activity ω) y.column y.height+
        (A.activity ω).movement (B.activity ω) a H) by
      by_cases he : ω ∈ E
      · rw [Set.indicator_of_mem he]
        exact (A.activity ω).terminal_survival_circular (B.activity ω) hH hn hs
          (ha ω he) (hax ω he) (hay ω he)
      · rw [Set.indicator_of_notMem he]
        linarith [(B.activity ω).cost_nonneg x.column y.column x.height y.height,
          (A.activity ω).movement_nonneg (B.activity ω) x.column x.height,
          (A.activity ω).movement_nonneg (B.activity ω) y.column y.height,
          (A.activity ω).movement_nonneg (B.activity ω) a H])
  rw [integral_indicator_const _ hE,smul_eq_mul,mul_comm] at hg
  rw [B.norm_refinedMap_sub]
  change _≤_+2*((∫ ω, |(B.activity ω).indicator x.column x.height-
      (A.activity ω).indicator x.column x.height| ∂μ)+
    (∫ ω, |(B.activity ω).indicator y.column y.height-
      (A.activity ω).indicator y.column y.height| ∂μ)+
    (∫ ω, |(B.activity ω).indicator a H-(A.activity ω).indicator a H| ∂μ))
  dsimp only [Pi.add_apply] at hg
  have e1 := integral_add hcost (((hxI.add hyI).add haI).const_mul 2)
  have e2 := integral_add (hxI.add hyI) haI
  have e3 := integral_add hxI hyI
  simp only [Pi.add_apply] at e1 e2 e3
  rw [e1,integral_const_mul,e2,e3] at hg
  exact hg
end SetSystem
end PlanarL1.Columns.Model

end



section

namespace PlanarL1.Threshold.Variables
open MeasureTheory Set
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A literal half-sign label rectangle, pulled back through the actual old
chart variables. No independence of different old charts is asserted. -/
noncomputable def slab (Z : Variables Ω μ) (b : Bool) (lo hi : ℝ) : Set Ω :=
  Z.value ⁻¹' ({b} ×ˢ Ico lo hi)
lemma measurable_slab (Z : Variables Ω μ) (b : Bool) (lo hi : ℝ) :
    MeasurableSet (Z.slab b lo hi) :=
  ((measurableSet_singleton b).prod measurableSet_Ico).preimage Z.preserving.measurable
lemma mem_slab (Z : Variables Ω μ) (b : Bool) (lo hi : ℝ) (ω : Ω) :
    ω ∈ Z.slab b lo hi ↔ (Z.value ω).1=b ∧ lo ≤ (Z.value ω).2 ∧ (Z.value ω).2 < hi := by
  simp only [slab,mem_preimage,mem_prod,mem_singleton_iff,mem_Ico]
lemma measure_slab (Z : Variables Ω μ) (b : Bool) {lo hi : ℝ} (hh : lo ≤ hi) :
    μ.real (Z.slab b lo hi)=(hi-lo)/2 := by
  unfold Measure.real slab
  rw [Z.preserving.measure_preimage (((measurableSet_singleton b).prod measurableSet_Ico).nullMeasurableSet),
    labelMeasure_eq,Measure.prod_prod, fair,Measure.smul_apply,smul_eq_mul,
    Measure.count_singleton,mul_one,Real.volume_Ico,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hh)]
  norm_num
  ring
end PlanarL1.Threshold.Variables

namespace PlanarL1.Columns.Model.OrdinaryState
open Parameters MeasureTheory
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {M : Model n} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable (S : OrdinaryState M kappaA Ω μ)

/-- The elementary barrier rectangle in one literal ordinary chart. All three
memberships and its uniform real mass are produced, rather than assumed. -/
lemma barrier_labels (a : Fin (S.count+1)) {root : Fin n}
    (x y e : M.Point (S.chart a).band root)
    (hx : S.name x.column x.height=a) (hy : S.name y.column y.height=a)
    (he : S.name e.column e.height=a)
    {lo : ℝ} (hxH : x.height ∈ Set.Icc lo (lo+a₂))
    (hyH : y.height ∈ Set.Icc lo (lo+a₂)) (heH : e.height ∈ Set.Icc lo (lo+a₂))
    (hclose : |(S.chart a).comparison.eval x-(S.chart a).comparison.eval y| ≤ EA)
    (hdrop : (S.chart a).comparison.eval e < (S.chart a).comparison.eval x-j ∨
      (S.chart a).comparison.eval e < (S.chart a).comparison.eval y-j) :
    ∃ E : Set Ω, MeasurableSet E ∧ kappaA*j/4 ≤ μ.real E ∧
      (∀ ω ∈ E, (S.sets.activity ω).active x.column x.height) ∧
      (∀ ω ∈ E, (S.sets.activity ω).active y.column y.height) ∧
      (∀ ω ∈ E, ¬(S.sets.activity ω).active e.column e.height) := by
  let sx := (S.chart a).comparison.eval x
  let sy := (S.chart a).comparison.eval y
  let se := (S.chart a).comparison.eval e
  let τ := (S.chart a).orientation
  let c := (S.chart a).constant
  obtain ⟨b,hb⟩ : ∃ b : Bool, (if b then (1:ℝ) else -1)=τ := by
    obtain h | h := (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp (S.chart a).unit_orientation
    · exact ⟨true,h.symm⟩
    · exact ⟨false,h.symm⟩
  let tx := x.height+kappaA*τ*c+kappaA*sx
  let ty := y.height+kappaA*τ*c+kappaA*sy
  let te := e.height+kappaA*τ*c+kappaA*se
  have hsx : j-EA ≤ sx-se := by
    dsimp only [sx,sy,se] at *
    obtain h | h := hdrop
    · linarith [show 0 ≤ EA by norm_num [EA,epsilon]]
    · linarith [(abs_le.mp hclose).1]
  have hsy : j-EA ≤ sy-se := by
    dsimp only [sx,sy,se] at *
    obtain h | h := hdrop
    · linarith [(abs_le.mp hclose).2]
    · linarith [show 0 ≤ EA by norm_num [EA,epsilon]]
  have hk : 0 < kappaA := by norm_num [kappaA,a₁]
  have hj : 0 < j := by norm_num [j,R]
  have hnum : kappaA*j/2 ≤ kappaA*(j-EA)-a₂ := by
    norm_num [kappaA,a₁,j,R,EA,epsilon,a₂]
  have htx : kappaA*j/2 ≤ tx-te := by
    have := mul_le_mul_of_nonneg_left hsx hk.le
    dsimp only [tx,te]
    nlinarith [hxH.1,heH.2]
  have hty : kappaA*j/2 ≤ ty-te := by
    have := mul_le_mul_of_nonneg_left hsy hk.le
    dsimp only [ty,te]
    nlinarith [hyH.1,heH.2]
  have hmin : kappaA*j/2 ≤ min tx ty-te := by
    rw [← min_sub_sub_right]
    exact le_min htx hty
  have hle : te ≤ min tx ty := by nlinarith
  have hformula (z : M.Point (S.chart a).band root) :
      (if b then z.height+kappaA*(S.chart a).value z.column ⟨z.height,z.inBand⟩
      else z.height-kappaA*(S.chart a).value z.column ⟨z.height,z.inBand⟩)=
        z.height+kappaA*τ*c+kappaA*(S.chart a).comparison.eval z := by
    cases b  <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hb ⊢  <;>
      dsimp only [OrdinaryData.value,Field.eval] 
    · have hτ : (S.chart a).orientation = -1 := hb.symm
      simp only [hτ]
      dsimp only [τ,c]
      rw [hτ]
      ring
    · have hτ : (S.chart a).orientation = 1 := hb.symm
      simp only [hτ]
      dsimp only [τ,c]
      rw [hτ]
      ring
  let E := (S.labels a).slab b te (min tx ty)
  refine ⟨E,(S.labels a).measurable_slab b te (min tx ty),?_,?_,?_,?_⟩
  · rw [(S.labels a).measure_slab b hle]
    linarith
  · intro ω hω
    obtain ⟨hωb,_,hω⟩ := ((S.labels a).mem_slab b te (min tx ty) ω).mp hω
    rw [S.represents_named ω _ _ a hx x.inBand]
    unfold Threshold.active
    rw [hωb,hformula x]
    exact hω.trans_le (min_le_left _ _)
  · intro ω hω
    obtain ⟨hωb,_,hω⟩ := ((S.labels a).mem_slab b te (min tx ty) ω).mp hω
    rw [S.represents_named ω _ _ a hy y.inBand]
    unfold Threshold.active
    rw [hωb,hformula y]
    exact hω.trans_le (min_le_right _ _)
  · intro ω hω ha
    obtain ⟨hωb,hω,_⟩ := ((S.labels a).mem_slab b te (min tx ty) ω).mp hω
    rw [S.represents_named ω _ _ a he e.inBand] at ha
    unfold Threshold.active at ha
    rw [hωb,hformula e] at ha
    exact (not_lt_of_ge hω) ha
end PlanarL1.Columns.Model.OrdinaryState

end



section

namespace PlanarL1.Columns.Model
open MeasureTheory
attribute [local instance] Classical.propDecidable
namespace OrdinaryState.MainStep
variable {n : ℕ} {M : Model n} {κ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {S : OrdinaryState M κ Ω μ} {J : Set ℝ} {root : Fin n}
variable (U : MainStep S J root)

/-- The other endpoint can be in another broad component. Only its actual old
identifier and its absence from this cell matter for the indicator calculation. -/
lemma pair_distance_external (x : M.Point J root) (j : Fin n) (T : ℝ)
    (hT : T ∈ U.data.band) (hx : x.column ∈ ColumnOrder.componentColumns U.cell)
    (hy : T ∉ MainCell.domain U.tree U.phase U.cell j) (hyn : S.name j T=U.index) :
    (∫ ω, |(U.patch.apply.activity ω).indicator x.column x.height-
        (U.patch.apply.activity ω).indicator j T| ∂(μ.prod Threshold.fair)) =
      max |x.height-T| (κ*|MainCell.replacement U.comparison U.sub_old U.tree U.phase U.cell
        U.anchor U.noise U.error U.shield_offset U.lo x-U.comparison.value j ⟨T,hT⟩|) := by
  have hxi := (MainCell.mem_domain U.tree U.phase U.cell).mpr ⟨hx,x.inBand⟩
  have he : MainCell.cellPoint U.tree U.phase U.cell x.column x.height hxi=x := by cases x; rfl
  have hid (ω : Ω × Bool) :
      (U.patch.apply.activity ω).indicator j T =
        Threshold.chartValue T (κ*(U.data.constant+U.data.orientation*U.comparison.value j ⟨T,hT⟩))
          ((S.labels U.index).lift.value ω) := by
    have hr := S.represents_named ω.1 j T U.index hyn hT
    have hp := U.patch.unchanged hy ω
    simp only [Activity.indicator,Threshold.chartValue,Threshold.half,Threshold.active] at *
    exact if_congr (hp.trans hr) rfl rfl
  simp_rw [U.indicator_inside _ _ _ hxi,he,hid]
  rw [(S.labels U.index).lift.distance]
  congr 1
  rw [show κ*(U.data.constant+U.data.orientation*MainCell.replacement U.comparison U.sub_old
      U.tree U.phase U.cell U.anchor U.noise U.error U.shield_offset U.lo x)-
      κ*(U.data.constant+U.data.orientation*U.comparison.value j ⟨T,hT⟩) =
      κ*U.data.orientation*(MainCell.replacement U.comparison U.sub_old U.tree U.phase U.cell
        U.anchor U.noise U.error U.shield_offset U.lo x-U.comparison.value j ⟨T,hT⟩) by ring,
    abs_mul,abs_mul,abs_of_nonneg U.kappa_nonneg,U.data.unit_orientation,mul_one]

lemma separation_of_raise_external (x : M.Point J root) (j : Fin n) (T : ℝ)
    (hT : T ∈ U.data.band) (hx : x.column ∈ ColumnOrder.componentColumns U.cell)
    (hy : T ∉ MainCell.domain U.tree U.phase U.cell j) (hyn : S.name j T=U.index) (hκ : 0<κ)
    (hclose : |MainCell.old U.comparison U.sub_old x-U.comparison.value j ⟨T,hT⟩| ≤ U.error)
    (hraise : MainCell.old U.comparison U.sub_old x+2*U.error <
      MainCell.replacement U.comparison U.sub_old U.tree U.phase U.cell U.anchor
        U.noise U.error U.shield_offset U.lo x) :
    κ*U.error < (∫ ω, |(U.patch.apply.activity ω).indicator x.column x.height-
        (U.patch.apply.activity ω).indicator j T| ∂(μ.prod Threshold.fair)) := by
  rw [U.pair_distance_external x j T hT hx hy hyn]
  apply lt_of_lt_of_le _ (le_max_right _ _)
  apply mul_lt_mul_of_pos_left _ hκ
  have hb := (abs_le.mp hclose).1
  have ha := le_abs_self (MainCell.replacement U.comparison U.sub_old U.tree U.phase U.cell
    U.anchor U.noise U.error U.shield_offset U.lo x-U.comparison.value j ⟨T,hT⟩)
  linarith

lemma pair_separation_external (x : M.Point J root) (j : Fin n) (T : ℝ)
    (hT : T ∈ U.data.band) (hx : x.column ∈ ColumnOrder.componentColumns U.cell)
    (hy : T ∉ MainCell.domain U.tree U.phase U.cell j) (hyn : S.name j T=U.index) (hκ : 0<κ)
    {ε : ℝ} (hε : 0<ε) (hεsmall : ε ≤ (1:ℝ)/100)
    (hζ : U.tree.ζ=ε/100) (hE : U.error=ε/1000)
    (hclose : |MainCell.old U.comparison U.sub_old x-U.comparison.value j ⟨T,hT⟩| ≤ U.error)
    (hshield : MainCell.old U.comparison U.sub_old U.anchor+2 ≤
      Clipping.heightShield U.lo U.tree.a (MainCell.old U.comparison U.sub_old U.anchor)
        U.shield_offset x.height)
    (hlow : U.phase+(1:ℝ)/100000+2*U.tree.a <
      dist U.tree.base (x.withHeight U.tree.base.height U.tree.base.inBand))
    (hupp : dist U.tree.base (x.withHeight U.tree.base.height U.tree.base.inBand) <
      U.phase+(1:ℝ)/1000-(1:ℝ)/100000-2*U.tree.a)
    (hno : ¬Nonempty (U.comparison.BandDescent J (x.widen U.sub_old) ε)) :
    κ*U.error < (∫ ω, |(U.patch.apply.activity ω).indicator x.column x.height-
        (U.patch.apply.activity ω).indicator j T| ∂(μ.prod Threshold.fair)) := by
  apply U.separation_of_raise_external x j T hT hx hy hyn hκ hclose
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

end OAI
