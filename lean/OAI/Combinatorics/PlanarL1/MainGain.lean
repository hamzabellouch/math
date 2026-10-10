import OAI.Combinatorics.PlanarL1.PairSelection

namespace OAI


section

namespace PlanarL1.Columns.Model.MainFamily
open Parameters MeasureTheory
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable (A : Ambient M) (S : OrdinaryState M kappaA Ω μ)
variable {q L U : ℝ} (phase : BandComponent (M := M) q L U → ℝ)

lemma unique_at_padded {c d : CellIndex q L U phase} {i : Fin (k+1)} {H : ℝ}
    (hp : Tiling.Padded a₁ q H (a₁/10))
    (hc : H ∈ domain phase c i) (hd : H ∈ domain phase d i) : c=d := by
  apply unique_in_band phase _ hc hd
  apply Subtype.ext
  exact (Tiling.unique_band_of_padded interpolationA.2.1 (by norm_num [a₁]) hp
    (domain_band phase c hc)).trans
    (Tiling.unique_band_of_padded interpolationA.2.1 (by norm_num [a₁]) hp
      (domain_band phase d hd)).symm

variable {m : ℕ} (hm : 0 < m) (omega : Sample phase m)
lemma batch_inside_kept (c : Kept A S phase omega) (w : Ω × Bool)
    (i : Fin (k+1)) (H : ℝ) (hH : H ∈ domain phase c.val i) :
    ((batch A S phase hm omega).sets.activity w).active i H ↔
      ((keptStep A S phase hm omega c).patch.apply.activity w).active i H := by
  apply SetPatch.batch_inside _ (batch A S phase hm omega).overlap
  · apply List.mem_ofFn.mpr
    let e := @Fintype.equivFin (Kept A S phase omega) (instFintypeKept A S phase omega)
    refine ⟨e c, ?_⟩
    exact congrArg (fun d => (keptStep A S phase hm omega d).patch) (e.symm_apply_apply c)
  · exact hH

lemma batch_old_suppressed (c : CellIndex q L U phase) (w : Ω × Bool)
    (i : Fin (k+1)) (H : ℝ) (hH : H ∈ domain phase c i)
    (hp : Tiling.Padded a₁ q H (a₁/10)) (hoff : (omega c).2.2=false) :
    ((batch A S phase hm omega).sets.activity w).active i H ↔
      (S.lift.sets.activity w).active i H := by
  apply SetPatch.batch_old _ (batch A S phase hm omega).overlap
  intro P hP
  obtain ⟨d,rfl⟩ := List.mem_ofFn.mp hP
  apply ((batch A S phase hm omega).step d).patch.unchanged
  intro hd
  let d' : Kept A S phase omega := (Fintype.equivFin _).symm d
  have hd' : H ∈ domain phase d'.val i := hd
  have he : c=d'.val := unique_at_padded phase hp hH hd'
  have ht := d'.property.2
  rw [←he,hoff] at ht
  cases ht

end PlanarL1.Columns.Model.MainFamily

end



section

namespace PlanarL1.FiniteRandom
attribute [local instance] Classical.propDecidable
lemma prob_second {Ω Λ : Type*} [Fintype Ω] [Nonempty Ω] [Fintype Λ]
    (P : Λ → Prop) : prob (fun z : Ω × Λ => P z.2)=prob P := by
  rw [prob_prod]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (by positivity)

/-- Separate coins from all other finite independent local data, including
when the local data type depends on the cell/group. -/
def coinProduct {I : Type*} (D : I → Type*) :
    (∀ i, D i × Bool) ≃ (∀ i, D i) × (I → Bool) where
  toFun f := (fun i => (f i).1,fun i => (f i).2)
  invFun f i := (f.1 i,f.2 i)
  left_inv f := by funext i; rfl
  right_inv f := by cases f; rfl
lemma prob_coinProduct {I : Type*} [Fintype I] (D : I → Type*)
    [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)] (P : (I → Bool) → Prop) :
    prob (fun f : ∀ i, D i × Bool => P (fun i => (f i).2))=prob P := by
  rw [←prob_equiv (coinProduct D).symm]
  exact prob_second P
end PlanarL1.FiniteRandom

namespace PlanarL1.Columns.Model.MainFamily
open Parameters FiniteRandom
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {q L U : ℝ}
variable (phase : BandComponent (M := M) q L U → ℝ) (m : ℕ)
abbrev Uncoined (c : CellIndex q L U phase) :=
  Point.RadialTree.GridSample (n := k+1) (tree phase c).depthCap m × Fin (m+1)
def restructure : Sample phase m ≃ (∀ c, Uncoined phase m c × Bool) where
  toFun f c := (((f c).1,(f c).2.1),(f c).2.2)
  invFun f c := ((f c).1.1,((f c).1.2,(f c).2))
  left_inv f := by funext c; rfl
  right_inv f := by funext c; rfl
lemma prob_coins (P : (CellIndex q L U phase → Bool) → Prop) :
    prob (fun omega : Sample phase m => P (fun c => (omega c).2.2))=prob P := by
  let e := (restructure phase m).trans (coinProduct (Uncoined phase m))
  have he := prob_equiv e.symm (fun omega : Sample phase m => P (fun c => (omega c).2.2))
  change prob (fun f : (∀ c, Uncoined phase m c) × (CellIndex q L U phase → Bool) => P f.2)=_ at he
  exact he.symm.trans (prob_second P)
lemma prob_keep_suppress (c d : CellIndex q L U phase) (hne : c≠d) :
    prob (fun omega : Sample phase m => (omega c).2.2=true ∧ (omega d).2.2=false)=1/4 := by
  apply (prob_coins phase m (fun f => f c=true ∧ f d=false)).trans
  convert prob_two_coins c d hne true false using 1
  exact congrArg (fun F : Fintype (CellIndex q L U phase → Bool) =>
    @prob _ F (fun f => f c=true ∧ f d=false)) (Subsingleton.elim _ _)
end PlanarL1.Columns.Model.MainFamily

end



section

namespace PlanarL1.Columns.Model.MainFamily
open Parameters MeasureTheory
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable (A : Ambient M) (S : OrdinaryState M kappaA Ω μ)
variable {q L U : ℝ} (phase : BandComponent (M := M) q L U → ℝ)
variable {m : ℕ} (hm : 0 < m) (omega : Sample phase m)

lemma batch_pair_kept_suppressed (c : Kept A S phase omega) (d : CellIndex q L U phase)
    (ii jj : Fin (k+1)) (H T : ℝ)
    (hx : H ∈ domain phase c.val ii) (hy : T ∈ domain phase d jj)
    (hp : Tiling.Padded a₁ q T (a₁/10)) (hoff : (omega d).2.2=false) :
    (∫ w, |((batch A S phase hm omega).sets.activity w).indicator ii H-
      ((batch A S phase hm omega).sets.activity w).indicator jj T| ∂(μ.prod Threshold.fair)) =
    (∫ w, |((keptStep A S phase hm omega c).patch.apply.activity w).indicator ii H-
      ((keptStep A S phase hm omega c).patch.apply.activity w).indicator jj T| ∂(μ.prod Threshold.fair)) := by
  have hout : T ∉ domain phase c.val jj := by
    intro hc
    have he := unique_at_padded phase hp hy hc
    have ht := c.property.2
    rw [←he,hoff] at ht
    cases ht
  apply integral_congr_ae
  filter_upwards [] with w
  have heX := batch_inside_kept A S phase hm omega c w ii H hx
  have heY := batch_old_suppressed A S phase hm omega d w jj T hy hp hoff
  have hpY := (keptStep A S phase hm omega c).patch.unchanged hout w
  simp only [Activity.indicator,heX,heY,hpY]

lemma padded_height {c : CellIndex q L U phase} {i : Fin (k+1)} {H : ℝ}
    (hx : H ∈ domain phase c i) (hp : Tiling.Padded a₁ q H (a₁/10)) :
    lower q L U c.1.1+a₁/10 < H ∧ H < lower q L U c.1.1+a₁-a₁/10 := by
  have he := Tiling.unique_band_of_padded interpolationA.2.1 (by norm_num [a₁]) hp
    (domain_band phase c hx)
  unfold Tiling.Padded at hp
  rw [←he] at hp
  change q+(c.1.1.val:ℝ)*a₁+a₁/10 < H ∧ H < q+(c.1.1.val:ℝ)*a₁+a₁-a₁/10
  constructor <;> linarith [hp.1,hp.2]

lemma kept_shield (c : Kept A S phase omega)
    (x : M.Point (BandTrees.band broad (lower q L U c.val.1.1))
      (BandTrees.root M broad (lower q L U c.val.1.1) c.val.1.2))
    (hx : x.height ∈ domain phase c.val x.column)
    (hp : Tiling.Padded a₁ q x.height (a₁/10)) :
    MainCell.old (keptStep A S phase hm omega c).comparison
      (keptStep A S phase hm omega c).sub_old (keptStep A S phase hm omega c).anchor+2 ≤
    Clipping.heightShield (keptStep A S phase hm omega c).lo (keptStep A S phase hm omega c).tree.a
      (MainCell.old (keptStep A S phase hm omega c).comparison
        (keptStep A S phase hm omega c).sub_old (keptStep A S phase hm omega c).anchor)
      (keptStep A S phase hm omega c).shield_offset x.height := by
  have hpad := padded_height phase hx hp
  have he := Clipping.heightShield_plateau (s :=
    MainCell.old (keptStep A S phase hm omega c).comparison
      (keptStep A S phase hm omega c).sub_old (keptStep A S phase hm omega c).anchor)
    (α := (keptStep A S phase hm omega c).shield_offset)
    interpolationA.2.1 (lo := lower q L U c.val.1.1) (H := x.height)
    (by linarith [hpad.1]) (by linarith [hpad.2])
  change _ ≤ Clipping.heightShield (lower q L U c.val.1.1) a₁ _ _ x.height
  rw [he]
  have hpos : 0 ≤ EA/(m:ℝ)*((omega c.val).2.1.val:ℝ) :=
    mul_nonneg (div_nonneg interpolationA.1.le (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  change _ ≤ _+2+EA/(m:ℝ)*((omega c.val).2.1.val:ℝ)
  linarith

/-- A literal missing descent in an available padded cell produces the gain
in the *whole* simultaneous main update on the keep/suppress coin event. -/
lemma no_descent_gain (c d : CellIndex q L U phase) (hc : Available A S phase c)
    (x : M.Point (BandTrees.band broad (lower q L U c.1.1))
      (BandTrees.root M broad (lower q L U c.1.1) c.1.2))
    (ii : Fin (k+1)) (T : ℝ)
    (hx : x.column ∈ ColumnOrder.componentColumns c.2.2)
    (hy : T ∈ domain phase d ii)
    (hpx : Tiling.Padded a₁ q x.height (a₁/10)) (hpy : Tiling.Padded a₁ q T (a₁/10))
    (hr : BandTrees.RadialInterior D (phase c.1) x)
    (hn : S.name ii T=index A S phase c hc)
    (hT : T ∈ (S.chart (index A S phase c hc)).band)
    (hclose : |(S.chart (index A S phase c hc)).comparison.eval
        (x.widen (sub_old A S phase c hc))-
        (S.chart (index A S phase c hc)).comparison.value ii ⟨T,hT⟩| ≤ EA)
    (hno : ¬Nonempty ((S.chart (index A S phase c hc)).comparison.BandDescent
      (BandTrees.band broad (lower q L U c.1.1)) (x.widen (sub_old A S phase c hc)) epsilon))
    (hon : (omega c).2.2=true) (hoff : (omega d).2.2=false) :
    kappaA*EA < (∫ w, |((batch A S phase hm omega).sets.activity w).indicator x.column x.height-
      ((batch A S phase hm omega).sets.activity w).indicator ii T| ∂(μ.prod Threshold.fair)) := by
  let ck : Kept A S phase omega := ⟨c,hc,hon⟩
  let V := keptStep A S phase hm omega ck
  have hxi : x.height ∈ domain phase c x.column := (MainCell.mem_domain _ _ _).mpr ⟨hx,x.inBand⟩
  rw [batch_pair_kept_suppressed A S phase hm omega ck d _ _ _ _ hxi hy hpy hoff]
  have hout : T ∉ domain phase c ii := by
    intro hzc
    have he := unique_at_padded phase hpy hy hzc
    rw [he,hon] at hoff
    cases hoff
  have hr' : BandTrees.RadialInterior (1/1000) (phase c.1) x := by
    norm_num [D] at hr ⊢
    exact hr
  have hp := BandTrees.radialInterior_padding (by norm_num) (by norm_num [a₁]) x hr' c.2 hx
  apply V.pair_separation_external x ii T hT hx hout hn (by norm_num [kappaA,a₁])
    (ε := epsilon) (by norm_num [epsilon]) (by norm_num [epsilon]) rfl rfl hclose
    (kept_shield A S phase hm omega ck x hxi hpx) _ _ hno
  · change radial phase c+1/100000+2*a₁ < BandTrees.radialValue x
    norm_num [radial] at hp ⊢
    exact hp.1
  · change BandTrees.radialValue x < radial phase c+1/1000-1/100000-2*a₁
    norm_num [radial] at hp ⊢
    exact hp.2

end PlanarL1.Columns.Model.MainFamily

end



section

namespace PlanarL1.Columns.Model.MainFamily
open Parameters MeasureTheory
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable (A : Ambient M) (S : OrdinaryState M kappaA Ω μ)
variable {q L U : ℝ} (phase : BandComponent (M := M) q L U → ℝ)
variable {m : ℕ} (hm : 0 < m) 

lemma no_descent_probability (c d : CellIndex q L U phase) (hc : Available A S phase c)
    (x : M.Point (BandTrees.band broad (lower q L U c.1.1))
      (BandTrees.root M broad (lower q L U c.1.1) c.1.2))
    (ii : Fin (k+1)) (T : ℝ)
    (hx : x.column ∈ ColumnOrder.componentColumns c.2.2)
    (hy : T ∈ domain phase d ii)
    (hpx : Tiling.Padded a₁ q x.height (a₁/10)) (hpy : Tiling.Padded a₁ q T (a₁/10))
    (hr : BandTrees.RadialInterior D (phase c.1) x)
    (hn : S.name ii T=index A S phase c hc)
    (hT : T ∈ (S.chart (index A S phase c hc)).band)
    (hclose : |(S.chart (index A S phase c hc)).comparison.eval
        (x.widen (sub_old A S phase c hc))-
        (S.chart (index A S phase c hc)).comparison.value ii ⟨T,hT⟩| ≤ EA)
    (hno : ¬Nonempty ((S.chart (index A S phase c hc)).comparison.BandDescent
      (BandTrees.band broad (lower q L U c.1.1)) (x.widen (sub_old A S phase c hc)) epsilon))
    (hne : c≠d) :
    1/4 ≤ FiniteRandom.prob (fun omega : Sample phase m =>
      kappaA*EA < (∫ w, |((batch A S phase hm omega).sets.activity w).indicator x.column x.height-
        ((batch A S phase hm omega).sets.activity w).indicator ii T| ∂(μ.prod Threshold.fair))) := by
  rw [←prob_keep_suppress phase m c d hne]
  exact FiniteRandom.prob_mono (fun omega h => no_descent_gain A S phase hm omega c d hc x ii T
    hx hy hpx hpy hr hn hT hclose hno h.1 h.2)

end PlanarL1.Columns.Model.MainFamily

end



section

namespace PlanarL1.Columns.Model.VertexBands
open Parameters MeasureTheory
variable {k : ℕ} {M : Model (k+1)} {V : Type*}
variable (A : Ambient M) (v : V → M.Point Set.univ A.root)
variable {L U : ℝ} (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q : ℝ} (phase : MainFamily.BandComponent (M := M) q L U → ℝ)
noncomputable def mainCell (x : V) : MainFamily.CellIndex q L U phase :=
  ⟨bandComponent A v L U hv q x,
    (BandTrees.main_cover broad (lower A v L U hv q x) (component A v L U hv q x)
      (phase (bandComponent A v L U hv q x)) (i := (v x).column) rfl).choose⟩
lemma mainCell_column (x : V) : (v x).column ∈ ColumnOrder.componentColumns (mainCell A v hv phase x).2.2 :=
  (BandTrees.main_cover broad (lower A v L U hv q x) (component A v L U hv q x)
    (phase (bandComponent A v L U hv q x)) (i := (v x).column) rfl).choose_spec
lemma mainCell_mem (x : V) : (v x).height∈MainFamily.domain phase (mainCell A v hv phase x) (v x).column :=
  (MainCell.mem_domain _ _ _).mpr ⟨mainCell_column A v hv phase x,height_mem A v L U hv q x⟩
end PlanarL1.Columns.Model.VertexBands

namespace PlanarL1.Columns.Model.PairGeometry
open Parameters MeasureTheory VertexTests VertexBands
attribute [local instance] Classical.propDecidable
attribute [local irreducible] FiniteRandom.prob
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω} {ν : Measure Ξ}
variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)
variable (SB : BState M kappaB SecondaryGeometry.Group.lam Ξ ν)
variable (v : V → M.Point Set.univ A.root)
variable {L U : ℝ} (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q p : ℝ} {phaseD phaseG : MainFamily.BandComponent (M := M) q L U → ℝ}
variable {x y : V} (he : Eligible A SA SB v x y)
variable (hi : Interior A v (hv := hv) q p phaseD phaseG x)
variable (hj : Interior A v (hv := hv) q p phaseD phaseG y)
variable (hc : Cutoffs A SA SB v x y) (ha : 1≤dist (v x) (v y))

include he in
lemma main_available : MainFamily.Available A SA phaseD (mainCell A v hv phaseD x) :=
  MainFamily.available_of_ball5 A SA phaseD _ (v x) (mainCell_mem A v hv phaseD x) he.1
lemma main_index : MainFamily.index A SA phaseD (mainCell A v hv phaseD x) (main_available A SA SB v hv he)=indexA A SA v x :=
  (MainFamily.same_name A SA phaseD _ (main_available A SA SB v hv he) _ _ (mainCell_mem A v hv phaseD x)).symm

private lemma comparison_coordinates {D E : OrdinaryData M} (hDE : D=E)
    {i j : Fin (k+1)} (hij : i=j) {H T : ℝ} (hHT : H=T) (hD : H∈D.band) (hE : T∈E.band) :
    D.comparison.value i ⟨H,hD⟩=E.comparison.value j ⟨T,hE⟩ := by
  subst E; subst j; subst T; rfl

include hj hc ha in
lemma no_descent_probability {m : ℕ} (hm : 0 < m)
    (hno : ¬Nonempty ((SA.chart (indexA A SA v x)).comparison.BandDescent
      (BandTrees.band broad (lower A v L U hv q x))
      ((position A SA SB v hv he hi).point.widen (position A SA SB v hv he hi).subA) epsilon)) :
    1/4≤FiniteRandom.prob (fun omega : MainFamily.Sample phaseD m =>
      kappaA*EA < (MainFamily.batch A SA phaseD hm omega).sets.separation
        (v x).column (v x).height (v y).column (v y).height) := by
  let c := mainCell A v hv phaseD x
  let d := mainCell A v hv phaseD y
  let hav := main_available A SA SB v hv he (phaseD := phaseD)
  have hidx := main_index A SA SB v hv he (phaseD := phaseD)
  have hn : SA.name (v y).column (v y).height=MainFamily.index A SA phaseD c hav :=
    (he.namesA A SA SB v).trans hidx.symm
  have hT : (v y).height∈(SA.chart (MainFamily.index A SA phaseD c hav)).band := by
    rw [←hn]; exact SA.height_in _ _
  have hclose : |(SA.chart (MainFamily.index A SA phaseD c hav)).comparison.eval
      ((point A v L U hv q x).widen (MainFamily.sub_old A SA phaseD c hav))-
      (SA.chart (MainFamily.index A SA phaseD c hav)).comparison.value
        (v y).column ⟨(v y).height,hT⟩|≤EA := by
    have hx := comparison_coordinates (congrArg SA.chart hidx) (i := (v x).column) rfl
      (H := (v x).height) rfl
      (MainFamily.sub_old A SA phaseD c hav (height_mem A v L U hv q x)) (SA.height_in _ _)
    have hy := comparison_coordinates (congrArg SA.chart (hidx.trans (he.namesA A SA SB v).symm))
      (i := (v y).column) rfl (H := (v y).height) rfl hT (SA.height_in _ _)
    change |(SA.chart (MainFamily.index A SA phaseD c hav)).comparison.value (v x).column _-
      (SA.chart (MainFamily.index A SA phaseD c hav)).comparison.value (v y).column _|≤EA
    have hb : |(SA.chart (MainFamily.index A SA phaseD c hav)).comparison.value (v x).column ⟨(v x).height,MainFamily.sub_old A SA phaseD c hav (height_mem A v L U hv q x)⟩ - (SA.chart (MainFamily.index A SA phaseD c hav)).comparison.value (v y).column ⟨(v y).height,hT⟩| ≤ EA := by
      rw [hx,hy]
      exact hc.2.1.le
    exact hb
  apply MainFamily.no_descent_probability A SA phaseD hm c d hav (point A v L U hv q x)
    (v y).column (v y).height (mainCell_column A v hv phaseD x) (mainCell_mem A v hv phaseD y)
    hi.1 hj.1 hi.2.2.1 hn hT hclose _
    (MainFamily.distinct_cells A phaseD (v x) (v y) ha c d (mainCell_mem A v hv phaseD x) (mainCell_mem A v hv phaseD y))
  intro h
  apply hno
  exact OrdinaryData.descent_coordinates (congrArg SA.chart hidx) rfl _ _ h rfl rfl
end PlanarL1.Columns.Model.PairGeometry

end

end OAI
