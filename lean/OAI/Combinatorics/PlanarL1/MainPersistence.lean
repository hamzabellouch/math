import OAI.Combinatorics.PlanarL1.MainFamily

namespace OAI


section

namespace PlanarL1.Columns.Model
open MeasureTheory
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {M : Model n} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

namespace OrdinaryState.MainBatch
variable {κ : ℝ} {S : OrdinaryState M κ Ω μ} (B : MainBatch S)
lemma choose_eq {i j : Fin n} {H T : ℝ}
    (he : ∀ q, (B.step q).choose i H=(B.step q).choose j T) :
    B.choose i H=B.choose j T := by
  have h : B.chosen i H=B.chosen j T := by
    funext a
    simp only [chosen,he a.1]
  unfold choose
  simp only [h]

lemma name_eq [SFinite μ] {i j : Fin n} {H T : ℝ}
    (hold : S.name i H=S.name j T) (he : B.choose i H=B.choose j T) :
    B.apply.name i H=B.apply.name j T := by
  dsimp only [apply,OrdinaryState.append,OrdinaryState.lift]
  rw [he,hold]
end OrdinaryState.MainBatch

namespace MainCell
variable {I J : Set ℝ} {root : Fin n} (F : M.Field I 1) (hJI : J ⊆ I)
  (R : Point.RadialTree (M := M) (J := J) (root := root)) (q : ℝ)
  (C : Cell R q)
lemma choose_eq_of_name (v : M.Point J root)
    (α : Point.RadialTree.Noise (n := n)) (E β lo : ℝ) {i j : Fin n} {H T : ℝ}
    (hi : H ∈ domain R q C i) (hj : T ∈ domain R q C j)
    (hn : (namedReplacement F hJI R q C v α E β lo (cellPoint R q C i H hi)).name=
      (namedReplacement F hJI R q C v α E β lo (cellPoint R q C j T hj)).name) :
    choose F hJI R q C v α E β lo i H=choose F hJI R q C v α E β lo j T := by
  simp only [choose,dite_eq_left hi,dite_eq_left hj]
  simp only [hn]

lemma choose_none_of_name (v : M.Point J root)
    (α : Point.RadialTree.Noise (n := n)) (E β lo : ℝ) {i : Fin n} {H : ℝ}
    (hi : H ∈ domain R q C i)
    (hn : (namedReplacement F hJI R q C v α E β lo (cellPoint R q C i H hi)).name=0) :
    choose F hJI R q C v α E β lo i H=none := by
  simp only [choose,dite_eq_left hi,dite_eq_left hn]
end MainCell
end PlanarL1.Columns.Model

end



section

namespace PlanarL1.Tiling
lemma near_band_unique {a q h t H : ℝ} (ha : 0<a) (_ht : 0≤t)
    (hp : Padded a q h t) (hd : |H-h|≤t) {b : ℤ} (hb : H ∈ band a q b) :
    b=index a q h := by
  rcases lt_trichotomy b (index a q h) with hl | he | hu
  · have hbl : (b:ℝ)+1≤(index a q h:ℝ) := by
      exact_mod_cast (show b+1≤ index a q h by omega)
    have hv := mul_le_mul_of_nonneg_right hbl ha.le
    have hlo := hp.1
    change q+(index a q h:ℝ)*a+t<h at hlo
    have hh := hb.2
    change H≤q+((b:ℝ)+1)*a at hh
    have hd' := (abs_le.mp hd).1
    linarith
  · exact he
  · have hbl : (index a q h:ℝ)+1≤(b:ℝ) := by
      exact_mod_cast (show index a q h+1≤b by omega)
    have hv := mul_le_mul_of_nonneg_right hbl ha.le
    have hup := hp.2
    change h<q+((index a q h:ℝ)+1)*a-t at hup
    have hh := hb.1
    change q+(b:ℝ)*a≤H at hh
    have hd' := (abs_le.mp hd).2
    linarith

lemma near_mem_band {a q h t H : ℝ} (_ha : 0<a) (_ht : 0≤t)
    (hp : Padded a q h t) (hd : |H-h|≤t) : H ∈ band a q (index a q h) := by
  change q+(index a q h:ℝ)*a≤H ∧ H≤q+((index a q h:ℝ)+1)*a
  have hlo := hp.1
  have hup := hp.2
  change q+(index a q h:ℝ)*a+t<h at hlo
  change h<q+((index a q h:ℝ)+1)*a-t at hup
  have hd' := abs_le.mp hd
  constructor <;> linarith
end PlanarL1.Tiling

namespace PlanarL1.Columns.Model
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)}
namespace Point
lemma local_center {J : Set ℝ} {r s : Fin (k+1)}
    (x y : M.Point Set.univ r) (y' : M.Point J s)
    (hy : y'.column=y.column) (_hY : y'.height=y.height) {ρ : ℝ} (hρ : 0≤ρ)
    (hJ : ∀ H, |H-x.height|≤ρ → H ∈ J) (hd : dist x y≤ρ) :
    ∃ x' : M.Point J s, x'.column=x.column ∧ x'.height=x.height := by
  obtain ⟨p,_,hp⟩ := x.exists_shortest isClosed_univ y
  obtain ⟨q,_⟩ := p.restrict_of_length x.height y.height x.height ρ hJ (by simpa [hp] using hd)
  have hxJ : x.height ∈ J := hJ _ (by simpa using hρ)
  refine ⟨⟨x.column,x.height,hxJ,?_⟩,rfl,rfl⟩
  exact y'.reachable.trans (hy.symm ▸ q.word.reachable.symm)
end Point
namespace MainFamily
open Parameters
variable (A : Ambient M) {q L U : ℝ}
  (phase : BandComponent (M := M) q L U → ℝ)
  (x : M.Point Set.univ A.root) {ρ : ℝ} (hρ : 0≤ρ)
  (hp : Tiling.Padded a₁ q x.height ρ)

include hρ hp
lemma touched_band {c : CellIndex q L U phase} {y : M.Point Set.univ A.root}
    (hy : dist x y≤ρ) (hc : y.height ∈ domain phase c y.column) :
    c.1.1.val=Tiling.index a₁ q x.height := by
  apply Tiling.near_band_unique interpolationA.2.1 hρ hp _ (domain_band phase c hc)
  rw [abs_sub_comm]
  exact (x.height_change_le y).trans hy

lemma touched_envelope {c : CellIndex q L U phase} {y : M.Point Set.univ A.root}
    (hy : dist x y≤ρ) (hc : y.height ∈ domain phase c y.column) :
    ∀ H, |H-x.height|≤ρ → H ∈ BandTrees.band broad (lower q L U c.1.1) := by
  intro H hH
  have he := touched_band A phase x hρ hp hy hc
  have hb := Tiling.near_mem_band interpolationA.2.1 hρ hp hH
  rw [←he] at hb
  change q+(c.1.1.val:ℝ)*a₁≤H ∧ H≤q+(c.1.1.val:ℝ)*a₁+a₁
  dsimp only [Tiling.band,Set.mem_Icc] at hb
  constructor <;> linarith [hb.1,hb.2]

lemma local_center {c : CellIndex q L U phase} {y : M.Point Set.univ A.root}
    (hy : dist x y≤ρ) (hc : y.height ∈ domain phase c y.column) :
    ∃ x' : M.Point (BandTrees.band broad (lower q L U c.1.1))
      (BandTrees.root M broad (lower q L U c.1.1) c.1.2),
      x'.column=x.column ∧ x'.height=x.height :=
  Point.local_center x y (MainCell.cellPoint (tree phase c) (radial phase c) c.2.2 _ _ hc)
    rfl rfl hρ (touched_envelope A phase x hρ hp hy hc) hy

lemma local_ball {c : CellIndex q L U phase}
    (x' : M.Point (BandTrees.band broad (lower q L U c.1.1))
      (BandTrees.root M broad (lower q L U c.1.1) c.1.2))
    (hx : x'.column=x.column) (hX : x'.height=x.height)
    {y : M.Point Set.univ A.root} (hy : dist x y≤ρ)
    (hc : c.1.1.val=Tiling.index a₁ q x.height) :
    ∃ y' : M.Point (BandTrees.band broad (lower q L U c.1.1))
      (BandTrees.root M broad (lower q L U c.1.1) c.1.2),
      y'.column=y.column ∧ y'.height=y.height ∧ dist x' y'=dist x y := by
  apply Point.local_point x y x' hx hX isClosed_univ (Set.subset_univ _) _ hy
  intro H hH
  have hb := Tiling.near_mem_band interpolationA.2.1 hρ hp hH
  rw [←hc] at hb
  change q+(c.1.1.val:ℝ)*a₁≤H ∧ H≤q+(c.1.1.val:ℝ)*a₁+a₁
  dsimp only [Tiling.band,Set.mem_Icc] at hb
  constructor <;> linarith [hb.1,hb.2]
end MainFamily
end PlanarL1.Columns.Model

end



section

namespace PlanarL1.Columns.Model
open MeasureTheory
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)}
namespace Point
lemma eq_of_coordinates {J : Set ℝ} {r : Fin (k+1)} (x y : M.Point J r)
    (hc : x.column=y.column) (hh : x.height=y.height) : x=y := by
  cases x
  cases y
  cases hc
  cases hh
  rfl
end Point
namespace MainFamily
open Parameters
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable (A : Ambient M) (S : OrdinaryState M kappaA Ω μ)
variable {q L U : ℝ} (phase : BandComponent (M := M) q L U → ℝ)
variable {m : ℕ} (hm : 0 < m) (omega : Sample phase m)
variable (x : M.Point Set.univ A.root) {ρ : ℝ} (hρ : 0≤ρ)
    (hp : Tiling.Padded a₁ q x.height ρ) (hsmall : 4*ρ<3*EA)

include hρ hp hsmall
/-- An actual available main cell does not install an identifier anywhere in a
small padded ball if that ball has a column outside the cell. -/
lemma choose_none_crossed (c : Kept A S phase omega)
    (hex : ∃ y : M.Point Set.univ A.root, dist x y≤ρ ∧
      y.column ∉ ColumnOrder.componentColumns c.val.2.2)
    (z : M.Point Set.univ A.root) (hz : dist x z≤ρ) :
    (keptStep A S phase hm omega c).choose z.column z.height=none := by
  let V := keptStep A S phase hm omega c
  change MainCell.choose V.comparison V.sub_old V.tree V.phase V.cell V.anchor
    V.noise V.error V.shield_offset V.lo z.column z.height=none
  by_cases hd : z.height ∈ domain phase c.val z.column
  · obtain ⟨x',hx,hX⟩ := local_center A phase x hρ hp hz hd
    have hb := touched_band A phase x hρ hp hz hd
    obtain ⟨w,hw,hW,hdw⟩ := local_ball A phase x hρ hp x' hx hX hz hb
    have hw' : w=MainCell.cellPoint V.tree V.phase V.cell z.column z.height hd :=
      Point.eq_of_coordinates _ _ hw hW
    obtain ⟨y,hy,hout⟩ := hex
    obtain ⟨y',hy',hY,hdy⟩ := local_ball A phase x hρ hp x' hx hX hy hb
    have hh := MainCell.namedReplacement_retained_on_touched_ball V.comparison V.sub_old
      V.tree V.phase V.cell isCompact_Icc V.anchor x' V.noise_bounds
      interpolationA.1.le (show V.tree.δ=EA/8 by rfl) V.shield_offset V.lo hsmall
      ⟨y',by simpa only [hdy] using hy,by
        change y'.column ∉ ColumnOrder.componentColumns c.val.2.2
        rwa [hy']⟩
      w (by simpa only [hdw] using hz) (by
        rw [hw]
        exact ((MainCell.mem_domain _ _ _).mp hd).1)
    apply MainCell.choose_none_of_name V.comparison V.sub_old V.tree V.phase V.cell
      V.anchor V.noise V.error V.shield_offset V.lo hd
    rw [←hw']
    exact congrArg PlanarL1.Interpolation.NamedValue.name hh
  · exact MainCell.choose_none_outside V.comparison V.sub_old V.tree V.phase V.cell
      V.anchor V.noise V.error V.shield_offset V.lo _ _ hd

/-- If two main cells are seen by the center ball, every cell's chosen name is
none on the ball. This also covers two representatives of the same quotient
point and arbitrarily many touched cells. -/
lemma all_choices_none_crossed (c : CellIndex q L U phase)
    (hc : x.height ∈ domain phase c x.column)
    (hex : ∃ y : M.Point Set.univ A.root, dist x y≤ρ ∧
      y.column ∉ ColumnOrder.componentColumns c.2.2)
    (z : M.Point Set.univ A.root) (hz : dist x z≤ρ)
    (d : Kept A S phase omega) :
    (keptStep A S phase hm omega d).choose z.column z.height=none := by
  by_cases hd : z.height ∈ domain phase d.val z.column
  · apply choose_none_crossed A S phase hm omega x hρ hp hsmall d _ z hz
    by_cases he : c=d.val
    · subst c
      exact hex
    · refine ⟨x,by simpa using hρ,?_⟩
      intro hx
      have hb := touched_band A phase x hρ hp hz hd
      have hcband := touched_band A phase x hρ hp (y := x) (by simpa using hρ) hc
      have hband : c.1.1=d.val.1.1 := Subtype.ext (hcband.trans hb.symm)
      have hxd : x.height ∈ domain phase d.val x.column :=
        (MainCell.mem_domain _ _ _).mpr ⟨hx,touched_envelope A phase x hρ hp hz hd
          x.height (by simpa using hρ)⟩
      exact he (unique_in_band phase hband hc hxd)
  · exact MainCell.choose_none_outside
      (keptStep A S phase hm omega d).comparison (keptStep A S phase hm omega d).sub_old
      (tree phase d.val) (radial phase d.val) d.val.2.2 (anchor phase d.val)
      (keptStep A S phase hm omega d).noise EA (keptStep A S phase hm omega d).shield_offset
      (lower q L U d.val.1.1) z.column z.height hd
end MainFamily
end PlanarL1.Columns.Model

end



section

namespace PlanarL1.FiniteRandom
lemma prob_pi_eval_bound {I : Type*} {D : I → Type*} [Fintype I] [DecidableEq I]
    [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)] (i : I) (P : D i → Prop)
    {b : ℝ} (h : prob P≤b) : prob (fun f : ∀ i, D i => P (f i))≤b := by
  classical
  let e := Equiv.piSplitAt i D
  have he (u : D i × (∀ j : {j // j≠i}, D j.val)) : (e.symm u) i=u.1 :=
    congrArg Prod.fst (e.apply_symm_apply u)
  rw [←prob_equiv e.symm]
  apply prob_prod_bound_left
  intro f
  simpa only [he] using h
end PlanarL1.FiniteRandom

end



section

namespace PlanarL1.Columns.Model.MainFamily
open MeasureTheory Parameters
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable (A : Ambient M) (S : OrdinaryState M kappaA Ω μ)
variable {q L U : ℝ} (phase : BandComponent (M := M) q L U → ℝ)
variable {m : ℕ} (hm : 0 < m) (omega : Sample phase m)
variable (x : M.Point Set.univ A.root) {ρ : ℝ} (hρ : 0≤ρ)
    (hp : Tiling.Padded a₁ q x.height ρ) (hsmall : 4*ρ<3*EA)

noncomputable def sampleName (c : CellIndex q L U phase) (hc : Available A S phase c)
    (w : Point.RadialTree.GridSample (n := k+1) (tree phase c).depthCap m × Fin (m+1))
    (z : M.Point (BandTrees.band broad (lower q L U c.1.1))
      (BandTrees.root M broad (lower q L U c.1.1) c.1.2)) : ℕ :=
  (MainCell.namedReplacement (S.chart (index A S phase c hc)).comparison
    (sub_old A S phase c hc) (tree phase c) (radial phase c) c.2.2 (anchor phase c)
    ((tree phase c).gridNoise (tree phase c).depthCap m w.1) EA (EA/m*w.2.val)
    (lower q L U c.1.1) z).name

include hρ hp in
lemma choose_none_other (c : CellIndex q L U phase)
    (hfull : ∀ z : M.Point Set.univ A.root, dist x z≤ρ → z.height ∈ domain phase c z.column)
    (d : Kept A S phase omega) (hne : d.val≠c)
    (z : M.Point Set.univ A.root) (hz : dist x z≤ρ) :
    (keptStep A S phase hm omega d).choose z.column z.height=none := by
  apply MainCell.choose_none_outside
  intro hd
  have hd' : z.height ∈ domain phase d.val z.column := hd
  have hb := touched_band A phase x hρ hp hz hd'
  have hcband := touched_band A phase x hρ hp hz (hfull z hz)
  exact hne (unique_in_band phase (Subtype.ext (hb.trans hcband.symm)) hd' (hfull z hz))

include hρ hp hsmall in
lemma result_name_eq [SFinite μ] (c : CellIndex q L U phase)
    (hc : x.height ∈ domain phase c x.column)
    (hcontrol : ∀ hav : Available A S phase c,
      let x' := MainCell.cellPoint (tree phase c) (radial phase c) c.2.2 x.column x.height hc
      ∀ z, dist x' z≤ρ →
        sampleName A S phase c hav ((omega c).1,(omega c).2.1) z=
          sampleName A S phase c hav ((omega c).1,(omega c).2.1) x')
    (z : M.Point Set.univ A.root) (hz : dist x z≤ρ)
    (hold : S.name z.column z.height=S.name x.column x.height) :
    (result A S phase hm omega).name z.column z.height=
      (result A S phase hm omega).name x.column x.height := by
  apply OrdinaryState.MainBatch.name_eq _ hold
  apply OrdinaryState.MainBatch.choose_eq
  intro j
  let d : Kept A S phase omega := (Fintype.equivFin (Kept A S phase omega)).symm j
  change (keptStep A S phase hm omega d).choose z.column z.height=
    (keptStep A S phase hm omega d).choose x.column x.height
  by_cases hex : ∃ y : M.Point Set.univ A.root, dist x y≤ρ ∧
      y.column ∉ ColumnOrder.componentColumns c.2.2
  · rw [all_choices_none_crossed A S phase hm omega x hρ hp hsmall c hc hex z hz d,
      all_choices_none_crossed A S phase hm omega x hρ hp hsmall c hc hex x (by simpa using hρ) d]
  · have hfull (y : M.Point Set.univ A.root) (hy : dist x y≤ρ) :
        y.height ∈ domain phase c y.column := by
      apply (MainCell.mem_domain _ _ _).mpr
      refine ⟨?_,?_⟩
      · by_contra hn
        exact hex ⟨y,hy,hn⟩
      · apply touched_envelope A phase x hρ hp (by simpa using hρ) hc
        rw [abs_sub_comm]
        exact (x.height_change_le y).trans hy
    by_cases he : d.val=c
    · subst c
      let V := keptStep A S phase hm omega d
      have hdz := hfull z hz
      apply MainCell.choose_eq_of_name V.comparison V.sub_old V.tree V.phase V.cell V.anchor
        V.noise V.error V.shield_offset V.lo hdz hc
      let x' := MainCell.cellPoint (tree phase d.val) (radial phase d.val) d.val.2.2
        x.column x.height hc
      have hb := touched_band A phase x hρ hp (by simpa using hρ) hc
      obtain ⟨z',hz',hZ,hd⟩ := local_ball A phase x hρ hp x' rfl rfl hz hb
      have hd' : dist x' z'≤ρ := hd.le.trans hz
      have hn := hcontrol d.property.1 z' hd'
      have hzP : z'=MainCell.cellPoint (tree phase d.val) (radial phase d.val) d.val.2.2
          z.column z.height hdz := Point.eq_of_coordinates _ _ hz' hZ
      rw [hzP] at hn
      exact hn
    · rw [choose_none_other A S phase hm omega x hρ hp c hfull d he z hz,
        choose_none_other A S phase hm omega x hρ hp c hfull d he x (by simpa using hρ)]
end PlanarL1.Columns.Model.MainFamily

end



section

namespace PlanarL1.Columns.Model.MainFamily
open MeasureTheory Parameters FiniteRandom
attribute [local instance] Classical.propDecidable
attribute [local irreducible] FiniteRandom.prob
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable (A : Ambient M) (S : OrdinaryState M kappaA Ω μ)
variable {q L U : ℝ} (phase : BandComponent (M := M) q L U → ℝ)

noncomputable def localLoss (c : CellIndex q L U phase) (ρ : ℝ) (m : ℕ) : ℝ :=
  (6*((tree phase c).lookback+1)+2 : ℕ)^2 *
    ((4*(MainCell.replacementConstant (tree phase c) : ℝ)*ρ+(tree phase c).q/m)/(tree phase c).q+
      (4*(MainCell.replacementConstant (tree phase c) : ℝ)*ρ+EA/m)/EA)
lemma localLoss_nonneg (c : CellIndex q L U phase) {ρ : ℝ} (hρ : 0≤ρ) (m : ℕ) :
    0≤localLoss phase c ρ m := by
  unfold localLoss
  positivity [(tree phase c).q_pos,interpolationA.1]

lemma sampleName_probability (c : CellIndex q L U phase) (hc : Available A S phase c)
    (x : M.Point (BandTrees.band broad (lower q L U c.1.1))
      (BandTrees.root M broad (lower q L U c.1.1) c.1.2))
    {ρ : ℝ} (hρ : 0≤ρ) (hr : ρ≤(tree phase c).radius) (m : ℕ) (hm : 0 < m) :
    prob (fun omega : Sample phase m => ∃ z, dist x z≤ρ ∧
      sampleName A S phase c hc ((omega c).1,(omega c).2.1) z≠
        sampleName A S phase c hc ((omega c).1,(omega c).2.1) x)≤localLoss phase c ρ m := by
  classical
  apply prob_pi_eval_bound (D := fun d => CellSample phase d m) c
    (fun w => ∃ z, dist x z≤ρ ∧
      sampleName A S phase c hc (w.1,w.2.1) z≠sampleName A S phase c hc (w.1,w.2.1) x)
  let e := Equiv.prodAssoc
    (Point.RadialTree.GridSample (n := k+1) (tree phase c).depthCap m) (Fin (m+1)) Bool
  rw [←prob_equiv e]
  apply prob_prod_bound_left
  intro b
  exact MainCell.namedReplacement_probability (S.chart (index A S phase c hc)).comparison
    (sub_old A S phase c hc) (tree phase c) (radial phase c) c.2.2 isCompact_Icc
    (anchor phase c) x EA (lower q L U c.1.1) EA interpolationA.1 hρ hr m hm

/-- Chart persistence for the **whole literal main mode**, conditional on the
padded height band. No factor depending on the number of graph cells occurs. -/
lemma persistence_probability [SFinite μ] (x : M.Point Set.univ A.root)
    (c : CellIndex q L U phase) (hc : x.height ∈ domain phase c x.column)
    {ρ : ℝ} (hρ : 0≤ρ) (hp : Tiling.Padded a₁ q x.height ρ)
    (hsmall : 4*ρ<3*EA) (hr : ρ≤(tree phase c).radius)
    (hold : ∀ z : M.Point Set.univ A.root, dist x z≤ρ →
      S.name z.column z.height=S.name x.column x.height)
    (m : ℕ) (hm : 0 < m) :
    prob (fun omega : Sample phase m => ∃ z : M.Point Set.univ A.root, dist x z≤ρ ∧
      (result A S phase hm omega).name z.column z.height≠
        (result A S phase hm omega).name x.column x.height) ≤ localLoss phase c ρ m := by
  classical
  by_cases hav : Available A S phase c
  · let x' := MainCell.cellPoint (tree phase c) (radial phase c) c.2.2 x.column x.height hc
    apply (prob_mono (Q := fun omega : Sample phase m => ∃ z, dist x' z≤ρ ∧
      sampleName A S phase c hav ((omega c).1,(omega c).2.1) z≠
        sampleName A S phase c hav ((omega c).1,(omega c).2.1) x') _).trans
      (sampleName_probability A S phase c hav x' hρ hr m hm)
    intro omega hbad
    by_contra hn
    obtain ⟨z,hz,hz'⟩ := hbad
    apply hz'
    apply result_name_eq A S phase hm omega x hρ hp hsmall c hc _ z hz (hold z hz)
    intro hc'
    dsimp only
    intro y hy
    exact not_ne_iff.mp (fun he => hn ⟨y,hy,he⟩)
  · have hzero : prob (fun omega : Sample phase m => ∃ z : M.Point Set.univ A.root,
        dist x z≤ρ ∧ (result A S phase hm omega).name z.column z.height≠
          (result A S phase hm omega).name x.column x.height)≤prob (fun _ : Sample phase m => False) := by
      apply prob_mono
      intro omega ⟨z,hz,hz'⟩
      exact hz' (result_name_eq A S phase hm omega x hρ hp hsmall c hc
        (fun hc' => False.elim (hav hc')) z hz (hold z hz))
    rw [prob_false] at hzero
    exact hzero.trans (localLoss_nonneg phase c hρ m)
end PlanarL1.Columns.Model.MainFamily

end

end OAI
