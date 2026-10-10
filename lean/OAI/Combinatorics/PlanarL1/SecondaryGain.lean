import OAI.Combinatorics.PlanarL1.MainGain

namespace OAI


section

namespace PlanarL1.Columns.Model.RetainedSelection
open Parameters
variable {k : ℕ} {M : Model (k+1)} {q p L U : ℝ}
namespace Block
variable (b : Block (M := M) q p L U)
lemma broad_eq : BandTrees.band broad b.lower=Tiling.band a₁ q b.1.1.val := by
  ext H
  simp only [BandTrees.band,lower,MainFamily.lower,Tiling.band,Set.mem_Icc]
  change (_≤H ∧ H≤q+(b.1.1.val:ℝ)*a₁+a₁) ↔ (_≤H ∧ H≤q+((b.1.1.val:ℝ)+1)*a₁)
  ring_nf
lemma narrow_eq : BandTrees.band narrow b.lower₂=Tiling.band a₂ p b.2.val.val := by
  ext H
  simp only [BandTrees.band,lower₂,Tiling.band,Set.mem_Icc]
  change (_≤H ∧ H≤p+(b.2.val.val:ℝ)*a₂+a₂) ↔ (_≤H ∧ H≤p+((b.2.val.val:ℝ)+1)*a₂)
  ring_nf

/-- At a doubly height-interior point, a narrow-band path can reach a seed
only in this very processed broad/component/narrow block. -/
lemma eq_of_path (d : Block (M := M) q p L U)
    (c : M.Point (BandTrees.band broad b.lower) (BandTrees.root M broad b.lower b.1.2))
    (e : M.Point (BandTrees.band broad d.lower) (BandTrees.root M broad d.lower d.1.2))
    (hc : c.height ∈ BandTrees.band narrow b.lower₂)
    (hd : c.height ∈ BandTrees.band narrow d.lower₂)
    (hp : Tiling.Padded a₁ q c.height (a₁/10))
    (hn : Tiling.Padded a₂ p c.height (a₂/10))
    (path : M.Path (BandTrees.band narrow d.lower₂) c.column e.column) : b=d := by
  have hNb : b.2.val.val=Tiling.index a₂ p c.height :=
    Tiling.unique_band_of_padded interpolationB.2.1 (by norm_num [a₂]) hn (b.narrow_eq ▸ hc)
  have hNd : d.2.val.val=Tiling.index a₂ p c.height :=
    Tiling.unique_band_of_padded interpolationB.2.1 (by norm_num [a₂]) hn (d.narrow_eq ▸ hd)
  have hBb : b.1.1.val=Tiling.index a₁ q c.height :=
    Tiling.unique_band_of_padded interpolationA.2.1 (by norm_num [a₁]) hp (b.broad_eq ▸ c.inBand)
  have hBd : d.1.1.val=Tiling.index a₁ q c.height :=
    Tiling.unique_band_of_padded interpolationA.2.1 (by norm_num [a₁]) hp (d.broad_eq ▸ d.sub hd)
  have hB : b.1.1=d.1.1 := Subtype.ext (hBb.trans hBd.symm)
  rcases b with ⟨⟨bi,bC⟩,bn⟩
  rcases d with ⟨⟨di,dC⟩,dn⟩
  dsimp only at hB
  subst di
  have hC : bC=dC := by
    have hr := c.reachable.trans ((path.widen (Block.sub ⟨⟨bi,dC⟩,dn⟩)).word.reachable.trans e.reachable.symm)
    have hm := SimpleGraph.ConnectedComponent.sound hr
    have hb : (M.activeGraph (BandTrees.band broad (MainFamily.lower q L U bi))).connectedComponentMk
        (BandTrees.root M broad (MainFamily.lower q L U bi) bC)=bC := BandTrees.root_mem _ _ _ _
    have hd' : (M.activeGraph (BandTrees.band broad (MainFamily.lower q L U bi))).connectedComponentMk
        (BandTrees.root M broad (MainFamily.lower q L U bi) dC)=dC := BandTrees.root_mem _ _ _ _
    exact hb.symm.trans (hm.trans hd')
  subst dC
  have hN : bn=dn := Subtype.ext (Subtype.ext (hNb.trans hNd.symm))
  subst dn
  rfl
end Block
end PlanarL1.Columns.Model.RetainedSelection

end



section

namespace PlanarL1.Columns.Model.RetainedSelection
open Parameters MeasureTheory
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [Fintype V] [MeasurableSpace Ω] [MeasurableSpace Ξ]
variable {μ : Measure Ω} {ν : Measure Ξ}
variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)
variable (SB : BState M kappaB SecondaryGeometry.Group.lam Ξ ν)
variable (v : V → M.Point Set.univ A.root)
variable {L U : ℝ} (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q p : ℝ} {phaseD phaseG : MainFamily.BandComponent (M := M) q L U → ℝ}
variable (b : Block (M := M) q p L U)
variable (c : M.Point (BandTrees.band broad b.lower) (BandTrees.root M broad b.lower b.1.2))

/-- All actual processed groups that can affect this point through their
narrow-band geometry. It is not just the groups having a prescribed ID. -/
def Touch (i : GroupIndex A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG)) : Prop :=
  c.height ∈ BandTrees.band narrow i.1.lower₂ ∧
  ∃ w, SurvivingGroups.key (localSeeds A SA SB v hv (phaseD := phaseD) (phaseG := phaseG) i.1) w=i.2.val ∧
    ∃ path : M.Path (BandTrees.band narrow i.1.lower₂) c.column (localSeeds A SA SB v hv (phaseD := phaseD) (phaseG := phaseG) i.1 w).point.column,
      path.length c.height (localSeeds A SA SB v hv (phaseD := phaseD) (phaseG := phaseG) i.1 w).point.height≤4*R
noncomputable abbrev Hits :=
  {i : GroupIndex A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG) // Touch A SA SB v hv b c i}
noncomputable instance : Fintype (Hits A SA SB v hv b c (phaseD := phaseD) (phaseG := phaseG)) :=
  Fintype.ofFinite _

variable (hc : c.height ∈ BandTrees.band narrow b.lower₂)
variable (hp : Tiling.Padded a₁ q c.height (a₁/10)) (hn : Tiling.Padded a₂ p c.height (a₂/10))
include hc hp hn

lemma touch_block {i : GroupIndex A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG)}
    (h : Touch A SA SB v hv b c i) : i.1=b := by
  obtain ⟨w,_,path,_⟩ := h.2
  exact (b.eq_of_path i.1 c (localSeeds A SA SB v hv (phaseD := phaseD) (phaseG := phaseG) i.1 w).point hc h.1 hp hn path).symm

noncomputable def localHit (i : Hits A SA SB v hv b c (phaseD := phaseD) (phaseG := phaseG)) :
    SurvivingGroups.Hits (localSeeds A SA SB v hv (phaseD := phaseD) (phaseG := phaseG) b) c := by
  have he := touch_block A SA SB v hv b c hc hp hn i.property
  rcases i with ⟨⟨d,j⟩,hi⟩
  dsimp only at he
  subst d
  exact ⟨j,hi.2⟩

lemma localHit_injective : Function.Injective
    (localHit A SA SB v hv b c hc hp hn (phaseD := phaseD) (phaseG := phaseG)) := by
  intro i j he
  have hi := touch_block A SA SB v hv b c hc hp hn i.property
  have hj := touch_block A SA SB v hv b c hc hp hn j.property
  rcases i with ⟨⟨d,i⟩,hi'⟩
  rcases j with ⟨⟨e,j⟩,hj'⟩
  dsimp only at hi hj
  subst d
  subst e
  have hraw : i=j := congrArg Subtype.val he
  subst j
  rfl

/-- Universal packing for the whole actual, finitely selected family. Both
old identifiers are derived by the local packing theorem, not assumed. -/
lemma touching_card : Fintype.card (Hits A SA SB v hv b c (phaseD := phaseD) (phaseG := phaseG))≤
    SurvivingGroups.packBound := by
  let := SurvivingGroups.instFintypeHits
    (localSeeds A SA SB v hv (phaseD := phaseD) (phaseG := phaseG) b) c
  have hb := SurvivingGroups.touching_card
    (localSeeds A SA SB v hv (phaseD := phaseD) (phaseG := phaseG) b) b.sub c hc
  apply le_trans _ hb
  exact Fintype.card_le_of_injective _ (localHit_injective A SA SB v hv b c hc hp hn)

lemma touching_finset_card :
    (Finset.univ.filter (Touch A SA SB v hv b c (phaseD := phaseD) (phaseG := phaseG))).card≤
      SurvivingGroups.packBound := by
  simpa only [Hits,Fintype.card_subtype] using touching_card A SA SB v hv b c hc hp hn

end PlanarL1.Columns.Model.RetainedSelection

end



section

namespace PlanarL1.Columns.Model.SecondaryGeometry.Group
open MeasureTheory Parameters
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {A : Ambient M} {S : BState M kappaB lam Ω μ}
variable (G : SecondaryGeometry.Group A S)

lemma seed_domain (positive : Bool) (C : G.Component)
    (x : M.Point (BandTrees.band narrow G.lower) (G.root C))
    (hx : x ∈ G.admittedSeeds positive C) :
    x.height ∈ SecondaryCell.domain (G.admittedSeeds positive C) R x.column := by
  apply (SecondaryCell.mem_domain _ _).mpr
  exact ⟨x,rfl,rfl,by rw [SecondaryCell.seedDistance_seed _ hx]; norm_num [R]⟩

lemma seed_cellPoint (positive : Bool) (C : G.Component)
    (x : M.Point (BandTrees.band narrow G.lower) (G.root C))
    (hx : x ∈ G.admittedSeeds positive C) :
    SecondaryCell.point (G.admittedSeeds positive C) R x.column x.height (G.seed_domain positive C x hx)=x := by
  have hc := SecondaryCell.point_column (G.admittedSeeds positive C) R (G.seed_domain positive C x hx)
  have ht := SecondaryCell.point_height (G.admittedSeeds positive C) R (G.seed_domain positive C x hx)
  generalize SecondaryCell.point (G.admittedSeeds positive C) R x.column x.height
    (G.seed_domain positive C x hx) = y at hc ht ⊢
  cases x
  cases y
  cases hc
  cases ht
  rfl

lemma step_gain (positive : Bool) (C : G.Component)
    (hC : (G.admittedSeeds positive C).Nonempty)
    (noise : Point.RadialTree.Noise (n := k+1)) (hnoise : (G.tree C).NoiseBounds noise)
    (alpha beta : ℝ) (ha : alpha ≤ EB) (hb : beta ≤ EB) (ha0 : 0 ≤ alpha) (hb0 : 0 ≤ beta)
    (x : M.Point (BandTrees.band narrow G.lower) (G.root C))
    (hx : x ∈ G.admittedSeeds positive C)
    (hl : G.lower+9*a₂/100 ≤ x.height) (hu : x.height ≤ G.lower+a₂-9*a₂/100) :
    G.old positive C x+R/25 < (G.step positive C hC noise hnoise alpha beta ha hb).replacement x := by
  let U := G.step positive C hC noise hnoise alpha beta ha hb
  apply SecondaryCell.replacement_seed U.tree U.seeds U.old U.supportValue U.data.isOrdinary
    U.zeta_eq (show 0 < R by norm_num [R]) U.radius_small ha0 hb0 U.delta_eq U.noise_bounds hx
    (U.seed_near x hx) _ hl hu
  intro ho
  exact (G.support_seed_near positive C ho x (Finset.mem_filter.mp hx).1).trans (show 10*g ≤ (10/1000000:ℝ)*R by norm_num [g,R])

lemma full_step_gain (positive : Bool) (C : G.Component)
    (hC : (G.admittedSeeds positive C).Nonempty)
    (noise : Point.RadialTree.Noise (n := k+1)) (hnoise : (G.tree C).NoiseBounds noise)
    (alpha beta : ℝ) (ha : alpha ≤ EB) (hb : beta ≤ EB) (ha0 : 0 ≤ alpha) (hb0 : 0 ≤ beta)
    (x : M.Point (BandTrees.band narrow G.lower) (G.root C))
    (hx : x ∈ G.admittedSeeds positive C)
    (hl : G.lower+9*a₂/100 ≤ x.height) (hu : x.height ≤ G.lower+a₂-9*a₂/100) :
    G.old positive C x+R/25 < (G.step positive C hC noise hnoise alpha beta ha hb).fullReplacement
      x.column ⟨x.height,G.sub_old (G.narrow_sub x.inBand)⟩ := by
  let U := G.step positive C hC noise hnoise alpha beta ha hb
  change G.old positive C x+R/25 < U.fullReplacement x.column
    ⟨x.height,G.sub_old (G.narrow_sub x.inBand)⟩
  rw [U.fullReplacement_inside x.column ⟨x.height,G.sub_old (G.narrow_sub x.inBand)⟩
    (show x.height ∈ SecondaryCell.domain U.seeds U.radius x.column from G.seed_domain positive C x hx)]
  change G.old positive C x+R/25 < U.replacement
    (SecondaryCell.point (G.admittedSeeds positive C) R x.column x.height (G.seed_domain positive C x hx))
  have he := G.seed_cellPoint positive C x hx
  rw [he]
  exact G.step_gain positive C hC noise hnoise alpha beta ha hb ha0 hb0 x hx hl hu

end PlanarL1.Columns.Model.SecondaryGeometry.Group

end



section

namespace PlanarL1.Columns.Model.SecondaryGeometry.Group
open Parameters MeasureTheory
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {A : Ambient M} {S : BState M kappaB (⟨lambda,by norm_num [lambda,R]⟩) Ω μ}
variable (G : SecondaryGeometry.Group A S)

lemma domain_near (positive : Bool) (C : G.Component)
    (hC : (G.admittedSeeds positive C).Nonempty) (i : Fin (k+1)) (H : ℝ)
    (hx : H ∈ SecondaryCell.domain (G.admittedSeeds positive C) R i) :
    H ∈ BandTrees.band narrow G.lower ∧ ∃ v ∈ G.seeds,
      ∃ p : M.Path (BandTrees.band narrow G.lower) i v.column, p.length H v.height ≤ R := by
  obtain ⟨x,hi,hH,hd⟩ := (SecondaryCell.mem_domain _ _).mp hx
  obtain ⟨w,hw,he⟩ := SecondaryCell.seedDistance_attained _ hC x
  obtain ⟨v,hv,hc,hvH⟩ := (G.allSeeds_description C w).mp (Finset.mem_filter.mp hw).1
  obtain ⟨p,_,hp⟩ := x.exists_shortest isClosed_Icc w
  refine ⟨hH ▸ x.inBand,v,hv,?_⟩
  have hh := hp.le.trans (he.symm.le.trans hd)
  refine ⟨p.cast hi hc.symm,?_⟩
  calc
    _ = p.length H v.height := PlanarL1.Columns.Model.Path.length_cast p hi hc.symm H v.height
    _ ≤ R := by simpa only [←hH,hvH] using hh

end PlanarL1.Columns.Model.SecondaryGeometry.Group

end



section

namespace PlanarL1.Columns.Model.RetainedSelection
open Parameters MeasureTheory
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [Fintype V] [MeasurableSpace Ω] [MeasurableSpace Ξ]
variable {μ : Measure Ω} {ν : Measure Ξ}
variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)
variable (SB : BState M kappaB SecondaryGeometry.Group.lam Ξ ν)
variable (v : V → M.Point Set.univ A.root)
variable {L U : ℝ} (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q p : ℝ} {phaseD phaseG : MainFamily.BandComponent (M := M) q L U → ℝ}
variable (b : Block (M := M) q p L U)
variable (c : M.Point (BandTrees.band broad b.lower) (BandTrees.root M broad b.lower b.1.2))

lemma domain_touch (i : GroupIndex A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG))
    (positive : Bool) (C : (group A SA SB v hv i).Component)
    (hC : ((group A SA SB v hv i).admittedSeeds positive C).Nonempty)
    (hd : c.height ∈ SecondaryCell.domain ((group A SA SB v hv i).admittedSeeds positive C) R c.column) :
    Touch A SA SB v hv b c i := by
  obtain ⟨hH,z,hz,path,hpath⟩ := (group A SA SB v hv i).domain_near positive C hC c.column c.height hd
  obtain ⟨w,hw,he⟩ := (SurvivingGroups.seed_mem
    (localSeeds A SA SB v hv (phaseD := phaseD) (phaseG := phaseG) i.1) i.2).mp hz
  subst z
  refine ⟨hH,w,hw,path,hpath.trans ?_⟩
  norm_num [R]

end PlanarL1.Columns.Model.RetainedSelection

end



section

namespace PlanarL1.Columns.Model.SecondaryGeometry.Group
open Parameters MeasureTheory
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {A : Ambient M} {S : BState M kappaB lam Ω μ}
variable (G : SecondaryGeometry.Group A S)

/-- A whole secondary group, not only the selected narrow component, stays
away from the other endpoint of a distance-scale pair. -/
lemma far_not_domain (x : M.Point G.broad G.broad_root) (hx : x ∈ G.seeds)
    (j : Fin (k+1)) (T : ℝ) (hfar : 1 ≤ dist (A.point x.column x.height) (A.point j T))
    (positive : Bool) (C : G.Component) (hC : (G.admittedSeeds positive C).Nonempty) :
    T ∉ SecondaryCell.domain (G.admittedSeeds positive C) R j := by
  intro hy
  obtain ⟨y,hj,hT,hd⟩ := (SecondaryCell.mem_domain _ _).mp hy
  obtain ⟨w,hw,he⟩ := SecondaryCell.seedDistance_attained _ hC y
  obtain ⟨v,hv,hc,hH⟩ := (G.allSeeds_description C w).mp (Finset.mem_filter.mp hw).1
  have hvw : A.point v.column v.height=A.point w.column w.height := by rw [hc,hH]
  have h₁ := (MainFamily.ambient_dist_le A x v).trans (G.diameter x hx v hv)
  have h₂ := MainFamily.ambient_dist_le A w y
  rw [dist_comm w y,← he] at h₂
  have htri := dist_triangle (A.point x.column x.height) (A.point v.column v.height) (A.point j T)
  rw [hvw] at h₁
  rw [hvw,←hj,←hT] at htri
  have hsmall : 10*g+R < (1:ℝ) := by norm_num [g,R]
  rw [←hj,←hT] at hfar
  linarith

end PlanarL1.Columns.Model.SecondaryGeometry.Group

end



section

namespace PlanarL1.Interpolation
lemma maxSelection_ge_member {X : Type*} (old : X → NamedValue)
    (Fs : List (X → NamedValue)) (F : X → NamedValue) (hF : F ∈ Fs) (x : X) :
    (F x).value ≤ (maxSelection old Fs x).value := by
  induction Fs with
  | nil => simp at hF
  | cons G gs ih =>
    rw [maxSelection,maxNamed_value]
    rcases List.mem_cons.mp hF with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)
lemma familySelection_ge {X : Type*} {n : ℕ} (old : X → ℝ)
    (F : Fin n → X → NamedValue) (q : Fin n) (x : X) :
    (F q x).value ≤ (familySelection old F x).value :=
  maxSelection_ge_member (fun x => ⟨0,old x⟩)
    (List.ofFn (fun q => fun x => ⟨familyName q (F q x).name,(F q x).value⟩))
    (fun x => ⟨familyName q (F q x).name,(F q x).value⟩)
    (List.mem_ofFn.mpr ⟨q,rfl⟩) x
end PlanarL1.Interpolation

namespace PlanarL1.Columns.Model.BState.SecondaryBatch
open MeasureTheory
open scoped NNReal
open PlanarL1.Interpolation
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {κ : ℝ} {lam : ℝ≥0}
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {S : BState M κ lam Ω μ}
variable (B : SecondaryBatch S)

lemma selected_ge (q : Fin B.count) (i : Fin (k+1)) (H : B.data.band) :
    κ*(B.step q).fullReplacement i (B.groupHeight q H) ≤ (B.selected i H).value := by
  rw [←B.groupNamed_value]
  exact familySelection_ge (fun H => κ*B.comparison.value i H) (fun q => B.groupNamed q i) q H

lemma indicator_inside (w : Ω × Bool) (i : Fin (k+1)) (H : ℝ) (h : H ∈ B.domain i) :
    (B.patch.apply.activity w).indicator i H=
      Threshold.chartValue H (B.converted i H) ((S.labels B.index).lift.value w) := by
  simp only [Activity.indicator,B.patch.inside h w]
  rfl

lemma indicator_outside (w : Ω × Bool) (j : Fin (k+1)) (T : ℝ)
    (hT : T ∈ B.data.band) (hy : T ∉ B.domain j) (hn : S.name j T=B.index) :
    (B.patch.apply.activity w).indicator j T=
      Threshold.chartValue T (κ*(B.data.offset+B.data.orientation B.positive*
        B.comparison.value j ⟨T,hT⟩)) ((S.labels B.index).lift.value w) := by
  have hr := S.represents_named w.1 j T B.index hn hT
  have he := B.data.comparison_convert lam B.lambda_bound B.positive j ⟨T,hT⟩
  change (S.sets.activity w.1).active j T ↔
    Threshold.active (S.labels B.index) T (κ*B.data.value lam j ⟨T,hT⟩) w.1 at hr
  rw [he] at hr
  have hp := B.patch.unchanged hy w
  simp only [Activity.indicator,Threshold.chartValue,Threshold.half,Threshold.active] at *
  exact if_congr (hp.trans hr) rfl rfl

lemma pair_separation_external (i j : Fin (k+1)) (H T : ℝ)
    (hx : H ∈ B.domain i) (hT : T ∈ B.data.band) (hy : T ∉ B.domain j)
    (hn : S.name j T=B.index) :
    B.patch.apply.separation i H j T=max |H-T|
      |(B.selected i ⟨H,B.domain_band hx⟩).value-κ*B.comparison.value j ⟨T,hT⟩| := by
  unfold SetSystem.separation
  simp_rw [B.indicator_inside _ i H hx,B.indicator_outside _ j T hT hy hn]
  rw [(S.labels B.index).lift.distance,B.converted_on i H (B.domain_band hx)]
  congr 1
  rw [show κ*B.data.offset+B.data.orientation B.positive*(B.selected i ⟨H,B.domain_band hx⟩).value-
      κ*(B.data.offset+B.data.orientation B.positive*B.comparison.value j ⟨T,hT⟩)=
      B.data.orientation B.positive*((B.selected i ⟨H,B.domain_band hx⟩).value-
        κ*B.comparison.value j ⟨T,hT⟩) by ring,
    abs_mul,B.data.orientation_unit,one_mul]

/-- Overlapping proposals at the raised endpoint can only help. It is enough
for the other endpoint to stay outside all acting domains of its identifier. -/
lemma gain_external (q : Fin B.count) (i j : Fin (k+1)) (H T : ℝ)
    (hx : H ∈ SecondaryCell.domain (B.step q).seeds (B.step q).radius i)
    (hT : T ∈ B.data.band) (hy : T ∉ B.domain j) (hn : S.name j T=B.index)
    {r : ℝ} (hr : 0 < r) (hk : 0 < κ)
    (hclose : |B.comparison.value i ⟨H,B.domain_band (B.mem_domain.mpr ⟨q,hx⟩)⟩-
      B.comparison.value j ⟨T,hT⟩| ≤ r/10000)
    (hgain : (B.step q).comparison.value i
        (B.groupHeight q ⟨H,B.domain_band (B.mem_domain.mpr ⟨q,hx⟩)⟩)+r/25 <
      (B.step q).fullReplacement i
        (B.groupHeight q ⟨H,B.domain_band (B.mem_domain.mpr ⟨q,hx⟩)⟩)) :
    κ*r/50 < B.patch.apply.separation i H j T := by
  rw [B.pair_separation_external i j H T (B.mem_domain.mpr ⟨q,hx⟩) hT hy hn]
  apply lt_of_lt_of_le _ (le_max_right _ _)
  have hs := B.selected_ge q i ⟨H,B.domain_band (B.mem_domain.mpr ⟨q,hx⟩)⟩
  rw [B.step_comparison] at hgain
  have hg := mul_lt_mul_of_pos_left hgain hk
  have hc := mul_le_mul_of_nonneg_left (abs_le.mp hclose).1 hk.le
  have ha := le_abs_self ((B.selected i ⟨H,B.domain_band (B.mem_domain.mpr ⟨q,hx⟩)⟩).value-
    κ*B.comparison.value j ⟨T,hT⟩)
  nlinarith [mul_pos hk hr]
end PlanarL1.Columns.Model.BState.SecondaryBatch

end



section

namespace PlanarL1.Columns.Model.BState.SecondaryLayer
open MeasureTheory
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {κ : ℝ} {lam : ℝ≥0}
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {S : BState M κ lam Ω μ}
variable (L : SecondaryLayer S)

lemma inside (a : Fin (S.count+1)) (w : Ω × Bool) (i : Fin (k+1)) (H : ℝ)
    (hi : H ∈ (L.batch a).domain i) :
    (L.sets.activity w).active i H ↔ ((L.batch a).patch.apply.activity w).active i H :=
  SetPatch.batch_inside _ L.overlap (List.mem_ofFn.mpr ⟨a,rfl⟩) w i H hi

lemma outside (a : Fin (S.count+1)) (w : Ω × Bool) (i : Fin (k+1)) (H : ℝ)
    (hi : H ∉ (L.batch a).domain i) (hn : S.name i H=a) :
    (L.sets.activity w).active i H ↔ ((L.batch a).patch.apply.activity w).active i H := by
  apply Iff.trans _ ((L.batch a).patch.unchanged hi w).symm
  apply SetPatch.batch_old _ L.overlap w i H
  intro P hP
  obtain ⟨q,rfl⟩ := List.mem_ofFn.mp hP
  apply (L.batch q).patch.unchanged _ w
  intro hq
  have he := (L.batch q).domain_name hq
  rw [L.same_index,hn] at he
  exact hi (he ▸ hq)

lemma pair_external (a : Fin (S.count+1)) (i j : Fin (k+1)) (H T : ℝ)
    (hx : H ∈ (L.batch a).domain i) (hy : T ∉ (L.batch a).domain j)
    (hn : S.name j T=a) :
    L.sets.separation i H j T=(L.batch a).patch.apply.separation i H j T := by
  unfold SetSystem.separation
  congr 1
  funext w
  simp only [Activity.indicator,L.inside a w i H hx,L.outside a w j T hy hn]

end PlanarL1.Columns.Model.BState.SecondaryLayer

end



section

namespace PlanarL1.Columns.Model.SecondaryGeometry
open Parameters MeasureTheory
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {A : Ambient M} {S : BState M kappaB Group.lam Ω μ}
variable {I : Type*} [Fintype I] (G : I → Group A S)
variable {m : ℕ} (hm : 0 < m) (omega : Sample G m)

omit [Fintype I] in
lemma actingStep_gain (a : Fin (S.count+1)) (q : Acting G omega a)
    (x : M.Point (BandTrees.band narrow (G q.val.1).lower) ((G q.val.1).root q.val.2))
    (hx : x ∈ (G q.val.1).admittedSeeds (omega.1 a) q.val.2)
    (hl : (G q.val.1).lower+9*a₂/100 ≤ x.height)
    (hu : x.height ≤ (G q.val.1).lower+a₂-9*a₂/100) :
    (actingStep G hm omega a q).comparison.value x.column
      ⟨x.height,(G q.val.1).sub_old ((G q.val.1).narrow_sub x.inBand)⟩+R/25 <
      (actingStep G hm omega a q).fullReplacement x.column
        ⟨x.height,(G q.val.1).sub_old ((G q.val.1).narrow_sub x.inBand)⟩ := by
  exact (G q.val.1).full_step_gain (omega.1 a) q.val.2 q.property.2.2 _ _ _ _ _ _
    (mul_nonneg (div_nonneg interpolationB.1.le (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
    (mul_nonneg (div_nonneg interpolationB.1.le (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) x hx hl hu

lemma gain_external (a : Fin (S.count+1)) (q : Acting G omega a)
    (x : M.Point (BandTrees.band narrow (G q.val.1).lower) ((G q.val.1).root q.val.2))
    (hx : x ∈ (G q.val.1).admittedSeeds (omega.1 a) q.val.2)
    (hl : (G q.val.1).lower+9*a₂/100 ≤ x.height)
    (hu : x.height ≤ (G q.val.1).lower+a₂-9*a₂/100)
    (j : Fin (k+1)) (T : ℝ) (hT : T ∈ (S.chart a).band)
    (hy : T ∉ (batch G hm omega a).domain j) (hn : S.name j T=a)
    (hclose : ∀ hH : x.height ∈ (S.chart a).band,
      |((S.chart a).comparison Group.lam Group.lam_bound (omega.1 a)).value x.column ⟨x.height,hH⟩-
       ((S.chart a).comparison Group.lam Group.lam_bound (omega.1 a)).value j ⟨T,hT⟩| ≤ R/10000) :
    kappaB*R/50 < (layer G hm omega).sets.separation x.column x.height j T := by
  let e := @Fintype.equivFin (Acting G omega a) (instFintypeActing G omega a)
  have hd : x.height ∈ SecondaryCell.domain ((batch G hm omega a).step (e q)).seeds
      ((batch G hm omega a).step (e q)).radius x.column := by
    change x.height ∈ SecondaryCell.domain
      (G (e.symm (e q)).val.1 |>.admittedSeeds (omega.1 a) (e.symm (e q)).val.2) R x.column
    rw [e.symm_apply_apply]
    exact (G q.val.1).seed_domain (omega.1 a) q.val.2 x hx
  have hdom := (batch G hm omega a).mem_domain.mpr ⟨e q,hd⟩
  rw [(layer G hm omega).pair_external a x.column j x.height T hdom hy hn]
  apply (batch G hm omega a).gain_external (e q) x.column j x.height T hd hT hy hn
    (by norm_num [R]) (by norm_num [kappaB,a₂]) (hclose _) 
  have gain (q' : Acting G omega a) (he : q'=q)
      (H : (actingStep G hm omega a q').data.band) (hH : H.val=x.height) :
      (actingStep G hm omega a q').comparison.value x.column H+R/25 <
        (actingStep G hm omega a q').fullReplacement x.column H := by
    subst q'
    obtain ⟨T,hT⟩ := H
    dsimp only at hH
    subst T
    exact actingStep_gain G hm omega a q x hx hl hu
  exact gain (e.symm (e q)) (e.symm_apply_apply q) _ rfl

end PlanarL1.Columns.Model.SecondaryGeometry

end



section

namespace PlanarL1.Columns.Model.RetainedSelection
open Parameters MeasureTheory SecondaryGeometry
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [Fintype V] [MeasurableSpace Ω] [MeasurableSpace Ξ]
variable {μ : Measure Ω} {ν : Measure Ξ}
variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)
variable (SB : BState M kappaB Group.lam Ξ ν)
variable (v : V → M.Point Set.univ A.root)
variable {L U : ℝ} (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q p : ℝ} {phaseD phaseG : MainFamily.BandComponent (M := M) q L U → ℝ}
variable (b : Block (M := M) q p L U)
variable (c : M.Point (BandTrees.band broad b.lower) (BandTrees.root M broad b.lower b.1.2))
variable (i : GroupIndex A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG))
variable (x : M.Point (group A SA SB v hv i).broad (group A SA SB v hv i).broad_root)
variable (hx : x ∈ (group A SA SB v hv i).seeds)
variable (hfar : 1≤dist (A.point x.column x.height) (A.point c.column c.height))
variable {m : ℕ} (hm : 0 < m)
variable (omega : Sample (group A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG)) m)

include hx hfar in
lemma batch_not_domain (a : Fin (SB.count+1))
    (hs : ∀ j, Touch A SA SB v hv b c j → j≠i → omega.2.1 j=false) :
    c.height ∉ (batch (group A SA SB v hv) hm omega a).domain c.column := by
  intro h
  obtain ⟨n,hn⟩ := (batch (group A SA SB v hv) hm omega a).mem_domain.mp h
  let e := @Fintype.equivFin (Acting (group A SA SB v hv) omega a)
    (instFintypeActing (group A SA SB v hv) omega a)
  let z := e.symm n
  change c.height ∈ SecondaryCell.domain
    ((group A SA SB v hv (e.symm n).val.1).admittedSeeds (omega.1 a) (e.symm n).val.2) R c.column at hn
  change c.height ∈ SecondaryCell.domain
    ((group A SA SB v hv z.val.1).admittedSeeds (omega.1 a) z.val.2) R c.column at hn
  by_cases hz : z.val.1=i
  · have haway (j : GroupIndex A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG))
        (hj : j=i) (C : (group A SA SB v hv j).Component)
        (hC : ((group A SA SB v hv j).admittedSeeds (omega.1 a) C).Nonempty) :
        c.height ∉ SecondaryCell.domain ((group A SA SB v hv j).admittedSeeds (omega.1 a) C) R c.column := by
      subst j
      exact (group A SA SB v hv i).far_not_domain x hx c.column c.height hfar (omega.1 a) C hC
    exact haway z.val.1 hz z.val.2 z.property.2.2 hn
  · have ht := domain_touch A SA SB v hv b c z.val.1 (omega.1 a) z.val.2 z.property.2.2 hn
    have hf := hs z.val.1 ht hz
    have hk := z.property.2.1
    change omega.2.1 z.val.1=true at hk
    rw [hf] at hk
    contradiction
end PlanarL1.Columns.Model.RetainedSelection

end



section

namespace PlanarL1.FiniteRandom
attribute [local instance] Classical.propDecidable

lemma prob_mono_instances {Ω : Type*} (F F' : Fintype Ω) {P Q : Ω → Prop}
    (h : ∀ w, P w → Q w) : @prob Ω F P ≤ @prob Ω F' Q := by
  cases Subsingleton.elim F' F
  exact @prob_mono Ω F P Q h

lemma prob_true {Ω : Type*} [Fintype Ω] [Nonempty Ω] : prob (fun _ : Ω => True)=1 := by
  simp [prob,event]

lemma prob_first {Ω Λ : Type*} [Fintype Ω] [Fintype Λ] [Nonempty Λ]
    (P : Ω → Prop) : prob (fun z : Ω × Λ => P z.1)=prob P := by
  rw [←prob_equiv (Equiv.prodComm Λ Ω)]
  exact prob_second P

lemma prob_rectangle {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
    (P : Ω → Prop) (Q : Λ → Prop) :
    prob (fun z : Ω × Λ => P z.1 ∧ Q z.2)=prob P*prob Q := by
  rw [prob_prod]
  have he (w : Ω) : prob (fun z : Λ => P w ∧ Q z)=(if P w then (1:ℝ) else 0)*prob Q := by
    by_cases h : P w
    · simp only [h,true_and,ite_true,one_mul]
    · simp only [h,false_and,ite_false,zero_mul,prob_false]
  simp_rw [he]
  rw [←Finset.sum_mul,prob_eq_sum P]
  ring

lemma prob_coin {I : Type*} [Fintype I] (i : I) (b : Bool) :
    prob (fun f : I → Bool => f i=b)=1/2 := by
  simpa using prob_prescribed ({i} : Finset I) (fun _ => b)

lemma prob_keep_outside {I : Type*} [Fintype I] (i : I) (T : Finset I) {N : ℕ}
    (hT : T.card≤N) :
    1/(2:ℝ)^(N+1) ≤ prob (fun f : I → Bool => f i=true ∧ ∀ j ∈ T, j≠i → f j=false) := by
  apply prob_at_least_prescription (insert i T) (fun j => if j=i then true else false)
  · exact (Finset.card_insert_le _ _).trans (by omega)
  · intro f hf
    refine ⟨?_,?_⟩
    · simpa using hf i (Finset.mem_insert_self _ _)
    · intro j hj hji
      simpa [hji] using hf j (Finset.mem_insert_of_mem hj)
end PlanarL1.FiniteRandom

namespace PlanarL1.Columns.Model.SecondaryGeometry
open Parameters MeasureTheory FiniteRandom
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {A : Ambient M} {S : BState M kappaB (⟨lambda,by norm_num [lambda,R]⟩) Ω μ}
variable {I : Type*} [Fintype I] (G : I → Group A S) (m : ℕ)

lemma prob_orientation_coins (P : (Fin (S.count+1) → Bool) → Prop) (Q : (I → Bool) → Prop) :
    prob (fun omega : Sample G m => P omega.1 ∧ Q omega.2.1)=prob P*prob Q := by
  let e := (Equiv.prodAssoc (Fin (S.count+1) → Bool) (I → Bool)
    (∀ i C, ComponentSample G i C m)).symm
  rw [←prob_equiv e.symm]
  calc
    _ = prob (fun z : (Fin (S.count+1) → Bool) × (I → Bool) => P z.1 ∧ Q z.2) :=
      prob_first _
    _ = _ := prob_rectangle P Q

lemma prob_orient_keep_suppress (a : Fin (S.count+1)) (positive : Bool) (i : I)
    (T : Finset I) {N : ℕ} (hT : T.card≤N) :
    1/(2:ℝ)^(N+2) ≤ prob (fun omega : Sample G m =>
      omega.1 a=positive ∧ omega.2.1 i=true ∧ ∀ j ∈ T, j≠i → omega.2.1 j=false) := by
  rw [prob_orientation_coins G m (fun f => f a=positive) (fun f => f i=true ∧ ∀ j ∈ T, j≠i → f j=false)]
  have hc : prob (fun f : Fin (S.count+1) → Bool => f a=positive)=(1/2:ℝ) := by
    convert prob_coin a positive using 1
    exact congrArg (fun F : Fintype (Fin (S.count+1) → Bool) =>
      @prob _ F (fun f => f a=positive)) (Subsingleton.elim _ _)
  have h := prob_keep_outside i T hT
  calc
    _ = (1/2:ℝ)*(1/2^(N+1)) := by rw [show N+2=(N+1)+1 by omega,pow_succ]; ring
    _ ≤ (1/2:ℝ)*prob (fun f : I → Bool => f i=true ∧ ∀ j ∈ T, j≠i → f j=false) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ = _ := congrArg (fun t => t*prob (fun f : I → Bool => f i=true ∧ ∀ j ∈ T, j≠i → f j=false)) hc.symm
end PlanarL1.Columns.Model.SecondaryGeometry

end

end OAI
