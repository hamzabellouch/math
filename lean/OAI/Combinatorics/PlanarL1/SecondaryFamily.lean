import OAI.Combinatorics.PlanarL1.MainFamily
import OAI.Combinatorics.PlanarL1.SecondaryBatch

namespace OAI


section

namespace PlanarL1.Columns.Model
open MeasureTheory Parameters
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)}

namespace BData
/-- A proved ordered support at the actual representative of a group.
The support is needed only in an ordinary chart; ordered charts use their
literal sphere admission test instead. -/
lemma support_at (D : BData M) (lam : ℝ≥0) (hlam : lam≤(1:ℝ≥0)/100)
    (positive : Bool) (i : Fin (k+1)) (H : ℝ) (hi : H ∈ D.band) (hu : D.Uses i) :
    ∃ (F : M.Field D.band 1) (a b : Fin (k+1)), F.OrderedFrom a b ∧
      (D.isOrdinary=true → F.value i ⟨H,hi⟩=(D.comparison lam hlam positive).value i ⟨H,hi⟩) ∧
      ∀ (j : Fin (k+1)) (T : D.band), D.isOrdinary=true → D.Uses j →
        F.value j T≤(D.comparison lam hlam positive).value j T := by
  cases D with
  | ordinary C =>
    obtain ⟨F,a,b,ho,he,hF⟩ := C.support_at i H ⟨hi,hu⟩
    refine ⟨F,a,b,ho,fun _ => he,?_⟩
    intro j T _ hj
    exact hF j T.val ⟨T.property,hj⟩
  | ordered C =>
    exact ⟨Field.constant M C.band 0,0,0,Field.constant_ordered 0 0 0,
      by simp [isOrdinary],by simp [isOrdinary]⟩

lemma uses_reachable (D : BData M) {i j : Fin (k+1)} (hi : D.Uses i)
    (hr : (M.activeGraph D.band).Reachable i j) : D.Uses j := by
  cases D with
  | ordered _ => trivial
  | ordinary C => exact fun r o ho => (hi r o ho).trans hr
end BData

namespace SecondaryGeometry
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable (A : Ambient M) (S : BState M kappaB (⟨lambda,by norm_num [lambda,R]⟩) Ω μ)

/-- The geometric information attached to one actual surviving g-cell group.
The seed collection is finite, lies in one broad component and one narrow
height band, and keeps its TWO chart identifiers through the surviving-pair
selection. The B half needed for its literal update is recorded here. -/
structure Group where
  index : Fin (S.count+1)
  broad : Set ℝ
  broad_root : Fin (k+1)
  broad_closed : IsClosed broad
  lower : ℝ
  narrow_sub : BandTrees.band narrow lower ⊆ broad
  sub_old : broad ⊆ (S.chart index).band
  seeds : Finset (M.Point broad broad_root)
  nonempty : seeds.Nonempty
  height : ∀ w ∈ seeds, w.height ∈ BandTrees.band narrow lower
  diameter : ∀ w ∈ seeds, ∀ v ∈ seeds, dist w v≤10*g
  common : ∀ w ∈ seeds, A.Common S.name (A.point w.column w.height) 5 index

namespace Group
variable {A S} (G : Group A S)
noncomputable def representative : M.Point G.broad G.broad_root := G.nonempty.choose
lemma representative_mem : G.representative ∈ G.seeds := G.nonempty.choose_spec
noncomputable abbrev data : BData M := S.chart G.index
noncomputable def lam : ℝ≥0 := ⟨lambda,by norm_num [lambda,R]⟩
lemma lam_bound : lam≤(1:ℝ≥0)/100 := by
  change lambda≤(1:ℝ)/100
  norm_num [lambda,R]
noncomputable def comparison (positive : Bool) : M.Field G.data.band 5 :=
  G.data.comparison lam lam_bound positive
noncomputable def value (positive : Bool) (x : M.Point G.broad G.broad_root) : ℝ :=
  (G.comparison positive).value x.column ⟨x.height,G.sub_old x.inBand⟩
noncomputable def pc (positive : Bool) : ℝ := G.value positive G.representative

lemma representative_uses : G.data.Uses G.representative.column := by
  apply S.uses_named _ G.representative.height G.index
  exact (G.common G.representative G.representative_mem).center A (by norm_num)

lemma value_lipschitz (positive : Bool) : LipschitzWith 5 (G.value positive) :=
  ((G.comparison positive).restrict G.sub_old).lipschitz G.broad_closed G.broad_root

lemma value_near (positive : Bool) (w : M.Point G.broad G.broad_root) (hw : w ∈ G.seeds) :
    |G.value positive w-G.pc positive|≤50*g := by
  have h := (G.value_lipschitz positive).dist_le_mul w G.representative
  rw [Real.dist_eq] at h
  have hd := G.diameter w hw G.representative G.representative_mem
  change |G.value positive w-G.pc positive|≤5*dist w G.representative at h
  linarith

abbrev Component := BandTrees.Component M narrow G.lower
noncomputable abbrev root (C : G.Component) := BandTrees.root M narrow G.lower C
noncomputable abbrev tree (C : G.Component) := BandTrees.tree M narrow G.lower C

noncomputable def inComponent (C : G.Component) : Finset (M.Point G.broad G.broad_root) :=
  G.seeds.filter (fun w => w.column ∈ C.supp)

noncomputable def narrowPoint (C : G.Component) (w : G.inComponent C) :
    M.Point (BandTrees.band narrow G.lower) (G.root C) :=
  ⟨w.val.column,w.val.height,G.height w.val (Finset.mem_filter.mp w.property).1,
    C.reachable_of_mem_supp (BandTrees.root_mem M narrow G.lower C) (Finset.mem_filter.mp w.property).2⟩

noncomputable def allSeeds (C : G.Component) : Finset (M.Point (BandTrees.band narrow G.lower) (G.root C)) :=
  (G.inComponent C).attach.image (G.narrowPoint C)

lemma allSeeds_description (C : G.Component) (x : M.Point (BandTrees.band narrow G.lower) (G.root C)) :
    x ∈ G.allSeeds C ↔ ∃ w ∈ G.seeds, w.column=x.column ∧ w.height=x.height := by
  constructor
  · intro hx
    obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hx
    exact ⟨w.val,(Finset.mem_filter.mp w.property).1,rfl,rfl⟩
  · rintro ⟨w,hw,hc,hH⟩
    have hcol : w.column ∈ C.supp := hc ▸ BandTrees.reachable_mem M narrow G.lower C x.reachable
    let w' : G.inComponent C := ⟨w,Finset.mem_filter.mpr ⟨hw,hcol⟩⟩
    refine Finset.mem_image.mpr ⟨w',Finset.mem_attach _ _,?_⟩
    obtain ⟨xc,xh,xi,xr⟩ := x
    dsimp only at hc hH
    cases hc
    cases hH
    rfl

noncomputable def old (positive : Bool) (C : G.Component)
    (x : M.Point (BandTrees.band narrow G.lower) (G.root C)) : ℝ :=
  (G.comparison positive).value x.column ⟨x.height,G.sub_old (G.narrow_sub x.inBand)⟩

/-- Literal admission; every ordinary seed is kept, and in an ordered chart
this tests all points on the intrinsic narrow-band sphere. -/
def Admitted (positive : Bool) (C : G.Component)
    (w : M.Point (BandTrees.band narrow G.lower) (G.root C)) : Prop :=
  G.data.isOrdinary=true ∨ ∀ x : M.Point (BandTrees.band narrow G.lower) (G.root C),
    dist w x=R → G.pc positive-(65/100:ℝ)*R≤G.old positive C x

noncomputable def admittedSeeds (positive : Bool) (C : G.Component) :=
  (G.allSeeds C).filter (G.Admitted positive C)

lemma admitted_sphere (positive : Bool) (C : G.Component) (hord : G.data.isOrdinary=false)
    (w : M.Point (BandTrees.band narrow G.lower) (G.root C)) (hw : w ∈ G.admittedSeeds positive C) :
    ∀ x : M.Point (BandTrees.band narrow G.lower) (G.root C),
      dist w x=R → G.pc positive-(65/100:ℝ)*R≤G.old positive C x := by
  obtain ⟨_,ha⟩ := Finset.mem_filter.mp hw
  exact ha.resolve_left (by simp [hord])

lemma ordinary_admits (positive : Bool) (C : G.Component) (hord : G.data.isOrdinary=true) :
    G.admittedSeeds positive C=G.allSeeds C := by
  apply Finset.filter_true_of_mem
  intro w _
  exact Or.inl hord

end Group
end SecondaryGeometry
end PlanarL1.Columns.Model

end



section

namespace PlanarL1.Columns.Model.SecondaryGeometry.Group
open MeasureTheory Parameters
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {A : Ambient M} {S : BState M kappaB (⟨lambda,by norm_num [lambda,R]⟩) Ω μ}
variable (G : SecondaryGeometry.Group A S)

structure Support (positive : Bool) where
  field : M.Field G.data.band 1
  lower : Fin (k+1)
  upper : Fin (k+1)
  ordered : field.OrderedFrom lower upper
  at_center : G.data.isOrdinary=true →
    field.value G.representative.column ⟨G.representative.height,G.sub_old G.representative.inBand⟩=G.pc positive
  below : ∀ (i : Fin (k+1)) (H : G.data.band), G.data.isOrdinary=true → G.data.Uses i →
    field.value i H≤(G.comparison positive).value i H

noncomputable def support (positive : Bool) : G.Support positive := by
  apply Classical.choice
  obtain ⟨F,a,b,ho,he,hF⟩ := G.data.support_at lam lam_bound positive
    G.representative.column G.representative.height (G.sub_old G.representative.inBand) G.representative_uses
  exact ⟨⟨F,a,b,ho,he,hF⟩⟩

lemma old_eq (positive : Bool) (C : G.Component) (w : M.Point G.broad G.broad_root)
    (x : M.Point (BandTrees.band narrow G.lower) (G.root C))
    (hc : w.column=x.column) (hH : w.height=x.height) : G.old positive C x=G.value positive w := by
  dsimp only [old,value]
  congr 1
  exacts [hc.symm,Subtype.ext hH.symm]

lemma seed_common (C : G.Component) (x : M.Point (BandTrees.band narrow G.lower) (G.root C))
    (hx : x ∈ G.allSeeds C) : A.Common S.name (A.point x.column x.height) 5 G.index := by
  obtain ⟨w,hw,hc,hH⟩ := (G.allSeeds_description C x).mp hx
  rw [← hc,← hH]
  exact G.common w hw

lemma component_uses (C : G.Component) (hC : (G.allSeeds C).Nonempty)
    (x : M.Point (BandTrees.band narrow G.lower) (G.root C)) : G.data.Uses x.column := by
  obtain ⟨w,hw⟩ := hC
  have hu : G.data.Uses w.column := S.uses_named w.column w.height G.index
    ((G.seed_common C w hw).center A (by norm_num))
  obtain ⟨p,_,_⟩ := w.exists_shortest isClosed_Icc x
  exact G.data.uses_reachable hu (p.widen (G.narrow_sub.trans G.sub_old)).word.reachable

lemma seed_near (positive : Bool) (C : G.Component)
    (x : M.Point (BandTrees.band narrow G.lower) (G.root C)) (hx : x ∈ G.allSeeds C) :
    |G.old positive C x-G.pc positive|≤(60/1000000:ℝ)*R := by
  obtain ⟨w,hw,hc,hH⟩ := (G.allSeeds_description C x).mp hx
  rw [G.old_eq positive C w x hc hH]
  exact (G.value_near positive w hw).trans (by norm_num [g,R])

lemma support_seed_near (positive : Bool) (C : G.Component)
    (ho : G.data.isOrdinary=true)
    (x : M.Point (BandTrees.band narrow G.lower) (G.root C)) (hx : x ∈ G.allSeeds C) :
    |(G.support positive).field.value x.column ⟨x.height,G.sub_old (G.narrow_sub x.inBand)⟩-
      G.pc positive|≤10*g := by
  obtain ⟨w,hw,hc,hH⟩ := (G.allSeeds_description C x).mp hx
  have h := (((G.support positive).field.restrict G.sub_old).lipschitz G.broad_closed
    G.broad_root).dist_le_mul w G.representative
  rw [Real.dist_eq,NNReal.coe_one,one_mul] at h
  change |(G.support positive).field.value w.column ⟨w.height,G.sub_old w.inBand⟩-
    (G.support positive).field.value G.representative.column
      ⟨G.representative.height,G.sub_old G.representative.inBand⟩|≤dist w G.representative at h
  rw [(G.support positive).at_center ho] at h
  have he : (G.support positive).field.value w.column ⟨w.height,G.sub_old w.inBand⟩=
      (G.support positive).field.value x.column ⟨x.height,G.sub_old (G.narrow_sub x.inBand)⟩ := by
    exact congrArg₂ (G.support positive).field.value hc (Subtype.ext hH)
  rw [he] at h
  exact h.trans (G.diameter w hw G.representative G.representative_mem)

lemma domain_name (positive : Bool) (C : G.Component)
    (hC : (G.admittedSeeds positive C).Nonempty) (i : Fin (k+1)) (H : ℝ)
    (hi : H ∈ SecondaryCell.domain (G.admittedSeeds positive C) R i) : S.name i H=G.index := by
  obtain ⟨x,hx,hH,hd⟩ := (SecondaryCell.mem_domain _ _).mp hi
  obtain ⟨w,hw,he⟩ := SecondaryCell.seedDistance_attained _ hC x
  have hc := G.seed_common C w (Finset.mem_filter.mp hw).1
  have hdist : dist (A.point w.column w.height) (A.point i H)≤5 := by
    rw [← hx,← hH]
    have ha := MainFamily.ambient_dist_le A w x
    rw [dist_comm w x,← he] at ha
    exact ha.trans (hd.trans (by norm_num [R]))
  exact hc (A.point i H) hdist

/-- A nonempty admitted component now produces the literal, fully proved
secondary clipping operation. No admission, support, name-gluing or movement
conclusion is added as an assumption of the step. -/
noncomputable def step (positive : Bool) (C : G.Component)
    (hC : (G.admittedSeeds positive C).Nonempty)
    (noise : Point.RadialTree.Noise (n := k+1)) (hn : (G.tree C).NoiseBounds noise)
    (alpha beta : ℝ) (ha : alpha≤EB) (hb : beta≤EB) :
    BState.SecondaryStep S (BandTrees.band narrow G.lower) (G.root C) where
  index := G.index
  positive := positive
  lambda_bound := lam_bound
  tree := G.tree C
  lo := G.lower
  band_eq := rfl
  sub_old := G.narrow_sub.trans G.sub_old
  seeds := G.admittedSeeds positive C
  seeds_nonempty := hC
  pc := G.pc positive
  radius := R
  radius_nonneg := by norm_num [R]
  radius_small := by norm_num [R]
  support := (G.support positive).field
  lower := (G.support positive).lower
  upper := (G.support positive).upper
  support_ordered := (G.support positive).ordered
  support_le := by
    intro ho x
    exact (G.support positive).below x.column _ ho
      (G.component_uses C (hC.mono (Finset.filter_subset _ _)) x)
  admitted := G.admitted_sphere positive C
  seed_near := fun w hw => G.seed_near positive C w (Finset.mem_filter.mp hw).1
  zeta_eq := rfl
  delta_eq := rfl
  noise := noise
  noise_bounds := hn
  ordered_offset := alpha
  shield_offset := beta
  ordered_bound := ha
  shield_bound := hb
  same_name := G.domain_name positive C hC
  kappa_nonneg := verticalB.1
  vertical_bound := verticalB.2.1
  shield_strict := verticalB.2.2.1

end PlanarL1.Columns.Model.SecondaryGeometry.Group

end



section

namespace PlanarL1.Columns.Model.SecondaryGeometry
open MeasureTheory Parameters
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {A : Ambient M} {S : BState M kappaB Group.lam Ω μ}
variable {I : Type*} [Fintype I] (G : I → Group A S)

/-- Offsets are fresh for each narrow component. The keep coin, by contrast,
is shared by all the components of one surviving group. -/
abbrev ComponentSample (i : I) (C : (G i).Component) (m : ℕ) :=
  Point.RadialTree.GridSample (n := k+1) ((G i).tree C).depthCap m × Fin (m+1) × Fin (m+1)
abbrev Sample (m : ℕ) :=
  (Fin (S.count+1) → Bool) × (I → Bool) × (∀ i C, ComponentSample G i C m)
noncomputable instance (m : ℕ) : Fintype (Sample G m) := Fintype.ofFinite _
instance (m : ℕ) : Nonempty (Sample G m) := inferInstanceAs (Nonempty (_ × _ × _))

variable {m : ℕ} (hm : 0 < m) (omega : Sample G m)

def kept (i : I) : Prop := omega.2.1 i=true
abbrev Acting (a : Fin (S.count+1)) :=
  {q : Σ i, (G i).Component // (G q.1).index=a ∧ kept G omega q.1 ∧
    ((G q.1).admittedSeeds (omega.1 a) q.2).Nonempty}
noncomputable instance (a : Fin (S.count+1)) : Fintype (Acting G omega a) := Fintype.ofFinite _

include hm in
lemma offset_bound (t : Fin (m+1)) :
    EB/(m:ℝ)*(t.val:ℝ)≤EB := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have ht : (t.val:ℝ) ≤ m := by exact_mod_cast t.is_le
  calc _ ≤ EB/m*m := mul_le_mul_of_nonneg_left ht (div_nonneg (by norm_num [EB,R]) hmR.le)
       _ = EB := div_mul_cancel₀ _ hmR.ne'

noncomputable def actingStep (a : Fin (S.count+1)) (q : Acting G omega a) :=
  (G q.val.1).step (omega.1 a) q.val.2 q.property.2.2
    (((G q.val.1).tree q.val.2).gridNoise _ m (omega.2.2 q.val.1 q.val.2).1)
    (((G q.val.1).tree q.val.2).gridNoise_bounds _ _ hm (omega.2.2 q.val.1 q.val.2).1)
    (EB/m*(omega.2.2 q.val.1 q.val.2).2.1.val)
    (EB/m*(omega.2.2 q.val.1 q.val.2).2.2.val)
    (offset_bound hm _)
    (offset_bound hm _)

/-- Literal maximum within an old B identifier. Neither disjoint domains nor
an assumed winning branch replaces the actual overlapping maximum. -/
noncomputable def batch (a : Fin (S.count+1)) : BState.SecondaryBatch S where
  index := a
  positive := omega.1 a
  lambda_bound := Group.lam_bound
  count := Fintype.card (Acting G omega a)
  band j := BandTrees.band narrow
    (G ((Fintype.equivFin (Acting G omega a)).symm j).val.1).lower
  root j := (G ((Fintype.equivFin (Acting G omega a)).symm j).val.1).root
    ((Fintype.equivFin (Acting G omega a)).symm j).val.2
  step j := actingStep G hm omega a ((Fintype.equivFin (Acting G omega a)).symm j)
  same_index j := ((Fintype.equivFin (Acting G omega a)).symm j).property.1
  same_positive _ := rfl
  kappa_nonneg := verticalB.1
  kappa_five := verticalB.2.2.2

noncomputable def layer : BState.SecondaryLayer S where
  batch := batch G hm omega
  same_index _ := rfl

noncomputable def result [SFinite μ] :
    BState M kappaB Group.lam (Ω × Bool) (μ.prod Threshold.fair) :=
  (layer G hm omega).apply

/-- Sampling all orientations, group coins, interpolation atoms and branches
is a finite execution determined from the old geometric groups. -/
noncomputable def execution [SFinite μ] :
    Execution (BState M kappaB Group.lam (Ω × Bool) (μ.prod Threshold.fair)) :=
  (Execution.uniform (α := Sample G m)).bind fun omega => .pure (result G hm omega)

end PlanarL1.Columns.Model.SecondaryGeometry

end

end OAI
