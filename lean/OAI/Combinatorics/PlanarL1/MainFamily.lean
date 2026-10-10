import OAI.Combinatorics.PlanarL1.BandTrees
import OAI.Combinatorics.PlanarL1.MainStep

namespace OAI


section

namespace PlanarL1.Columns.Model
open MeasureTheory
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

namespace MainFamily
open Parameters
variable (A : Ambient M) (S : OrdinaryState M kappaA Ω μ)
variable (q L U : ℝ)

noncomputable abbrev BandIndex := Tiling.processed a₁ q L U
noncomputable def lower (b : BandIndex q L U) : ℝ := q+(b.val:ℝ)*a₁
abbrev BandComponent := Σ b : BandIndex q L U, BandTrees.Component M broad (lower q L U b)
noncomputable instance : Fintype (BandComponent (M := M) q L U) := Fintype.ofFinite _

abbrev CellIndex (phase : BandComponent (M := M) q L U → ℝ) :=
  Σ b : BandComponent (M := M) q L U,
    BandTrees.MainIndex M broad (lower q L U b.1) b.2 (phase b)
noncomputable instance (phase : BandComponent (M := M) q L U → ℝ) :
    Fintype (CellIndex q L U phase) := Fintype.ofFinite _

variable {q L U} (phase : BandComponent (M := M) q L U → ℝ)
variable (c : CellIndex q L U phase)
noncomputable abbrev tree := BandTrees.tree M broad (lower q L U c.1.1) c.1.2
noncomputable def radial := phase c.1+(c.2.1.val:ℝ)*(1/1000)
noncomputable abbrev anchor := BandTrees.anchor M broad (lower q L U c.1.1) c.1.2 (phase c.1) c.2
noncomputable def domain (i : Fin (k+1)) : Set ℝ := MainCell.domain (tree phase c) (radial phase c) c.2.2 i

/-- Availability is the manuscript's entire closed radius-one neighborhood of
this full-column cell, not just tests at the finite original vertices. -/
def neighborhood : Set (M.Point Set.univ A.root) :=
  {y | ∃ i H, H ∈ domain phase c i ∧ dist y (A.point i H)≤1}
def Available : Prop := ∃ index : Fin (S.count+1),
  ∀ y ∈ neighborhood A phase c, S.name y.column y.height=index

noncomputable def index (hc : Available A S phase c) : Fin (S.count+1) := hc.choose
lemma same_name (hc : Available A S phase c) (i : Fin (k+1)) (H : ℝ)
    (hi : H ∈ domain phase c i) : S.name i H=index A S phase c hc :=
  hc.choose_spec (A.point i H) ⟨i,H,hi,by simp⟩

lemma sub_old (hc : Available A S phase c) : BandTrees.band broad (lower q L U c.1.1) ⊆
    (S.chart (index A S phase c hc)).band := by
  intro H hH
  have hi : H ∈ domain phase c (anchor phase c).column :=
    (MainCell.mem_domain _ _ _).mpr ⟨BandTrees.anchor_mem _ _ _ _ _ _,hH⟩
  have hh := S.height_in (anchor phase c).column H
  rw [same_name A S phase c hc _ _ hi] at hh
  exact hh

/-- Every kept, available cell becomes an actual MainStep, including its old
chart and exact interpolation tree. All parameters are the fixed constants. -/
noncomputable def step (hc : Available A S phase c)
    (noise : Point.RadialTree.Noise (n := k+1)) (hn : (tree phase c).NoiseBounds noise)
    (beta : ℝ) (hb : beta ≤ EA) :
    OrdinaryState.MainStep S (BandTrees.band broad (lower q L U c.1.1))
      (BandTrees.root M broad (lower q L U c.1.1) c.1.2) where
  index := index A S phase c hc
  tree := tree phase c
  phase := radial phase c
  cell := c.2.2
  anchor := anchor phase c
  anchor_mem := BandTrees.anchor_mem _ _ _ _ _ _
  lo := lower q L U c.1.1
  band_eq := rfl
  thin := thinA
  sub_old := sub_old A S phase c hc
  same_name := same_name A S phase c hc
  noise := noise
  noise_bounds := hn
  error := EA
  error_pos := interpolationA.1
  delta_eq := rfl
  shield_offset := beta
  shield_bound := hb.trans (by norm_num [EA,epsilon])
  kappa_nonneg := verticalA.1
  vertical_bound := verticalA.2.1
  shield_strict := verticalA.2.2

lemma cell_column_component {i : Fin (k+1)} (hi : i ∈ ColumnOrder.componentColumns c.2.2) :
    i ∈ c.1.2.supp :=
  BandTrees.reachable_mem M broad (lower q L U c.1.1) c.1.2
    (ColumnOrder.componentColumns_subset c.2.2 hi).choose

lemma unique_in_band {c d : CellIndex q L U phase} (he : c.1.1=d.1.1)
    {i : Fin (k+1)} {H : ℝ} (hi : H ∈ domain phase c i) (hj : H ∈ domain phase d i) : c=d := by
  obtain ⟨⟨b,C⟩,K⟩ := c
  obtain ⟨⟨b',D⟩,T⟩ := d
  dsimp only at he
  subst b'
  have hci := cell_column_component phase (Sigma.mk ⟨b,C⟩ K) ((MainCell.mem_domain _ _ _).mp hi).1
  have hcj := cell_column_component phase (Sigma.mk ⟨b,D⟩ T) ((MainCell.mem_domain _ _ _).mp hj).1
  have hCD : C=D := ((SimpleGraph.ConnectedComponent.mem_supp_iff C i).mp hci).symm.trans
    ((SimpleGraph.ConnectedComponent.mem_supp_iff D i).mp hcj)
  subst D
  have hKT : K=T := by
    by_contra hn
    exact Set.disjoint_left.mp (BandTrees.main_disjoint M broad (lower q L U b) C (phase ⟨b,C⟩) hn)
      ((MainCell.mem_domain _ _ _).mp hi).1 ((MainCell.mem_domain _ _ _).mp hj).1
  subst T
  rfl

lemma domain_band {i : Fin (k+1)} {H : ℝ} (hi : H ∈ domain phase c i) :
    H ∈ Tiling.band a₁ q c.1.1.val := by
  obtain ⟨_,hl,hu⟩ := (MainCell.mem_domain _ _ _).mp hi
  change q+(c.1.1.val:ℝ)*a₁≤H ∧ H≤q+((c.1.1.val:ℝ)+1)*a₁
  dsimp [BandTrees.band,lower,broad] at hl hu
  constructor <;> linarith

end MainFamily

namespace OrdinaryState.MainStep
variable {κ : ℝ} {S : OrdinaryState M κ Ω μ} {J : Set ℝ} {root : Fin (k+1)}
variable (V : MainStep S J root)
lemma endpoint_old (ω : Ω × Bool) (i : Fin (k+1)) (H : ℝ)
    (hi : H ∈ V.patch.domain i) (he : H=V.lo ∨ H=V.lo+V.tree.a) :
    V.patch.active ω i H ↔ (S.lift.sets.activity ω).active i H := by
  apply V.patch.boundary
  change H ∈ frontier (MainCell.domain V.tree V.phase V.cell i)
  have hc := ((MainCell.mem_domain V.tree V.phase V.cell).mp hi).1
  rw [MainCell.domain,ite_eq_left hc,V.band_eq,frontier_Icc (by linarith [V.tree.width_pos])]
  simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using he
end OrdinaryState.MainStep
end PlanarL1.Columns.Model

end



section

namespace PlanarL1.Columns.Model.MainFamily
open MeasureTheory Parameters
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable (A : Ambient M) (S : OrdinaryState M kappaA Ω μ)
variable {q L U : ℝ} (phase : BandComponent (M := M) q L U → ℝ)

abbrev CellSample (c : CellIndex q L U phase) (m : ℕ) :=
  Point.RadialTree.GridSample (n := k+1) (tree phase c).depthCap m × Fin (m+1) × Bool
abbrev Sample (m : ℕ) := ∀ c : CellIndex q L U phase, CellSample phase c m
noncomputable instance (m : ℕ) : Fintype (Sample phase m) := inferInstanceAs (Fintype (∀ _, _))
instance (m : ℕ) : Nonempty (Sample phase m) := inferInstanceAs (Nonempty (∀ _, _))

variable {m : ℕ} (hm : 0 < m) (omega : Sample phase m)

def kept (c : CellIndex q L U phase) : Prop := Available A S phase c ∧ (omega c).2.2=true
abbrev Kept := {c : CellIndex q L U phase // kept A S phase omega c}
noncomputable instance : Fintype (Kept A S phase omega) := Fintype.ofFinite _

include hm in
lemma shield_bound (c : CellIndex q L U phase) : EA/(m:ℝ)*((omega c).2.1.val:ℝ)≤EA := by
  have hmR : (0:ℝ)< m := by exact_mod_cast hm
  have hi : (((omega c).2.1.val):ℝ)≤ m := by exact_mod_cast (omega c).2.1.is_le
  have hp : 0≤EA/m := div_nonneg (interpolationA.1.le) hmR.le
  calc _ ≤ EA/m*m := mul_le_mul_of_nonneg_left hi hp
       _ = EA := div_mul_cancel₀ _ hmR.ne'

noncomputable def keptStep (c : Kept A S phase omega) :=
  step A S phase c.val c.property.1
    ((tree phase c.val).gridNoise (tree phase c.val).depthCap m (omega c.val).1)
    ((tree phase c.val).gridNoise_bounds _ _ hm (omega c.val).1)
    (EA/m*(omega c.val).2.1.val) (shield_bound phase hm omega c.val)

lemma overlap {c d : Kept A S phase omega} (hne : c≠d) :
    SetPatch.UnchangedOverlap (keptStep A S phase hm omega c).patch
      (keptStep A S phase hm omega d).patch := by
  intro w i H hi hj
  have hi' : H ∈ domain phase c.val i := hi
  have hj' : H ∈ domain phase d.val i := hj
  have hbands : c.val.1.1≠d.val.1.1 := by
    intro he
    exact hne (Subtype.ext (unique_in_band phase he hi' hj'))
  have hne' : c.val.1.1.val≠d.val.1.1.val := fun he => hbands (Subtype.ext he)
  have hc := domain_band phase c.val hi'
  have hd := domain_band phase d.val hj'
  have hout : ∀ {e : Kept A S phase omega}, H ∈ (keptStep A S phase hm omega e).patch.domain i →
      (H=lower q L U e.val.1.1 ∨ H=lower q L U e.val.1.1+a₁) →
      ((keptStep A S phase hm omega e).patch.active w i H ↔ (S.lift.sets.activity w).active i H) := by
    intro e he he'
    exact (keptStep A S phase hm omega e).endpoint_old w i H he he'
  rcases lt_or_gt_of_ne hne' with he | he
  · obtain ⟨h1,h2⟩ := Tiling.overlap interpolationA.2.1 he hc hd
    exact ⟨hout hi (Or.inr (by dsimp [lower]; linarith)),hout hj (Or.inl h2)⟩
  · obtain ⟨h1,h2⟩ := Tiling.overlap interpolationA.2.1 he hd hc
    exact ⟨hout hi (Or.inl h2),hout hj (Or.inr (by dsimp [lower]; linarith))⟩

/-- The simultaneous main mode is now genuinely defined for every old state
and every finite sample. Its family contains exactly the available kept cells. -/
noncomputable def batch : OrdinaryState.MainBatch S where
  count := Fintype.card (Kept A S phase omega)
  band a := BandTrees.band broad (lower q L U ((Fintype.equivFin (Kept A S phase omega)).symm a).val.1.1)
  root a := BandTrees.root M broad
    (lower q L U ((Fintype.equivFin (Kept A S phase omega)).symm a).val.1.1)
    ((Fintype.equivFin (Kept A S phase omega)).symm a).val.1.2
  step a := keptStep A S phase hm omega ((Fintype.equivFin (Kept A S phase omega)).symm a)
  overlap := by
    apply List.pairwise_ofFn.mpr
    intro a b hab
    apply overlap A S phase hm omega
    exact fun he => (ne_of_lt hab) ((Fintype.equivFin (Kept A S phase omega)).symm.injective he)

noncomputable def result [SFinite μ] : OrdinaryState M kappaA (Ω × Bool) (μ.prod Threshold.fair) :=
  (batch A S phase hm omega).apply

/-- Fresh offsets and cell coins are sampled as a finite product, after the
bands and radial origins; unavailable cells simply discard their sample. -/
noncomputable def execution [SFinite μ] :
    Execution (OrdinaryState M kappaA (Ω × Bool) (μ.prod Threshold.fair)) :=
  (Execution.uniform (α := Sample phase m)).bind (fun omega => .pure (result A S phase hm omega))

end PlanarL1.Columns.Model.MainFamily

end


section

namespace PlanarL1.Columns.Model.OrdinaryState.MainBatch
open MeasureTheory
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {M : Model n} {κ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {S : OrdinaryState M κ Ω μ} (B : MainBatch S)

lemma point_description (i : Fin n) (H : ℝ) :
    (∃ q : Fin B.count, ∀ ω, (B.sets.activity ω).active i H ↔
      ((B.step q).patch.apply.activity ω).active i H) ∨
    (∀ ω, (B.sets.activity ω).active i H ↔ (S.lift.sets.activity ω).active i H) := by
  classical
  by_cases h : ∃ q : Fin B.count, H ∈ (B.step q).patch.domain i
  · obtain ⟨q,hq⟩ := h
    exact Or.inl ⟨q,fun ω => SetPatch.batch_inside _ B.overlap
      (List.mem_ofFn.mpr ⟨q,rfl⟩) ω i H hq⟩
  · right
    intro ω
    apply SetPatch.batch_old _ B.overlap ω i H
    intro P hP
    obtain ⟨q,rfl⟩ := List.mem_ofFn.mp hP
    exact (B.step q).patch.unchanged (fun hh => h ⟨q,hh⟩) ω

lemma apply_sets [SFinite μ] : B.apply.sets=B.sets := rfl

lemma movement_integrable (i : Fin n) (H : ℝ) :
    Integrable (fun ω => (B.sets.activity ω).indicator i H-
      (S.lift.sets.activity ω).indicator i H) (μ.prod Threshold.fair) := by
  rcases B.point_description i H with ⟨q,hq⟩ | h
  · have he (ω) : (B.sets.activity ω).indicator i H=((B.step q).patch.apply.activity ω).indicator i H := by
      simp only [Activity.indicator,hq ω]
    simp_rw [he]
    exact (B.step q).movement_integrable i H
  · have he (ω) : (B.sets.activity ω).indicator i H=(S.lift.sets.activity ω).indicator i H := by
      simp only [Activity.indicator,h ω]
    simp only [he,sub_self]
    exact integrable_zero _ _ _

/-- The number of simultaneous cells never enters the movement bound. -/
lemma movement_bound (hκ : 0≤κ) (i : Fin n) (H : ℝ) :
    (∫ ω, |(B.sets.activity ω).indicator i H-
      (S.lift.sets.activity ω).indicator i H| ∂(μ.prod Threshold.fair)) ≤ κ*(1+(1:ℝ)/100) := by
  rcases B.point_description i H with ⟨q,hq⟩ | h
  · have he (ω) : (B.sets.activity ω).indicator i H=((B.step q).patch.apply.activity ω).indicator i H := by
      simp only [Activity.indicator,hq ω]
    simp_rw [he]
    exact (B.step q).movement_bound i H
  · have he (ω) : (B.sets.activity ω).indicator i H=(S.lift.sets.activity ω).indicator i H := by
      simp only [Activity.indicator,h ω]
    simp only [he,sub_self,abs_zero,integral_zero]
    positivity

end PlanarL1.Columns.Model.OrdinaryState.MainBatch

end



section

namespace PlanarL1.Columns.Model
open MeasureTheory
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)}
namespace BandTrees
variable (P : Parameters.Interpolation) (lo : ℝ) (C : Component M P lo)
lemma main_cover (phase : ℝ) {i : Fin (k+1)} (hi : i ∈ C.supp) :
    ∃ c : MainIndex M P lo C phase, i ∈ ColumnOrder.componentColumns c.2 := by
  let x := point M P lo C ⟨i,hi⟩
  let l := Tiling.index (1/1000) phase (dist (base M P lo C) x)
  have hl : l ∈ levels M P lo C phase (1/1000) :=
    Finset.mem_image.mpr ⟨⟨i,hi⟩,Finset.mem_univ _,rfl⟩
  have hx : i ∈ (base M P lo C).layer (middle P lo) (middle_mem P lo)
      (phase+(l:ℝ)*(1/1000)) (1/1000) := by
    refine ⟨x.reachable,?_,?_⟩
    · have h := Int.floor_le ((dist (base M P lo C) x-phase)/(1/1000))
      have hh := (le_div_iff₀ (by norm_num : (0:ℝ)<1/1000)).mp h
      change phase+(l:ℝ)*(1/1000)≤dist (base M P lo C) x
      dsimp [l,Tiling.index]
      linarith
    · have h := Int.lt_floor_add_one ((dist (base M P lo C) x-phase)/(1/1000))
      have hh := (div_lt_iff₀ (by norm_num : (0:ℝ)<1/1000)).mp h
      change dist (base M P lo C) x<phase+(l:ℝ)*(1/1000)+1/1000
      dsimp [l,Tiling.index]
      linarith
  let G := (M.activeGraph (band P lo)).induce ((base M P lo C).layer (middle P lo)
    (middle_mem P lo) (phase+(l:ℝ)*(1/1000)) (1/1000))
  exact ⟨⟨⟨l,hl⟩,G.connectedComponentMk ⟨i,hx⟩⟩,⟨⟨i,hx⟩,rfl,rfl⟩⟩
end BandTrees

namespace MainFamily
open Parameters
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable (A : Ambient M) (S : OrdinaryState M kappaA Ω μ)
variable {q L U : ℝ} (phase : BandComponent (M := M) q L U → ℝ)

lemma cover (i : Fin (k+1)) {H : ℝ} (hH : H ∈ Set.Icc L U) :
    ∃ c : CellIndex q L U phase, H ∈ domain phase c i := by
  obtain ⟨b,hb,hHb⟩ := Tiling.processed_covers interpolationA.2.1 (q := q) hH
  let b' : BandIndex q L U := ⟨b,hb⟩
  let C : BandTrees.Component M broad (lower q L U b') :=
    (M.activeGraph (BandTrees.band broad (lower q L U b'))).connectedComponentMk i
  obtain ⟨c,hc⟩ := BandTrees.main_cover broad (lower q L U b') C (phase ⟨b',C⟩) (i := i) rfl
  refine ⟨⟨⟨b',C⟩,c⟩,(MainCell.mem_domain _ _ _).mpr ⟨hc,?_⟩⟩
  dsimp [BandTrees.band,lower,broad,b']
  constructor <;> dsimp [Tiling.band] at hHb <;> linarith [hHb.1,hHb.2]

lemma ambient_dist_le {J : Set ℝ} {root : Fin (k+1)} (x y : M.Point J root) :
    dist (A.point x.column x.height) (A.point y.column y.height)≤dist x y := by
  have h := x.dist_widen_le y (Set.subset_univ J)
  have he := Point.dist_coordinates (x.widen (Set.subset_univ J)) (y.widen (Set.subset_univ J))
    (A.point x.column x.height) (A.point y.column y.height) rfl rfl rfl rfl
  exact he ▸ h

lemma cell_diameter (c : CellIndex q L U phase) {i j : Fin (k+1)} {H T : ℝ}
    (hi : H ∈ domain phase c i) (hj : T ∈ domain phase c j) :
    dist (A.point i H) (A.point j T)≤1/100 := by
  let x := MainCell.cellPoint (tree phase c) (radial phase c) c.2.2 i H hi
  let y := MainCell.cellPoint (tree phase c) (radial phase c) c.2.2 j T hj
  have hh := (tree phase c).base.radial_cell_diameter (tree phase c).closed_band
    (tree phase c).base.inBand (tree phase c).width_pos thinA (tree phase c).half_width c.2.2 x y
    ((MainCell.mem_domain _ _ _).mp hi).1 ((MainCell.mem_domain _ _ _).mp hj).1
  exact (ambient_dist_le A x y).trans (by simpa only [show (10:ℝ)*(1/1000)=1/100 by norm_num] using hh)

/-- The full-neighborhood availability test is derived from a common old
radius-20 ball; it is not an extra hypothesis on the random execution. -/
lemma available_of_ball (c : CellIndex q L U phase) (x : M.Point Set.univ A.root)
    (hx : x.height ∈ domain phase c x.column)
    (hname : ∃ a : Fin (S.count+1), ∀ y : M.Point Set.univ A.root,
      dist x y≤20 → S.name y.column y.height=a) : Available A S phase c := by
  obtain ⟨a,ha⟩ := hname
  refine ⟨a,fun y hy => ha y ?_⟩
  obtain ⟨i,H,hi,hd⟩ := hy
  have hxpoint : A.point x.column x.height=x := by cases x; rfl
  have hc := cell_diameter A phase c hx hi
  rw [hxpoint] at hc
  have ht := dist_triangle x (A.point i H) y
  rw [dist_comm (A.point i H) y] at ht
  linarith

end MainFamily
end PlanarL1.Columns.Model

end

end OAI
