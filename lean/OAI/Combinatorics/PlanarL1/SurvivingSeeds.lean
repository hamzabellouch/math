import OAI.Combinatorics.PlanarL1.ScaleHistory

namespace OAI


section

namespace PlanarL1.Columns.Model.BandTrees
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (M : Model n) (P : Parameters.Interpolation) (lo : ℝ)
variable (C : Component M P lo)

/-- The very same finite connected radial cells, at an arbitrary prescribed
width; the secondary construction uses width g, not the main width D. -/
abbrev RadialIndex (width phase : ℝ) :=
  Σ l : levels M P lo C phase width,
    ((M.activeGraph (band P lo)).induce ((base M P lo C).layer (middle P lo)
      (middle_mem P lo) (phase+l.val*width) width)).ConnectedComponent
noncomputable instance (width phase : ℝ) : Fintype (RadialIndex M P lo C width phase) := Fintype.ofFinite _

variable {M P lo C} {width phase : ℝ}

lemma radial_cover (hw : 0<width) {i : Fin n} (hi : i ∈ C.supp) :
    ∃ K : RadialIndex M P lo C width phase, i ∈ ColumnOrder.componentColumns K.2 := by
  let x := point M P lo C ⟨i,hi⟩
  let l := Tiling.index width phase (dist (base M P lo C) x)
  have hl : l ∈ levels M P lo C phase width :=
    Finset.mem_image.mpr ⟨⟨i,hi⟩,Finset.mem_univ _,rfl⟩
  have hx : i ∈ (base M P lo C).layer (middle P lo) (middle_mem P lo)
      (phase+(l:ℝ)*width) width := by
    refine ⟨x.reachable,?_,?_⟩
    · have h := Int.floor_le ((dist (base M P lo C) x-phase)/width)
      have hh := (le_div_iff₀ hw).mp h
      change phase+(l:ℝ)*width≤dist (base M P lo C) x
      dsimp [l,Tiling.index]
      linarith
    · have h := Int.lt_floor_add_one ((dist (base M P lo C) x-phase)/width)
      have hh := (div_lt_iff₀ hw).mp h
      change dist (base M P lo C) x<phase+(l:ℝ)*width+width
      dsimp [l,Tiling.index]
      linarith
  let G := (M.activeGraph (band P lo)).induce ((base M P lo C).layer (middle P lo)
    (middle_mem P lo) (phase+(l:ℝ)*width) width)
  exact ⟨⟨⟨l,hl⟩,G.connectedComponentMk ⟨i,hx⟩⟩,⟨⟨i,hx⟩,rfl,rfl⟩⟩

lemma radial_unique (hw : 0<width) {K L : RadialIndex M P lo C width phase} {i : Fin n}
    (hi : i ∈ ColumnOrder.componentColumns K.2) (hj : i ∈ ColumnOrder.componentColumns L.2) : K=L := by
  have he : K.1=L.1 := Subtype.ext (same_level M P lo C hw
    (ColumnOrder.componentColumns_subset K.2 hi) (ColumnOrder.componentColumns_subset L.2 hj))
  obtain ⟨K,Ck⟩ := K
  obtain ⟨L,Cl⟩ := L
  dsimp only at he
  subst L
  have he' : Ck=Cl := same_component hi hj
  subst Cl
  rfl

lemma radial_diameter (hthin : P.width≤width/1000) (K : RadialIndex M P lo C width phase)
    (x y : M.Point (band P lo) (root M P lo C))
    (hx : x.column ∈ ColumnOrder.componentColumns K.2)
    (hy : y.column ∈ ColumnOrder.componentColumns K.2) : dist x y≤10*width :=
  (base M P lo C).radial_cell_diameter isClosed_Icc (middle_mem P lo) P.width_pos hthin
    (tree M P lo C).half_width K.2 x y hx hy

lemma radial_separated (hw : 0<width) {K L : RadialIndex M P lo C width phase} (hKL : K≠L)
    (x y : M.Point (band P lo) (root M P lo C))
    (hx : x.column ∈ ColumnOrder.componentColumns K.2)
    (hy : y.column ∈ ColumnOrder.componentColumns L.2) {b : ℝ}
    (hl : phase+(K.1.val:ℝ)*width+b+2*P.width <
      dist (base M P lo C) (x.withHeight (middle P lo) (middle_mem P lo)))
    (hu : dist (base M P lo C) (x.withHeight (middle P lo) (middle_mem P lo)) <
      phase+(K.1.val:ℝ)*width+width-b-2*P.width) : b<dist x y := by
  by_contra h
  have hd : dist x y≤b := le_of_not_gt h
  obtain ⟨p,_,hp⟩ := x.exists_shortest isClosed_Icc y
  have hyK := (base M P lo C).radial_cell_padding x y (middle_mem P lo) P.width_pos.le
    (tree M P lo C).half_width K.2 hx hl hu p (hp ▸ hd)
  exact hKL (radial_unique hw hyK hy)

end PlanarL1.Columns.Model.BandTrees

end


section

namespace PlanarL1.Columns.Model.SurvivingGroups
open Parameters MeasureTheory
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω Ξ : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω} {ν : Measure Ξ}
variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)
variable (SB : BState M kappaB SecondaryGeometry.Group.lam Ξ ν)
variable (lo : ℝ) (C : BandTrees.Component M broad lo) (lo₂ phase : ℝ)

/-- Geometric part of a retained endpoint, before witness selection. Both
old identifiers refer to the actual closed unrestricted radius-five ball. -/
structure Position where
  point : M.Point (BandTrees.band broad lo) (BandTrees.root M broad lo C)
  narrow_height : point.height ∈ BandTrees.band narrow lo₂
  cell : BandTrees.RadialIndex M broad lo C g phase
  cell_mem : point.column ∈ ColumnOrder.componentColumns cell.2
  lower_pad : phase+(cell.1.val:ℝ)*g+g/100+2*a₁ <
    dist (BandTrees.base M broad lo C)
      (point.withHeight (BandTrees.middle broad lo) (BandTrees.middle_mem broad lo))
  upper_pad : dist (BandTrees.base M broad lo C)
      (point.withHeight (BandTrees.middle broad lo) (BandTrees.middle_mem broad lo)) <
    phase+(cell.1.val:ℝ)*g+g-g/100-2*a₁
  indexA : Fin (SA.count+1)
  indexB : Fin (SB.count+1)
  commonA : A.Common SA.name (A.point point.column point.height) 5 indexA
  commonB : A.Common SB.name (A.point point.column point.height) 5 indexB

namespace Position
variable {A SA SB lo C lo₂ phase} (p : Position A SA SB lo C lo₂ phase)
lemma band_near {H : ℝ} (hH : H ∈ BandTrees.band broad lo) : |p.point.height-H|≤5 := by
  have hp := p.point.inBand
  change lo≤p.point.height ∧ p.point.height≤lo+a₁ at hp
  change lo≤H ∧ H≤lo+a₁ at hH
  have hsmall : a₁≤5 := by norm_num [a₁]
  exact abs_le.mpr ⟨by linarith [hp.1,hp.2,hH.1,hH.2],by linarith [hp.1,hp.2,hH.1,hH.2]⟩
lemma subA : BandTrees.band broad lo ⊆ (SA.chart p.indexA).band :=
  SA.ball_band A p.commonA (fun _ hH => p.band_near hH)
lemma subB : BandTrees.band broad lo ⊆ (SB.chart p.indexB).band :=
  SB.ball_band A p.commonB (fun _ hH => p.band_near hH)
lemma contains : (SA.chart p.indexA).Contains p.point.column p.point.height :=
  SA.contains_named _ _ _ (p.commonA.center A (by norm_num))
end Position

/-- Literal geometric data retained after both descent tests and the low-tip
exclusion. These records are finite witnesses of those tests, not estimates or
success/persistence assumptions. -/
structure Seed extends Position A SA SB lo C lo₂ phase where
  partner : M.Point (SA.chart indexA).band (BandTrees.root M broad lo C)
  descent : (SA.chart indexA).comparison.BandDescent (BandTrees.band broad lo)
    (point.widen toPosition.subA) epsilon
  partner_descent : (SA.chart indexA).comparison.BandDescent (BandTrees.band broad lo)
    partner epsilon
  apart : 1≤dist (point.widen toPosition.subA) partner
  close : |(SA.chart indexA).comparison.eval partner-
    (SA.chart indexA).comparison.eval (point.widen toPosition.subA)|≤EA
  retained : (SA.chart indexA).comparison.NoLowCircular
    (point.widen toPosition.subA) partner (BandTrees.band narrow lo₂) j

variable {A SA SB lo C lo₂ phase}
namespace Seed
variable (w : Seed A SA SB lo C lo₂ phase)
lemma source : ∃ o : M.Point (SA.chart w.indexA).band (BandTrees.root M broad lo C),
    (SA.chart w.indexA).comparison=o.radialField :=
  (SA.chart w.indexA).source_of_descent (w.point.widen w.toPosition.subA)
    w.toPosition.contains (by norm_num [epsilon]) ⟨w.descent⟩
end Seed

variable {W : Type*} [Fintype W] (s : W → Seed A SA SB lo C lo₂ phase)
abbrev Key := BandTrees.RadialIndex M broad lo C g phase × Fin (SA.count+1) × Fin (SB.count+1)
noncomputable def key (w : W) : Key (SA := SA) (SB := SB) (lo := lo) (C := C) (phase := phase) :=
  ((s w).cell,(s w).indexA,(s w).indexB)
noncomputable def keys := Finset.univ.image (key s)
noncomputable abbrev GroupIndex := keys s
noncomputable instance : Fintype (GroupIndex s) := Fintype.ofFinite _
noncomputable def members (q : GroupIndex s) : Finset W := Finset.univ.filter (fun w => key s w=q.val)
lemma members_nonempty (q : GroupIndex s) : (members s q).Nonempty := by
  obtain ⟨w,_,hw⟩ := Finset.mem_image.mp q.property
  exact ⟨w,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw⟩⟩
noncomputable def seeds (q : GroupIndex s) := (members s q).image (fun w => (s w).point)
lemma seed_mem (q : GroupIndex s) {x : M.Point (BandTrees.band broad lo) (BandTrees.root M broad lo C)} :
    x ∈ seeds s q ↔ ∃ w, key s w=q.val ∧ (s w).point=x := by
  simp only [seeds,members,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
lemma seeds_nonempty (q : GroupIndex s) : (seeds s q).Nonempty := (members_nonempty s q).image _

variable (hsub : BandTrees.band narrow lo₂ ⊆ BandTrees.band broad lo)
/-- Group formation: exactly one finite proposal family per g-cell and pair
of old identifiers. The update groups themselves add no chart boundary. -/
noncomputable def group (q : GroupIndex s) : SecondaryGeometry.Group A SB where
  index := q.val.2.2
  broad := BandTrees.band broad lo
  broad_root := BandTrees.root M broad lo C
  broad_closed := isClosed_Icc
  lower := lo₂
  narrow_sub := hsub
  sub_old := by
    obtain ⟨w,hw⟩ := members_nonempty s q
    have he : key s w=q.val := (Finset.mem_filter.mp hw).2
    have hb : (s w).indexB=q.val.2.2 := congrArg (fun t => t.2.2) he
    exact hb ▸ (s w).toPosition.subB
  seeds := seeds s q
  nonempty := seeds_nonempty s q
  height := by
    intro x hx
    obtain ⟨w,_,rfl⟩ := (seed_mem s q).mp hx
    exact (s w).narrow_height
  diameter := by
    intro x hx y hy
    obtain ⟨w,hw,rfl⟩ := (seed_mem s q).mp hx
    obtain ⟨v,hv,rfl⟩ := (seed_mem s q).mp hy
    have hc : (s w).cell=(s v).cell := congrArg Prod.fst (hw.trans hv.symm)
    exact BandTrees.radial_diameter (by norm_num [broad,a₁,g]) (s w).cell
      (s w).point (s v).point (s w).cell_mem (hc ▸ (s v).cell_mem)
  common := by
    intro x hx
    obtain ⟨w,hw,rfl⟩ := (seed_mem s q).mp hx
    have hb : (s w).indexB=q.val.2.2 := congrArg (fun t => t.2.2) hw
    exact hb ▸ (s w).commonB

end PlanarL1.Columns.Model.SurvivingGroups

end



section

namespace PlanarL1.Columns.Model.SurvivingGroups
open Parameters MeasureTheory
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω Ξ : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω} {ν : Measure Ξ}
variable {A : Ambient M} {SA : OrdinaryState M kappaA Ω μ}
variable {SB : BState M kappaB SecondaryGeometry.Group.lam Ξ ν}
variable {lo : ℝ} {C : BandTrees.Component M broad lo} {lo₂ phase : ℝ}
namespace Seed
variable (w : Seed A SA SB lo C lo₂ phase) {a : Fin (SA.count+1)}
noncomputable def partnerAt (he : w.indexA=a) :
    M.Point (SA.chart a).band (BandTrees.root M broad lo C) := he ▸ w.partner
noncomputable def descentAt (he : w.indexA=a)
    (hsub : BandTrees.band broad lo ⊆ (SA.chart a).band) :
    (SA.chart a).comparison.BandDescent (BandTrees.band broad lo)
    (w.point.widen hsub) epsilon := by subst a; exact w.descent
noncomputable def partnerDescentAt (he : w.indexA=a) :
    (SA.chart a).comparison.BandDescent (BandTrees.band broad lo)
    (w.partnerAt he) epsilon := by subst a; exact w.partner_descent
lemma apartAt (he : w.indexA=a)
    (hsub : BandTrees.band broad lo ⊆ (SA.chart a).band) :
    1≤dist (w.point.widen hsub) (w.partnerAt he) := by subst a; exact w.apart
lemma closeAt (he : w.indexA=a)
    (hsub : BandTrees.band broad lo ⊆ (SA.chart a).band) :
    |(SA.chart a).comparison.eval (w.partnerAt he)-
    (SA.chart a).comparison.eval (w.point.widen hsub)|≤EA := by subst a; exact w.close
lemma retainedAt (he : w.indexA=a)
    (hsub : BandTrees.band broad lo ⊆ (SA.chart a).band) :
    (SA.chart a).comparison.NoLowCircular
    (w.point.widen hsub) (w.partnerAt he) (BandTrees.band narrow lo₂) j := by
  subst a; exact w.retained
end Seed

variable {W : Type*} [Fintype W] (s : W → Seed A SA SB lo C lo₂ phase)
variable (hsub : BandTrees.band narrow lo₂ ⊆ BandTrees.band broad lo)

include hsub in
omit [Fintype W] in
/-- Coincidence of BOTH old names at the center is derived from literal
eligibility. No bound on the pre-existing number of chart identifiers is used. -/
lemma center_names (c : M.Point (BandTrees.band broad lo) (BandTrees.root M broad lo C))
    (cp : ∀ w, M.Path (BandTrees.band narrow lo₂) c.column (s w).point.column)
    (hp : ∀ w, (cp w).length c.height (s w).point.height≤4*R) (w : W) :
    SA.name c.column c.height=(s w).indexA ∧ SB.name c.column c.height=(s w).indexB := by
  have hd : dist (A.point (s w).point.column (s w).point.height) (A.point c.column c.height)≤5 := by
    rw [dist_comm]
    apply (MainFamily.ambient_dist_le (A := A) c (s w).point).trans
    apply (c.distance_le (s w).point ((cp w).widen hsub)).trans
    have h := hp w
    simp only [Path.length_widen]
    exact h.trans (by norm_num [R])
  exact ⟨(s w).commonA (A.point c.column c.height) hd,
    (s w).commonB (A.point c.column c.height) hd⟩

include hsub in
/-- The concrete restricted packing estimate for retained endpoints: choose
one seed per actual group meeting the narrow ball, rather than assume a
bounded overlap of proposal domains. -/
theorem packing (c : M.Point (BandTrees.band broad lo) (BandTrees.root M broad lo C))
    (hc : c.height ∈ BandTrees.band narrow lo₂)
    (cp : ∀ w, M.Path (BandTrees.band narrow lo₂) c.column (s w).point.column)
    (hp : ∀ w, (cp w).length c.height (s w).point.height≤4*R)
    (hkey : Function.Injective (key s)) : (Fintype.card W : ℝ)≤2+1600*R/g := by
  classical
  by_cases hn : Nonempty W
  · let w₀ : W := Classical.choice hn
    have sameA (w : W) : (s w).indexA=(s w₀).indexA :=
      (center_names s hsub c cp hp w).1.symm.trans (center_names s hsub c cp hp w₀).1
    have sameB (w : W) : (s w).indexB=(s w₀).indexB :=
      (center_names s hsub c cp hp w).2.symm.trans (center_names s hsub c cp hp w₀).2
    let hKI := (s w₀).toPosition.subA
    obtain ⟨o,ho⟩ := (s w₀).source
    let partner (w : W) := (s w).partnerAt (sameA w)
    have Dx (w : W) : o.radialField.BandDescent (BandTrees.band broad lo)
        ((s w).point.widen hKI) epsilon := by
      rw [← ho]; exact (s w).descentAt (sameA w) hKI
    have Dy (w : W) : o.radialField.BandDescent (BandTrees.band broad lo) (partner w) epsilon := by
      rw [← ho]; exact (s w).partnerDescentAt (sameA w)
    have hf (w : W) : |dist o (partner w)-dist o ((s w).point.widen hKI)|≤EA := by
      have h := (s w).closeAt (sameA w) hKI
      rw [ho] at h
      simpa only [Point.radialField_eval] using h
    have hr (w : W) : o.radialField.NoLowCircular ((s w).point.widen hKI)
        (partner w) (BandTrees.band narrow lo₂) j := by
      rw [← ho]; exact (s w).retainedAt (sameA w) hKI
    have hsep (w v : W) (h : w≠v) : g/100≤dist (s w).point (s v).point := by
      have he : (s w).cell≠(s v).cell := by
        intro he
        apply h (hkey ?_)
        change ((s w).cell,(s w).indexA,(s w).indexB)=((s v).cell,(s v).indexA,(s v).indexB)
        rw [he,sameA w,sameA v,sameB w,sameB v]
      exact (BandTrees.radial_separated (by norm_num [g]) he (s w).point (s v).point
        (s w).cell_mem (s v).cell_mem (s w).lower_pad (s w).upper_pad).le
    have hb := Field.radial_surviving_packing (SA.chart (s w₀).indexA).closed hsub hKI
      (a := a₁) (A := 4*R) (E := EA) (δ := (1:ℝ)/200000) (j := j) (ε := epsilon) (b := g/100)
      (by
        intro H hH T hT
        change lo≤H ∧ H≤lo+a₁ at hH
        change lo≤T ∧ T≤lo+a₁ at hT
        exact abs_le.mpr ⟨by linarith [hH.1,hH.2,hT.1,hT.2],by linarith [hH.1,hH.2,hT.1,hT.2]⟩)
      (by norm_num [R]) (by norm_num [R]) (by norm_num [EA,epsilon])
      (by norm_num [a₁,R]) (by norm_num [R,EA,epsilon,a₁]) (by norm_num [R,a₁])
      (by norm_num [g]) (by norm_num [j,epsilon,a₁,g]) (by norm_num [j,epsilon,a₁])
      o c hc (fun w => (s w).point) partner (fun w => (s w).narrow_height) Dx Dy
      (fun w => (s w).apartAt (sameA w) hKI) hf hr cp hp hsep
    convert hb using 1; norm_num [R,g]
  · have : IsEmpty W := not_nonempty_iff.mp hn
    simp only [Fintype.card_of_isEmpty,Nat.cast_zero]
    norm_num [R,g]

end PlanarL1.Columns.Model.SurvivingGroups

end



section

namespace PlanarL1.Columns.Model.SurvivingGroups
open Parameters MeasureTheory
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω Ξ : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω} {ν : Measure Ξ}
variable {A : Ambient M} {SA : OrdinaryState M kappaA Ω μ}
variable {SB : BState M kappaB SecondaryGeometry.Group.lam Ξ ν}
variable {lo : ℝ} {C : BandTrees.Component M broad lo} {lo₂ phase : ℝ}
variable {W : Type*} [Fintype W] (s : W → Seed A SA SB lo C lo₂ phase)

/-- A real group meets the narrow-band radius-four-R ball through one of its
actual retained endpoints. This test involves no fresh random choices. -/
def Touch (c : M.Point (BandTrees.band broad lo) (BandTrees.root M broad lo C))
    (q : GroupIndex s) : Prop := ∃ w, key s w=q.val ∧
      ∃ p : M.Path (BandTrees.band narrow lo₂) c.column (s w).point.column,
        p.length c.height (s w).point.height≤4*R
noncomputable abbrev Hits (c : M.Point (BandTrees.band broad lo) (BandTrees.root M broad lo C)) :=
  {q : GroupIndex s // Touch s c q}
noncomputable instance (c : M.Point (BandTrees.band broad lo) (BandTrees.root M broad lo C)) :
    Fintype (Hits s c) := Fintype.ofFinite _

/-- One fixed universal integer, never depending on the finite list, the old
identifiers, or the old chart count. -/
noncomputable def packBound : ℕ := 2+Nat.ceil (1600*R/g)

lemma packBound_real : 2+1600*R/g≤(packBound : ℝ) := by
  dsimp only [packBound]
  push_cast
  linarith [Nat.le_ceil (1600*R/g)]

lemma touching_card (hsub : BandTrees.band narrow lo₂ ⊆ BandTrees.band broad lo)
    (c : M.Point (BandTrees.band broad lo) (BandTrees.root M broad lo C))
    (hc : c.height ∈ BandTrees.band narrow lo₂) : Fintype.card (Hits s c)≤packBound := by
  classical
  let w : Hits s c → W := fun q => Classical.choose q.property
  have hw (q : Hits s c) : key s (w q)=q.val.val := (Classical.choose_spec q.property).1
  let p (q : Hits s c) : M.Path (BandTrees.band narrow lo₂) c.column (s (w q)).point.column :=
    Classical.choose (Classical.choose_spec q.property).2
  have hp (q : Hits s c) : (p q).length c.height (s (w q)).point.height≤4*R :=
    Classical.choose_spec (Classical.choose_spec q.property).2
  have hinj : Function.Injective (key (fun q : Hits s c => s (w q))) := by
    intro q q' he
    apply Subtype.ext
    apply Subtype.ext
    exact (hw q).symm.trans (he.trans (hw q'))
  have hb := packing (fun q : Hits s c => s (w q)) hsub c hc p hp hinj
  exact_mod_cast hb.trans packBound_real

lemma touching_finset_card (hsub : BandTrees.band narrow lo₂ ⊆ BandTrees.band broad lo)
    (c : M.Point (BandTrees.band broad lo) (BandTrees.root M broad lo C))
    (hc : c.height ∈ BandTrees.band narrow lo₂) :
    (Finset.univ.filter (Touch s c)).card≤packBound := by
  simpa only [Hits,Fintype.card_subtype] using touching_card s hsub c hc

end PlanarL1.Columns.Model.SurvivingGroups

end



section

namespace PlanarL1.Columns.Model.SecondaryGeometry.Group
open MeasureTheory Parameters
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {A : Ambient M} {S : BState M kappaB (⟨lambda,by norm_num [lambda,R]⟩) Ω μ}
variable (G : SecondaryGeometry.Group A S)

lemma not_admitted_witness (positive : Bool) (C : G.Component)
    (w : M.Point (BandTrees.band narrow G.lower) (G.root C))
    (h : ¬G.Admitted positive C w) :
    ∃ z : M.Point (BandTrees.band narrow G.lower) (G.root C),
      dist w z=R ∧ G.old positive C z<G.pc positive-(65/100:ℝ)*R := by
  have hn : ¬∀ z : M.Point (BandTrees.band narrow G.lower) (G.root C),
      dist w z=R → G.pc positive-(65/100:ℝ)*R≤G.old positive C z :=
    fun hh => h (Or.inr hh)
  push Not at hn
  exact hn

lemma nonadmission_drop (positive : Bool) (C : G.Component)
    (w z : M.Point (BandTrees.band narrow G.lower) (G.root C))
    (hw : w ∈ G.allSeeds C)
    (hz : G.old positive C z<G.pc positive-(65/100:ℝ)*R) :
    G.old positive C z<G.old positive C w-(3/5:ℝ)*R := by
  have hn := (abs_le.mp (G.seed_near positive C w hw)).1
  have hR : 0<R := by norm_num [R]
  linarith

lemma narrow_sub_ordered {D : OrderedData M} (he : G.data=.ordered D) :
    BandTrees.band narrow G.lower ⊆ D.band := by
  intro H hH
  simpa only [he,BData.band] using G.sub_old (G.narrow_sub hH)

lemma old_ordered {D : OrderedData M} (he : G.data=.ordered D)
    (positive : Bool) (C : G.Component)
    (w : M.Point (BandTrees.band narrow G.lower) (G.root C)) :
    G.old positive C w =
      if positive then D.value lam w.column ⟨w.height,G.narrow_sub_ordered he w.inBand⟩
      else -D.value lam w.column ⟨w.height,G.narrow_sub_ordered he w.inBand⟩ := by
  have aux (E : BData M) (hE : E=.ordered D) (i : Fin (k+1)) (H : ℝ) (hH : H ∈ E.band) :
      (E.comparison lam lam_bound positive).value i ⟨H,hH⟩ =
        if positive then D.value lam i ⟨H,by simpa only [hE,BData.band] using hH⟩
        else -D.value lam i ⟨H,by simpa only [hE,BData.band] using hH⟩ := by
    subst E
    cases positive
    · change -(D.field lam lam_bound).value i ⟨H,hH⟩ = -D.value lam i ⟨H,hH⟩
      rw [OrderedData.field_value]
    · exact D.field_value lam lam_bound i ⟨H,hH⟩
  exact aux G.data he _ _ _

/-- Literal rejection of both sphere tests provides actual narrow-band paths
with opposite excursions of the fixed ordered part. No excursion hypothesis
is substituted for the geometric admission test. -/
noncomputable def excursions_of_rejected {D : OrderedData M} (he : G.data=.ordered D)
    (C : G.Component) (w : M.Point (BandTrees.band narrow G.lower) (G.root C))
    (hw : w ∈ G.allSeeds C) (hpos : ¬G.Admitted true C w) (hneg : ¬G.Admitted false C w)
    {root : Fin (k+1)} (x : M.Point D.band root)
    (hc : x.column=w.column) (hH : x.height=w.height) :
    D.base.Excursions (G.narrow_sub_ordered he) x (2*R) (2*R/5) := by
  apply Classical.choice
  rcases x with ⟨xc,xh,xi,xr⟩
  change xc=w.column at hc
  change xh=w.height at hH
  subst xc
  subst xh
  have sub : BandTrees.band narrow G.lower ⊆ D.band := G.narrow_sub_ordered he
  obtain ⟨z,hz,hval⟩ := G.not_admitted_witness true C w hpos
  obtain ⟨v,hv,hval'⟩ := G.not_admitted_witness false C w hneg
  obtain ⟨p,_,hp⟩ := w.exists_shortest isClosed_Icc z
  obtain ⟨q,_,hq⟩ := w.exists_shortest isClosed_Icc v
  have hlo := G.nonadmission_drop true C w z hw hval
  have hhi := G.nonadmission_drop false C w v hw hval'
  rw [G.old_ordered he true C z,G.old_ordered he true C w] at hlo
  rw [G.old_ordered he false C v,G.old_ordered he false C w] at hhi
  simp only [ite_true,Bool.false_eq_true,ite_false] at hlo hhi
  have ha := (D.auxiliary.restrict sub).path_bound p ⟨w.height,w.inBand⟩ ⟨z.height,z.inBand⟩
  have hb := (D.auxiliary.restrict sub).path_bound q ⟨w.height,w.inBand⟩ ⟨v.height,v.inBand⟩
  change |D.auxiliary.value w.column ⟨w.height,sub w.inBand⟩-
    D.auxiliary.value z.column ⟨z.height,sub z.inBand⟩|≤100*p.length w.height z.height at ha
  change |D.auxiliary.value w.column ⟨w.height,sub w.inBand⟩-
    D.auxiliary.value v.column ⟨v.height,sub v.inBand⟩|≤100*q.length w.height v.height at hb
  have ha' := ha.trans (le_of_eq (congrArg (fun t : ℝ => 100*t) (hp.trans hz)))
  have hb' := hb.trans (le_of_eq (congrArg (fun t : ℝ => 100*t) (hq.trans hv)))
  have hlow := (abs_le.mp ha').2
  have hhigh := (abs_le.mp hb').1
  dsimp only [OrderedData.value] at hlo hhi
  have hl : (0:ℝ)≤(lam:ℝ) := NNReal.coe_nonneg lam
  have hnum : (lam:ℝ)*100*R < R/5 := by
    change lambda*100*R<R/5
    norm_num [lambda,R]
  have hlo' : D.base.value z.column ⟨z.height,sub z.inBand⟩ <
      D.base.value w.column ⟨w.height,sub w.inBand⟩-2*R/5 := by nlinarith
  have hhi' : D.base.value w.column ⟨w.height,sub w.inBand⟩+2*R/5 <
      D.base.value v.column ⟨v.height,sub v.inBand⟩ := by nlinarith
  refine ⟨⟨w.inBand,z.column,v.column,⟨z.height,z.inBand⟩,⟨v.height,v.inBand⟩,
    p,q,?_,?_,?_,?_⟩⟩
  · exact (le_of_eq (hp.trans hz)).trans (by norm_num [R])
  · exact (le_of_eq (hq.trans hv)).trans (by norm_num [R])
  · exact hlo'
  · exact hhi'

end PlanarL1.Columns.Model.SecondaryGeometry.Group

end



section

namespace PlanarL1.Columns.Model
open MeasureTheory Parameters
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)}

namespace OrderedData
/-- The literal old-field cutoff controls the fixed ordered part; the
auxiliary field is already 100-Lipschitz by its recorded history. -/
lemma base_close_of_value (D : OrderedData M) {root : Fin (k+1)}
    (x y : M.Point D.band root) (hnear : dist x y≤2)
    (hcut : |D.value SecondaryGeometry.Group.lam x.column ⟨x.height,x.inBand⟩-
      D.value SecondaryGeometry.Group.lam y.column ⟨y.height,y.inBand⟩|≤R/10000) :
    |D.base.eval x-D.base.eval y|≤R/1000 := by
  have hu := (D.auxiliary.lipschitz D.closed root).dist_le_mul x y
  change |D.auxiliary.eval x-D.auxiliary.eval y|≤100*dist x y at hu
  have haux : |D.auxiliary.eval x-D.auxiliary.eval y|≤200 := by linarith
  have hl : (0:ℝ)≤(SecondaryGeometry.Group.lam:ℝ) := NNReal.coe_nonneg _
  have hnum : R/10000+(SecondaryGeometry.Group.lam:ℝ)*200≤R/1000 := by
    change R/10000+lambda*200≤R/1000
    norm_num [lambda,R]
  have hh := abs_sub (D.value SecondaryGeometry.Group.lam x.column ⟨x.height,x.inBand⟩-
      D.value SecondaryGeometry.Group.lam y.column ⟨y.height,y.inBand⟩)
    ((SecondaryGeometry.Group.lam:ℝ)*(D.auxiliary.eval x-D.auxiliary.eval y))
  have he : (D.value SecondaryGeometry.Group.lam x.column ⟨x.height,x.inBand⟩-
      D.value SecondaryGeometry.Group.lam y.column ⟨y.height,y.inBand⟩)-
      (SecondaryGeometry.Group.lam:ℝ)*(D.auxiliary.eval x-D.auxiliary.eval y)=
      D.base.eval x-D.base.eval y := by simp only [value,Field.eval]; ring
  rw [he,abs_mul,abs_of_nonneg hl] at hh
  exact hh.trans ((add_le_add hcut (mul_le_mul_of_nonneg_left haux hl)).trans hnum)
end OrderedData

namespace SecondaryGeometry.Group
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {A : Ambient M} {S : BState M kappaB (⟨lambda,by norm_num [lambda,R]⟩) Ω μ}
variable (G H : SecondaryGeometry.Group A S)

/-- No admitted endpoint gives the genuine transverse separation. All sphere
witnesses and paths are obtained from the admission failures, not assumed. -/
theorem two_side_of_rejected {D : OrderedData M}
    (he : G.data=.ordered D) (hf : H.data=.ordered D) (hl : H.lower=G.lower)
    (C : G.Component) (E : H.Component)
    (w : M.Point (BandTrees.band narrow G.lower) (G.root C))
    (v : M.Point (BandTrees.band narrow H.lower) (H.root E))
    (hw : w ∈ G.allSeeds C) (hv : v ∈ H.allSeeds E)
    (hwp : ¬G.Admitted true C w) (hwn : ¬G.Admitted false C w)
    (hvp : ¬H.Admitted true E v) (hvn : ¬H.Admitted false E v)
    {root : Fin (k+1)} (x y : M.Point D.band root)
    (hxc : x.column=w.column) (hxh : x.height=w.height)
    (hyc : y.column=v.column) (hyh : y.height=v.height)
    (hlo : 1≤dist x y) (hhi : dist x y≤2)
    (hcut : |D.value lam x.column ⟨x.height,x.inBand⟩-
      D.value lam y.column ⟨y.height,y.inBand⟩|≤R/10000) :
    (D.base.transverse (by norm_num) D.lower D.upper).eval x *
      (D.base.transverse (by norm_num) D.lower D.upper).eval y < 0 ∧
    R/100≤|(D.base.transverse (by norm_num) D.lower D.upper).eval x| ∧
    R/100≤|(D.base.transverse (by norm_num) D.lower D.upper).eval y| ∧
    |(D.base.transverse (by norm_num) D.lower D.upper).eval x|≤8 ∧
    |(D.base.transverse (by norm_num) D.lower D.upper).eval y|≤8 := by
  let Ex := G.excursions_of_rejected he C w hw hwp hwn x hxc hxh
  have Ey : D.base.Excursions (G.narrow_sub_ordered he) y (2*R) (2*R/5) := by
    have e := H.excursions_of_rejected hf E v hv hvp hvn y hyc hyh
    simpa only [hl] using e
  have width : ∀ s ∈ BandTrees.band narrow G.lower,
      ∀ t ∈ BandTrees.band narrow G.lower, |s-t|≤a₂ := by
    intro s hs t ht
    change G.lower ≤ s ∧ s≤G.lower+a₂ at hs
    change G.lower ≤ t ∧ t≤G.lower+a₂ at ht
    exact abs_le.mpr ⟨by linarith [hs.1,ht.2],by linarith [ht.1,hs.2]⟩
  have hclose := D.base_close_of_value x y hhi hcut
  have eqR : R=(1:ℝ)/100000000 := by norm_num [R]
  rw [eqR] at Ex Ey hclose ⊢
  exact D.base.two_side D.ordered D.closed (by norm_num [a₂])
    (G.narrow_sub_ordered he) width x y hlo hhi Ex Ey hclose

end SecondaryGeometry.Group
end PlanarL1.Columns.Model

end

end OAI
