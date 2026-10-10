import OAI.Combinatorics.PlanarL1.PairGeometry

namespace OAI


section

namespace PlanarL1.Columns.Model.BandTrees
open Parameters
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {lo : ℝ} {C : Component M broad lo}

noncomputable def radialValue (x : M.Point (band broad lo) (root M broad lo C)) : ℝ :=
  dist (base M broad lo C) (x.withHeight (middle broad lo) (middle_mem broad lo))

/-- All column representatives, not only the chosen one, pass the radial
interior test. The quantification is over zero-distance geometric points. -/
def RadialInterior (width phase : ℝ) (x : M.Point (band broad lo) (root M broad lo C)) : Prop :=
  ∀ y : M.Point (band broad lo) (root M broad lo C), dist x y=0 →
    ¬Tiling.NearBoundary width phase (radialValue y) (width/50)

lemma radial_difference (x y : M.Point (band broad lo) (root M broad lo C)) :
    |radialValue x-radialValue y|≤dist x y+a₁ :=
  (base M broad lo C).radial_difference_le x y (middle_mem broad lo)
    (tree M broad lo C).half_width

lemma radialInterior_of_avoid {width phase : ℝ}
    (x : M.Point (band broad lo) (root M broad lo C))
    (hn : ¬Tiling.NearBoundary width phase (radialValue x) (width/50+a₁)) :
    RadialInterior width phase x := by
  intro y hy hn'
  have hd := radial_difference y x
  rw [dist_comm y x,hy,zero_add] at hd
  exact hn (hn'.perturb.mono (by linarith))

/-- Intrinsic zero-distance representatives are exactly enough: any other
unrestricted representative localizes into the same broad component. -/
lemma RadialInterior.ambient (A : Ambient M) {width phase : ℝ}
    {x : M.Point (band broad lo) (root M broad lo C)} (h : RadialInterior width phase x)
    (y : M.Point Set.univ A.root) (hy : dist (A.point x.column x.height) y=0) :
    ∃ y' : M.Point (band broad lo) (root M broad lo C),
      y'.column=y.column ∧ y'.height=y.height ∧
      ¬Tiling.NearBoundary width phase (radialValue y') (width/50) := by
  obtain ⟨y',hi,hH,hd⟩ := Point.local_point (A.point x.column x.height) y x rfl rfl
    isClosed_univ (Set.subset_univ _) (t := 0) (by
      intro H hH
      have he : H=x.height := sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hH (abs_nonneg _)))
      simpa only [he] using x.inBand) hy.le
  exact ⟨y',hi,hH,h y' (hd.trans hy)⟩

lemma radialInterior_padding {width phase : ℝ}
    (hw : 0<width) (hsmall : 2*a₁<width/100)
    (x : M.Point (band broad lo) (root M broad lo C)) (hi : RadialInterior width phase x)
    (K : RadialIndex M broad lo C width phase)
    (hx : x.column ∈ ColumnOrder.componentColumns K.2) :
    phase+(K.1.val:ℝ)*width+width/100+2*a₁<radialValue x ∧
    radialValue x<phase+(K.1.val:ℝ)*width+width-width/100-2*a₁ := by
  have hl := ColumnOrder.componentColumns_subset K.2 hx
  have he : Tiling.index width phase (radialValue x)=K.1.val :=
    Tiling.index_eq_of_mem_lt hw _ hl.2.1 (by
      have hu : radialValue x<phase+(K.1.val:ℝ)*width+width := hl.2.2
      nlinarith [hu])
  have hp := Tiling.padded_of_avoid hw (hi x (dist_self _))
  rw [Tiling.Padded,he] at hp
  exact ⟨by linarith [hp.1],by linarith [hp.2]⟩

end PlanarL1.Columns.Model.BandTrees

namespace PlanarL1.FiniteRandom
open Parameters Tiling

/-- Two canonical representatives, possibly in the same component, suffice
for the source 0.081 radial allowance. No count of columns is involved. -/
lemma radial_pair_probability {I : Type*} [Fintype I] [DecidableEq I]
    (m : ℕ) (hm : 10000 ≤ m) (i j : I) (x y : ℝ) {width : ℝ}
    (hw : 0<width) (hsmall : a₁≤width/100000) :
    prob (fun ω : I → Fin (m+1) =>
      NearBoundary width (width/m*(ω i).val) x (width/50+a₁) ∨
      NearBoundary width (width/m*(ω j).val) y (width/50+a₁)) ≤81/1000 := by
  have hm0 : 0 < m := by omega
  have hmR : (10000:ℝ) ≤ m := by exact_mod_cast hm
  have hmesh : width/m≤width/10000 := div_le_div_of_nonneg_left hw.le (by norm_num) hmR
  have hb : (2*(width/50+a₁)+2*width/m)/width≤81/2000 := by
    apply (div_le_iff₀ hw).mpr
    rw [mul_div_assoc]
    linarith
  have hp (h : ℝ) := (periodic_probability m hm0 hw
    (show 0≤width/50+a₁ by have ha := interpolationA.2.1; positivity) h).trans hb
  have h₁ := prob_eval_bound i (fun r : Fin (m+1) =>
    NearBoundary width (width/m*r.val) x (width/50+a₁)) (hp x)
  have h₂ := prob_eval_bound j (fun r : Fin (m+1) =>
    NearBoundary width (width/m*r.val) y (width/50+a₁)) (hp y)
  exact (prob_or_le _ _).trans (by linarith)

end PlanarL1.FiniteRandom

end



section

namespace PlanarL1.Columns.Model.VertexBands
open Parameters
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {V : Type*}
variable (A : Ambient M) (v : V → M.Point Set.univ A.root)
variable (L U : ℝ) (hv : ∀ x, (v x).height ∈ Set.Icc L U)

noncomputable def bandIndex (q : ℝ) (x : V) : MainFamily.BandIndex q L U :=
  ⟨Tiling.index a₁ q (v x).height,(Tiling.mem_processed interpolationA.2.1 q L U _).mpr
    ⟨(v x).height,Tiling.mem_band_index interpolationA.2.1 q _,hv x⟩⟩
noncomputable def lower (q : ℝ) (x : V) := MainFamily.lower q L U (bandIndex A v L U hv q x)
noncomputable def component (q : ℝ) (x : V) :
    BandTrees.Component M broad (lower A v L U hv q x) :=
  (M.activeGraph (BandTrees.band broad (lower A v L U hv q x))).connectedComponentMk (v x).column
noncomputable def bandComponent (q : ℝ) (x : V) : MainFamily.BandComponent (M := M) q L U :=
  ⟨bandIndex A v L U hv q x,component A v L U hv q x⟩
lemma height_mem (q : ℝ) (x : V) : (v x).height ∈ BandTrees.band broad (lower A v L U hv q x) := by
  have h := Tiling.mem_band_index interpolationA.2.1 q (v x).height
  change q+(Tiling.index a₁ q (v x).height:ℝ)*a₁≤(v x).height ∧
    (v x).height≤q+(Tiling.index a₁ q (v x).height:ℝ)*a₁+a₁
  constructor <;> dsimp [Tiling.band] at h <;> linarith [h.1,h.2]
noncomputable def point (q : ℝ) (x : V) :
    M.Point (BandTrees.band broad (lower A v L U hv q x))
      (BandTrees.root M broad (lower A v L U hv q x) (component A v L U hv q x)) where
  column := (v x).column
  height := (v x).height
  inBand := height_mem A v L U hv q x
  reachable := (component A v L U hv q x).reachable_of_mem_supp
    (BandTrees.root_mem _ _ _ _) rfl

variable {L U hv}
noncomputable def radial (q : ℝ) (width : ℝ)
    (phase : MainFamily.BandComponent (M := M) q L U → ℝ) (x : V) : Prop :=
  BandTrees.RadialInterior width (phase (bandComponent A v L U hv q x))
    (point A v L U hv q x)

/-- Exactly the literal vertex interior predicate. Narrow containment follows
from broad height padding and is included below as a checked consequence. -/
def Interior (q p : ℝ) (phaseD phaseG : MainFamily.BandComponent (M := M) q L U → ℝ)
    (x : V) : Prop :=
  Tiling.Padded a₁ q (v x).height (a₁/10) ∧
  Tiling.Padded a₂ p (v x).height (a₂/10) ∧
  radial A v (hv := hv) q D phaseD x ∧ radial A v (hv := hv) q g phaseG x

lemma Interior.narrow_sub {q p : ℝ}
    {phaseD phaseG : MainFamily.BandComponent (M := M) q L U → ℝ} {x : V}
    (h : Interior A v (hv := hv) q p phaseD phaseG x) :
    Tiling.band a₂ p (Tiling.index a₂ p (v x).height) ⊆
      BandTrees.band broad (lower A v L U hv q x) := by
  have hs := Tiling.narrow_contained (p := p) h.1
  convert hs using 1
  ext H
  simp only [BandTrees.band,lower,MainFamily.lower,bandIndex,Tiling.band,Set.mem_Icc]
  change (_≤H ∧ H≤q+(Tiling.index a₁ q (v x).height:ℝ)*a₁+a₁) ↔
    (_≤H ∧ H≤q+((Tiling.index a₁ q (v x).height:ℝ)+1)*a₁)
  ring_nf

end PlanarL1.Columns.Model.VertexBands

namespace PlanarL1.Tiling
lemma same_index_of_padded {a q h x t : ℝ} (ha : 0<a)
    (hp : Padded a q h t) (hx : |x-h|≤t) : index a q x=index a q h := by
  obtain ⟨hl,hu⟩ := abs_le.mp hx
  exact index_eq_of_mem_lt ha _ (by linarith [hp.1]) (by linarith [hp.2])
end PlanarL1.Tiling

end



section

namespace PlanarL1.Execution
lemma prob_bind_pure {α β : Type*} (E : Execution α) (f : α → β) (P : β → Prop) :
    (E.bind (fun x => .pure (f x))).prob P=E.prob (fun x => P (f x)) := by
  rw [prob_bind]
  rfl
end PlanarL1.Execution

namespace PlanarL1.Columns.Model.VertexBands
open Parameters FiniteRandom
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {V : Type*}
variable (A : Ambient M) (v : V → M.Point Set.univ A.root)
variable {L U : ℝ} (hv : ∀ x, (v x).height ∈ Set.Icc L U)

abbrev HeightChoices (m : ℕ) := Fin (m+1) × Fin (m+1)
noncomputable def shift (m : ℕ) (width : ℝ) (i : Fin (m+1)) : ℝ := width/m*i.val
abbrev RadialChoices (m : ℕ) (q L U : ℝ) (M : Model (k+1)) :=
  (MainFamily.BandComponent (M := M) q L U → Fin (m+1)) ×
  (MainFamily.BandComponent (M := M) q L U → Fin (m+1))
abbrev Choices (m : ℕ) (L U : ℝ) (M : Model (k+1)) :=
  Σ h : HeightChoices m, RadialChoices m (shift m a₁ h.1) L U M
noncomputable def phase {m : ℕ} {q L U : ℝ} (width : ℝ)
    (r : MainFamily.BandComponent (M := M) q L U → Fin (m+1)) :
    MainFamily.BandComponent (M := M) q L U → ℝ := fun b => shift m width (r b)

noncomputable def geometricExecution (m : ℕ) (L U : ℝ) (M : Model (k+1)) :
    Execution (Choices m L U M) :=
  Execution.uniform.bind (fun h : HeightChoices m =>
    Execution.uniform.bind (fun r : RadialChoices m (shift m a₁ h.1) L U M =>
      .pure ⟨h,r⟩))

def InteriorAt {m : ℕ} (c : Choices m L U M) (x : V) : Prop :=
  Interior A v (hv := hv) (shift m a₁ c.1.1) (shift m a₂ c.1.2)
    (phase D c.2.1) (phase g c.2.2) x

lemma radial_pair_failure (m : ℕ) (hm : 10000 ≤ m) (q : ℝ) (x y : V)
    {width : ℝ} (hw : 0<width) (hs : a₁≤width/100000) :
    prob (fun r : MainFamily.BandComponent (M := M) q L U → Fin (m+1) =>
      ¬(radial A v (hv := hv) q width (phase width r) x ∧
        radial A v (hv := hv) q width (phase width r) y))≤81/1000 := by
  let i := bandComponent A v L U hv q x
  let j := bandComponent A v L U hv q y
  let X := BandTrees.radialValue (point A v L U hv q x)
  let Y := BandTrees.radialValue (point A v L U hv q y)
  apply (prob_mono (P := fun r => ¬(radial A v (hv := hv) q width (phase width r) x ∧
    radial A v (hv := hv) q width (phase width r) y))
    (Q := fun r => Tiling.NearBoundary width (width/m*(r i).val) X (width/50+a₁) ∨
      Tiling.NearBoundary width (width/m*(r j).val) Y (width/50+a₁)) ?_).trans
    (radial_pair_probability m hm i j X Y hw hs)
  intro r hr
  by_contra hn
  push Not at hn
  exact hr ⟨BandTrees.radialInterior_of_avoid _ hn.1,BandTrees.radialInterior_of_avoid _ hn.2⟩

lemma radial_both_failure (m : ℕ) (hm : 10000 ≤ m) (q : ℝ) (x y : V) :
    prob (fun r : RadialChoices m q L U M =>
      ¬(radial A v (hv := hv) q D (phase D r.1) x ∧
        radial A v (hv := hv) q D (phase D r.1) y ∧
        radial A v (hv := hv) q g (phase g r.2) x ∧
        radial A v (hv := hv) q g (phase g r.2) y))≤81/500 := by
  let P := fun r : RadialChoices m q L U M =>
    ¬(radial A v (hv := hv) q D (phase D r.1) x ∧ radial A v (hv := hv) q D (phase D r.1) y)
  let Q := fun r : RadialChoices m q L U M =>
    ¬(radial A v (hv := hv) q g (phase g r.2) x ∧ radial A v (hv := hv) q g (phase g r.2) y)
  have hp : prob P≤81/1000 := prob_prod_bound_left P (fun _ =>
    radial_pair_failure A v hv m hm q x y (width := D) (by norm_num [D]) (by norm_num [a₁,D]))
  have hq : prob Q≤81/1000 := prob_prod_bound Q (fun _ =>
    radial_pair_failure A v hv m hm q x y (width := g) (by norm_num [g]) (by norm_num [a₁,g]))
  apply (prob_mono (Q := fun r => P r ∨ Q r) ?_).trans ((prob_or_le P Q).trans (by linarith))
  intro r hr
  by_contra hn
  have hP : ¬P r := (not_or.mp hn).1
  have hQ : ¬Q r := (not_or.mp hn).2
  exact hr ⟨(not_not.mp hP).1,(not_not.mp hP).2,(not_not.mp hQ).1,(not_not.mp hQ).2⟩

/-- A literal finite sequence of shifts followed by component-indexed radial
origins. Component types may depend on the height shifts; using bind avoids a
spurious uniform law on a dependent sum. -/
lemma interior_pair_probability (m : ℕ) (hm : 10000 ≤ m) (x y : V)
    (hd : |(v y).height-(v x).height|≤a₂/10000) :
    1/4≤(geometricExecution m L U M).prob
      (fun c => InteriorAt A v hv c x ∧ InteriorAt A v hv c y) := by
  let H := fun h : HeightChoices m =>
    Tiling.Padded a₁ (shift m a₁ h.1) (v x).height (a₁/10) ∧
    Tiling.Padded a₁ (shift m a₁ h.1) (v y).height (a₁/10) ∧
    Tiling.Padded a₂ (shift m a₂ h.2) (v x).height (a₂/10) ∧
    Tiling.Padded a₂ (shift m a₂ h.2) (v y).height (a₂/10)
  let P := fun h : HeightChoices m => ¬(Tiling.Padded a₁ (shift m a₁ h.1) (v x).height (a₁/10) ∧
    Tiling.Padded a₁ (shift m a₁ h.1) (v y).height (a₁/10))
  let Q := fun h : HeightChoices m => ¬(Tiling.Padded a₂ (shift m a₂ h.2) (v x).height (a₂/10) ∧
    Tiling.Padded a₂ (shift m a₂ h.2) (v y).height (a₂/10))
  have hp : prob P≤21/100 := prob_prod_bound_left _ (fun _ =>
    Tiling.height_pair_probability m hm interpolationA.2.1 (by norm_num [a₁,a₂]) hd)
  have hq : prob Q≤21/100 := prob_prod_bound _ (fun _ =>
    Tiling.height_pair_probability m hm interpolationB.2.1 le_rfl hd)
  have hheight : Execution.uniform.prob (fun h : HeightChoices m => ¬H h)≤21/50 := by
    rw [Execution.prob_uniform]
    apply (prob_mono (Q := fun h => P h ∨ Q h) ?_).trans ((prob_or_le P Q).trans (by linarith))
    intro h hh
    by_contra hn
    have hP : ¬P h := (not_or.mp hn).1
    have hQ : ¬Q h := (not_or.mp hn).2
    exact hh ⟨(not_not.mp hP).1,(not_not.mp hP).2,(not_not.mp hQ).1,(not_not.mp hQ).2⟩
  have hl := Execution.conditional_loss (Execution.uniform (α := HeightChoices m))
    (fun h => Execution.uniform.bind (fun r : RadialChoices m (shift m a₁ h.1) L U M =>
      .pure (⟨h,r⟩ : Choices m L U M))) H
    (fun c => InteriorAt A v hv c x ∧ InteriorAt A v hv c y)
    (show (0:ℝ)≤81/500 by norm_num) (by
      intro h hh
      rw [Execution.prob_bind_pure,Execution.prob_uniform]
      apply (prob_mono (Q := fun r : RadialChoices m (shift m a₁ h.1) L U M =>
        ¬(radial A v (hv := hv) _ D (phase D r.1) x ∧
          radial A v (hv := hv) _ D (phase D r.1) y ∧
          radial A v (hv := hv) _ g (phase g r.2) x ∧
          radial A v (hv := hv) _ g (phase g r.2) y)) ?_).trans
        (radial_both_failure A v hv m hm _ x y)
      intro r hr hs
      dsimp [InteriorAt,Interior] at hr
      exact hr ⟨⟨hh.1,hh.2.2.1,hs.1,hs.2.2.1⟩,⟨hh.2.1,hh.2.2.2,hs.2.1,hs.2.2.2⟩⟩)
  change (geometricExecution m L U M).prob
    (fun c => ¬(InteriorAt A v hv c x ∧ InteriorAt A v hv c y))≤_ at hl
  rw [Execution.prob_compl] at hl
  linarith

end PlanarL1.Columns.Model.VertexBands

end



section

namespace PlanarL1.Columns.Model.PairGeometry
open Parameters MeasureTheory VertexTests
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω} {ν : Measure Ξ}
variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)
variable (SB : BState M kappaB SecondaryGeometry.Group.lam Ξ ν)
variable (v : V → M.Point Set.univ A.root)
variable {L U : ℝ} (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable (q p : ℝ) (phaseD phaseG : MainFamily.BandComponent (M := M) q L U → ℝ)

noncomputable def narrowLower (x : V) : ℝ := p+(Tiling.index a₂ p (v x).height:ℝ)*a₂
lemma narrow_height (x : V) : (v x).height ∈ BandTrees.band narrow (narrowLower A v p x) := by
  have hh := Tiling.mem_band_index interpolationB.2.1 p (v x).height
  change p+(Tiling.index a₂ p (v x).height:ℝ)*a₂≤(v x).height ∧
    (v x).height≤p+(Tiling.index a₂ p (v x).height:ℝ)*a₂+a₂
  constructor <;> dsimp [Tiling.band] at hh <;> linarith [hh.1,hh.2]

variable {q p phaseD phaseG} {x y : V}
variable (he : Eligible A SA SB v x y)
variable (hi : VertexBands.Interior A v (hv := hv) q p phaseD phaseG x)

lemma gcell_exists : ∃ c : BandTrees.RadialIndex M broad (VertexBands.lower A v L U hv q x)
    (VertexBands.component A v L U hv q x) g (phaseG (VertexBands.bandComponent A v L U hv q x)),
    (v x).column ∈ ColumnOrder.componentColumns c.2 :=
  BandTrees.radial_cover (hw := by norm_num [g]) (hi := rfl)

noncomputable def position : SurvivingGroups.Position A SA SB
    (VertexBands.lower A v L U hv q x) (VertexBands.component A v L U hv q x)
    (narrowLower A v p x) (phaseG (VertexBands.bandComponent A v L U hv q x)) where
  point := VertexBands.point A v L U hv q x
  narrow_height := narrow_height A v p x
  cell := (gcell_exists A v hv (q := q) (phaseG := phaseG) (x := x)).choose
  cell_mem := (gcell_exists A v hv (q := q) (phaseG := phaseG) (x := x)).choose_spec
  lower_pad := (BandTrees.radialInterior_padding (by norm_num [g]) (by norm_num [a₁,g])
    (VertexBands.point A v L U hv q x) hi.2.2.2 _
    (gcell_exists A v hv (q := q) (phaseG := phaseG) (x := x)).choose_spec).1
  upper_pad := (BandTrees.radialInterior_padding (by norm_num [g]) (by norm_num [a₁,g])
    (VertexBands.point A v L U hv q x) hi.2.2.2 _
    (gcell_exists A v hv (q := q) (phaseG := phaseG) (x := x)).choose_spec).2
  indexA := indexA A SA v x
  indexB := indexB A SB v x
  commonA := by simpa only [VertexBands.point,A.coordinate_point] using he.1
  commonB := by simpa only [VertexBands.point,A.coordinate_point] using he.2.2.1

variable (hd : dist (v x) (v y)<2)
include hd in
lemma partner_exists : ∃ z : M.Point (SA.chart (indexA A SA v x)).band
    (BandTrees.root M broad (VertexBands.lower A v L U hv q x) (VertexBands.component A v L U hv q x)),
    z.column=(v y).column ∧ z.height=(v y).height ∧
    dist ((position A SA SB v hv he hi).point.widen (position A SA SB v hv he hi).subA) z=
      dist (v x) (v y) := by
  let w := position A SA SB v hv he hi
  apply Point.local_point (v x) (v y) (w.point.widen w.subA) rfl rfl
    isClosed_univ (Set.subset_univ _) (t := 2) ?_ hd.le
  intro H hH
  have hs := SA.ball_band A he.1 (J := {H : ℝ | |H-(v x).height|≤2}) (by
    intro T hT
    rw [abs_sub_comm]
    exact hT.trans (by norm_num))
  exact hs hH

noncomputable def partner : M.Point (SA.chart (indexA A SA v x)).band
    (BandTrees.root M broad (VertexBands.lower A v L U hv q x) (VertexBands.component A v L U hv q x)) :=
  (partner_exists A SA SB v hv he hi hd).choose
lemma partner_column : (partner A SA SB v hv he hi hd).column=(v y).column :=
  (partner_exists A SA SB v hv he hi hd).choose_spec.1
lemma partner_height : (partner A SA SB v hv he hi hd).height=(v y).height :=
  (partner_exists A SA SB v hv he hi hd).choose_spec.2.1
lemma partner_dist : dist ((position A SA SB v hv he hi).point.widen (position A SA SB v hv he hi).subA)
    (partner A SA SB v hv he hi hd)=dist (v x) (v y) :=
  (partner_exists A SA SB v hv he hi hd).choose_spec.2.2

private lemma comparison_transport {D E : OrdinaryData M} (he : D=E)
    (i : Fin (k+1)) (H : ℝ) (hD : H ∈ D.band) (hE : H ∈ E.band) :
    D.comparison.value i ⟨H,hD⟩=E.comparison.value i ⟨H,hE⟩ := by subst E; rfl

lemma partner_value : (SA.chart (indexA A SA v x)).comparison.eval (partner A SA SB v hv he hi hd)=
    ordinaryValue A SA v y := by
  let z := partner A SA SB v hv he hi hd
  have hiZ : z.column=(v y).column := partner_column A SA SB v hv he hi hd
  have hHZ : z.height=(v y).height := partner_height A SA SB v hv he hi hd
  have hHy : (v y).height ∈ (SA.chart (indexA A SA v x)).band := hHZ ▸ z.inBand
  have hcell : (SA.chart (indexA A SA v x)).comparison.eval z=
      (SA.chart (indexA A SA v x)).comparison.value (v y).column ⟨(v y).height,hHy⟩ := by
    change (SA.chart (indexA A SA v x)).comparison.value z.column ⟨z.height,z.inBand⟩=_
    rw [hiZ]
    exact congrArg ((SA.chart (indexA A SA v x)).comparison.value (v y).column) (Subtype.ext hHZ)
  exact hcell.trans (comparison_transport (congrArg SA.chart (he.namesA A SA SB v).symm) _ _ _ _)

lemma position_value : (SA.chart (indexA A SA v x)).comparison.eval
    ((position A SA SB v hv he hi).point.widen (position A SA SB v hv he hi).subA)=ordinaryValue A SA v x := rfl

/-- The actual surviving test is just the two descending-path tests and the
absence of a low separating tip, after the literal earlier tests. -/
def Retained : Prop :=
  Nonempty ((SA.chart (indexA A SA v x)).comparison.BandDescent
    (BandTrees.band broad (VertexBands.lower A v L U hv q x))
    ((position A SA SB v hv he hi).point.widen (position A SA SB v hv he hi).subA) epsilon) ∧
  Nonempty ((SA.chart (indexA A SA v x)).comparison.BandDescent
    (BandTrees.band broad (VertexBands.lower A v L U hv q x)) (partner A SA SB v hv he hi hd) epsilon) ∧
  (SA.chart (indexA A SA v x)).comparison.NoLowCircular
    ((position A SA SB v hv he hi).point.widen (position A SA SB v hv he hi).subA)
    (partner A SA SB v hv he hi hd) (BandTrees.band narrow (narrowLower A v p x)) j

noncomputable def seed (ha : 1≤dist (v x) (v y)) (hc : Cutoffs A SA SB v x y)
    (hr : Retained A SA SB v hv he hi hd) : SurvivingGroups.Seed A SA SB
    (VertexBands.lower A v L U hv q x) (VertexBands.component A v L U hv q x)
    (narrowLower A v p x) (phaseG (VertexBands.bandComponent A v L U hv q x)) where
  toPosition := position A SA SB v hv he hi
  partner := partner A SA SB v hv he hi hd
  descent := hr.1.some
  partner_descent := hr.2.1.some
  apart := by rw [partner_dist]; exact ha
  close := by
    change |(SA.chart (indexA A SA v x)).comparison.eval (partner A SA SB v hv he hi hd)-
      (SA.chart (indexA A SA v x)).comparison.eval
        ((position A SA SB v hv he hi).point.widen (position A SA SB v hv he hi).subA)|≤EA
    rw [partner_value,position_value,abs_sub_comm]
    exact hc.2.1.le
  retained := hr.2.2

end PlanarL1.Columns.Model.PairGeometry

end



section

namespace PlanarL1.Columns.Model.OrdinaryState
open MeasureTheory Parameters
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {M : Model n} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable (S : OrdinaryState M kappaA Ω μ)

/-- Failure of the actual circular low-tip test produces the literal source
certificate, including its tip and measurable positive label mass. -/
lemma low_tip_certificate (a : Fin (S.count+1)) {root : Fin n}
    (x y : M.Point (S.chart a).band root) (lo : ℝ)
    (hx : S.name x.column x.height=a) (hy : S.name y.column y.height=a)
    (hxH : x.height ∈ Set.Icc lo (lo+a₂)) (hyH : y.height ∈ Set.Icc lo (lo+a₂))
    (hclose : |(S.chart a).comparison.eval x-(S.chart a).comparison.eval y| ≤ EA)
    (hnear : ∀ e : M.Point (S.chart a).band root,
      (dist x e ≤ 1 ∨ dist y e ≤ 1) → S.name e.column e.height=a)
    (hf : ¬(S.chart a).comparison.NoLowCircular x y (Set.Icc lo (lo+a₂)) j) :
    ∃ (e : M.Point (S.chart a).band root) (b : Fin n) (E : Set Ω),
      e.height ∈ M.heights e.column b ∧ ¬Consecutive e.column b ∧
      Field.CircularTipSeparates e.column b x.column y.column ∧
      (dist x e ≤ 1 ∨ dist y e ≤ 1) ∧
      MeasurableSet E ∧ kappaA*j/4 ≤ μ.real E ∧
      (∀ ω ∈ E, (S.sets.activity ω).active x.column x.height) ∧
      (∀ ω ∈ E, (S.sets.activity ω).active y.column y.height) ∧
      (∀ ω ∈ E, ¬(S.sets.activity ω).active e.column e.height) := by
  unfold Field.NoLowCircular at hf
  push Not at hf
  obtain ⟨e,b,heH,hlink,hn,hsep,hd,hdrop⟩ := hf
  have hdrop' : (S.chart a).comparison.eval e < (S.chart a).comparison.eval x-j ∨
      (S.chart a).comparison.eval e < (S.chart a).comparison.eval y-j := by
    by_cases h : (S.chart a).comparison.eval e < (S.chart a).comparison.eval x-j
    · exact Or.inl h
    · exact Or.inr (hdrop (le_of_not_gt h))
  obtain ⟨E,hE,hm,hX,hY,hN⟩ := S.barrier_labels a x y e hx hy (hnear e hd) hxH hyH heH hclose hdrop'
  exact ⟨e,b,E,hlink,hn,hsep,hd,hE,hm,hX,hY,hN⟩

lemma barrier_refined_separation [SFinite μ] (a : Fin (S.count+1)) {root : Fin n}
    (o x y e : M.Point (S.chart a).band root) (b : Fin n)
    (hx : S.name x.column x.height=a) (hy : S.name y.column y.height=a)
    (he : S.name e.column e.height=a)
    {lo : ℝ} (hxH : x.height ∈ Set.Icc lo (lo+a₂))
    (hyH : y.height ∈ Set.Icc lo (lo+a₂)) (heH : e.height ∈ Set.Icc lo (lo+a₂))
    (hclose : |(S.chart a).comparison.eval x-(S.chart a).comparison.eval y| ≤ EA)
    (hdrop : (S.chart a).comparison.eval e < (S.chart a).comparison.eval x-j ∨
      (S.chart a).comparison.eval e < (S.chart a).comparison.eval y-j)
    (hlink : e.height ∈ M.heights e.column b) (hn : ¬Consecutive e.column b)
    (hsep : Field.CircularTipSeparates e.column b x.column y.column) :
    kappaA*j/2 ≤ ‖S.sets.refinedMap o x-S.sets.refinedMap o y‖ := by
  obtain ⟨E,hE,hm,hX,hY,hN⟩ := S.barrier_labels a x y e hx hy he hxH hyH heH hclose hdrop
  have h := (S.sets.refinedMap_terminal_circular o x y hlink hn hsep E hE hN hX hY).2
  linarith
end PlanarL1.Columns.Model.OrdinaryState

end



section

namespace PlanarL1.Columns.Model
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {M : Model n} {I J K : Set ℝ} {r s : Fin n}
namespace Point
lemma eq_coordinates (x y : M.Point I r) (hc : x.column=y.column) (hh : x.height=y.height) : x=y := by
  cases x
  cases y
  cases hc
  cases hh
  rfl
end Point
namespace Field
variable {F : M.Field I 1} {ε j : ℝ}
lemma BandDescent.coordinates {x : M.Point I r} {y : M.Point I s}
    (D : F.BandDescent J x ε) (hc : x.column=y.column) (hh : x.height=y.height) :
    Nonempty (F.BandDescent J y ε) := by
  have hr : (M.activeGraph I).Reachable s r := y.reachable.trans (hc ▸ x.reachable).symm
  have he : x.reRoot hr=y := Point.eq_coordinates _ _ hc hh
  exact he ▸ ⟨D.reRoot hr⟩

lemma NoLowCircular.symm {x y : M.Point I r} (h : F.NoLowCircular x y J j) :
    F.NoLowCircular y x J j := by
  intro v b hv hs hn ht hd
  have ht' : CircularTipSeparates v.column b x.column y.column := by
    simpa only [CircularTipSeparates,TipSeparates,or_comm] using ht
  exact (h v b hv hs hn ht' hd.symm).symm

lemma NoLowCircular.coordinates {x y : M.Point I r} {x' y' : M.Point I s}
    (H : F.NoLowCircular x y J j)
    (hxc : x.column=x'.column) (hxh : x.height=x'.height)
    (hyc : y.column=y'.column) (hyh : y.height=y'.height) : F.NoLowCircular x' y' J j := by
  have hr : (M.activeGraph I).Reachable s r := x'.reachable.trans (hxc ▸ x.reachable).symm
  have he : x.reRoot hr=x' := Point.eq_coordinates _ _ hxc hxh
  have hf : y.reRoot hr=y' := Point.eq_coordinates _ _ hyc hyh
  exact he ▸ hf ▸ H.reRoot hr
end Field
namespace OrdinaryData
lemma descent_coordinates {D E : OrdinaryData M} (hDE : D=E) {J K : Set ℝ} (hJK : J=K)
    {r s : Fin n} (x : M.Point D.band r) (y : M.Point E.band s) {ε : ℝ}
    (h : Nonempty (D.comparison.BandDescent J x ε))
    (hc : x.column=y.column) (hh : x.height=y.height) :
    Nonempty (E.comparison.BandDescent K y ε) := by
  subst E
  subst K
  exact h.some.coordinates hc hh
lemma noLow_coordinates {D E : OrdinaryData M} (hDE : D=E) {J K : Set ℝ} (hJK : J=K)
    {r s : Fin n} (x y : M.Point D.band r) (x' y' : M.Point E.band s) {j : ℝ}
    (h : D.comparison.NoLowCircular x y J j)
    (hxc : x.column=x'.column) (hxh : x.height=x'.height)
    (hyc : y.column=y'.column) (hyh : y.height=y'.height) : E.comparison.NoLowCircular x' y' K j := by
  subst E
  subst K
  exact h.coordinates hxc hxh hyc hyh
end OrdinaryData
end PlanarL1.Columns.Model

end



section

namespace PlanarL1.Columns.Model.RetainedSelection
open Parameters MeasureTheory VertexTests
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [Fintype V] [MeasurableSpace Ω] [MeasurableSpace Ξ]
variable {μ : Measure Ω} {ν : Measure Ξ}
variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)
variable (SB : BState M kappaB SecondaryGeometry.Group.lam Ξ ν)
variable (v : V → M.Point Set.univ A.root)
variable (L U : ℝ) (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable (q p : ℝ) (phaseD phaseG : MainFamily.BandComponent (M := M) q L U → ℝ)

/-- A literal surviving partner. This is tested before any group coin or
orientation is drawn, and never asserts success of an update. -/
structure Witness (x : V) where
  other : V
  test : PairTest A SA SB v (x,other)
  cutoffs : Cutoffs A SA SB v x other
  interior : VertexBands.Interior A v (hv := hv) q p phaseD phaseG x
  other_interior : VertexBands.Interior A v (hv := hv) q p phaseD phaseG other
  retained : PairGeometry.Retained A SA SB v hv test.2.2 interior test.2.1

noncomputable def remaining : Finset V :=
  Finset.univ.filter (fun x => Nonempty (Witness A SA SB v L U hv q p phaseD phaseG x))
noncomputable abbrev Endpoint := remaining A SA SB v L U hv q p phaseD phaseG
noncomputable instance : Fintype (Endpoint A SA SB v L U hv q p phaseD phaseG) := Fintype.ofFinite _

variable {L U q p phaseD phaseG}
lemma mem_remaining (x : V) : x ∈ remaining A SA SB v L U hv q p phaseD phaseG ↔
    Nonempty (Witness A SA SB v L U hv q p phaseD phaseG x) := by
  simp only [remaining,Finset.mem_filter,Finset.mem_univ,true_and]
noncomputable def witness (w : Endpoint A SA SB v L U hv q p phaseD phaseG) :
    Witness A SA SB v L U hv q p phaseD phaseG w.val :=
  ((mem_remaining A SA SB v hv w.val).mp w.property).some

/-- Finite processed broad-component/narrow-band blocks. In particular no
infinite family of unused tail bands is randomized. -/
def Block (q p L U : ℝ) := Σ b : MainFamily.BandComponent (M := M) q L U,
  {n : Tiling.processed a₂ p L U //
    Tiling.band a₂ p n.val ⊆ BandTrees.band broad (MainFamily.lower q L U b.1)}
noncomputable instance : Fintype (Block (M := M) q p L U) := by
  unfold Block
  exact Fintype.ofFinite _

namespace Block
variable (b : Block (M := M) q p L U)
noncomputable def lower : ℝ := MainFamily.lower q L U b.1.1
noncomputable def lower₂ : ℝ := p+(b.2.val.val:ℝ)*a₂
lemma sub : BandTrees.band narrow b.lower₂ ⊆ BandTrees.band broad b.lower := by
  change _ ⊆ BandTrees.band broad (MainFamily.lower q L U b.1.1)
  convert b.2.property using 1
  ext H
  simp only [BandTrees.band,lower₂,Tiling.band,Set.mem_Icc]
  change (_≤H ∧ H≤p+(b.2.val.val:ℝ)*a₂+a₂) ↔ (_≤H ∧ H≤p+((b.2.val.val:ℝ)+1)*a₂)
  ring_nf
end Block

noncomputable def block (w : Endpoint A SA SB v L U hv q p phaseD phaseG) : Block (M := M) q p L U :=
  ⟨VertexBands.bandComponent A v L U hv q w.val,
    ⟨⟨Tiling.index a₂ p (v w.val).height,
      (Tiling.mem_processed interpolationB.2.1 p L U _).mpr
        ⟨(v w.val).height,Tiling.mem_band_index interpolationB.2.1 p _,hv w.val⟩⟩,
      (witness A SA SB v hv w).interior.narrow_sub A v⟩⟩

abbrev LocalSeed (b : Block (M := M) q p L U) :=
  SurvivingGroups.Seed A SA SB b.lower b.1.2 b.lower₂ (phaseG b.1)

noncomputable def rawSeed (w : Endpoint A SA SB v L U hv q p phaseD phaseG) :
    LocalSeed A SA SB (phaseG := phaseG) (block A SA SB v hv w) :=
  PairGeometry.seed A SA SB v hv (witness A SA SB v hv w).test.2.2
    (witness A SA SB v hv w).interior (witness A SA SB v hv w).test.2.1
    (witness A SA SB v hv w).test.1 (witness A SA SB v hv w).cutoffs
    (witness A SA SB v hv w).retained

abbrev Slice (b : Block (M := M) q p L U) :=
  {w : Endpoint A SA SB v L U hv q p phaseD phaseG // block A SA SB v hv w=b}
noncomputable def localSeeds (b : Block (M := M) q p L U) (w : Slice A SA SB v hv (phaseD := phaseD) (phaseG := phaseG) b) :
    LocalSeed A SA SB (phaseG := phaseG) b := w.property ▸ rawSeed A SA SB v hv w.val

noncomputable abbrev GroupIndex := Σ b : Block (M := M) q p L U,
  SurvivingGroups.GroupIndex (localSeeds A SA SB v hv (phaseD := phaseD) (phaseG := phaseG) b)
noncomputable instance : Fintype (GroupIndex A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG)) :=
  Fintype.ofFinite _

noncomputable def group (i : GroupIndex A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG)) :
    SecondaryGeometry.Group A SB := SurvivingGroups.group (localSeeds A SA SB v hv i.1) i.1.sub i.2

noncomputable def groupOf (w : Endpoint A SA SB v L U hv q p phaseD phaseG) :
    GroupIndex A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG) :=
  ⟨block A SA SB v hv w,⟨SurvivingGroups.key (localSeeds A SA SB v hv _) ⟨w,rfl⟩,
    Finset.mem_image.mpr ⟨⟨w,rfl⟩,Finset.mem_univ _,rfl⟩⟩⟩

lemma localSeeds_self (w : Endpoint A SA SB v L U hv q p phaseD phaseG) :
    localSeeds A SA SB v hv (block A SA SB v hv w) ⟨w,rfl⟩=rawSeed A SA SB v hv w := rfl

lemma groupOf_seed (w : Endpoint A SA SB v L U hv q p phaseD phaseG) :
    (rawSeed A SA SB v hv w).point ∈ (group A SA SB v hv (groupOf A SA SB v hv w)).seeds := by
  exact (SurvivingGroups.seed_mem _ _).mpr ⟨⟨w,rfl⟩,rfl,rfl⟩

lemma rawSeed_column (w : Endpoint A SA SB v L U hv q p phaseD phaseG) :
    (rawSeed A SA SB v hv w).point.column=(v w.val).column := rfl
lemma rawSeed_height (w : Endpoint A SA SB v L U hv q p phaseD phaseG) :
    (rawSeed A SA SB v hv w).point.height=(v w.val).height := rfl

end PlanarL1.Columns.Model.RetainedSelection

end



section

namespace PlanarL1.Columns.Model.PairGeometry
open Parameters MeasureTheory VertexTests
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω} {ν : Measure Ξ}
variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)
variable (SB : BState M kappaB SecondaryGeometry.Group.lam Ξ ν)
variable (v : V → M.Point Set.univ A.root)
variable {L U : ℝ} (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q p : ℝ} {phaseD phaseG : MainFamily.BandComponent (M := M) q L U → ℝ}
variable {x y : V} (he : Eligible A SA SB v x y)
variable (hi : VertexBands.Interior A v (hv := hv) q p phaseD phaseG x)
variable (hj : VertexBands.Interior A v (hv := hv) q p phaseD phaseG y)
variable (hc : Cutoffs A SA SB v x y) (hd : dist (v x) (v y)<2)

include hi hc in
lemma broad_lower_eq : VertexBands.lower A v L U hv q y=VertexBands.lower A v L U hv q x := by
  have hxy : |(v y).height-(v x).height|≤a₁/10 := by
    rw [abs_sub_comm]
    exact hc.1.le.trans (by norm_num [a₂,a₁])
  have hn := Tiling.same_index_of_padded interpolationA.2.1 hi.1 hxy
  change q+(Tiling.index a₁ q (v y).height:ℝ)*a₁=q+(Tiling.index a₁ q (v x).height:ℝ)*a₁
  rw [hn]

include hi hc in
lemma narrow_lower_eq : narrowLower A v p y=narrowLower A v p x := by
  have hxy : |(v y).height-(v x).height|≤a₂/10 := by
    rw [abs_sub_comm]
    exact hc.1.le.trans (by norm_num [a₂])
  have hn := Tiling.same_index_of_padded interpolationB.2.1 hi.2.1 hxy
  unfold narrowLower
  rw [hn]

include hc in
lemma Retained.symm (hr : Retained A SA SB v hv he hi hd) :
    Retained A SA SB v hv (he.symm A SA SB v) hj (by simpa only [dist_comm] using hd) := by
  have hD : SA.chart (indexA A SA v x)=SA.chart (indexA A SA v y) :=
    congrArg SA.chart (he.namesA A SA SB v).symm
  have hJ : BandTrees.band broad (VertexBands.lower A v L U hv q x)=
      BandTrees.band broad (VertexBands.lower A v L U hv q y) :=
    congrArg (BandTrees.band broad) (broad_lower_eq A SA SB v hv hi hc).symm
  have hK : BandTrees.band narrow (narrowLower A v p x)=BandTrees.band narrow (narrowLower A v p y) :=
    congrArg (BandTrees.band narrow) (narrow_lower_eq A SA SB v hv hi hc).symm
  let he' := he.symm A SA SB v
  have hd' : dist (v y) (v x)<2 := by simpa only [dist_comm] using hd
  have hyc : (partner A SA SB v hv he hi hd).column=
      ((position A SA SB v hv he' hj).point.widen (position A SA SB v hv he' hj).subA).column :=
    partner_column A SA SB v hv he hi hd
  have hyh : (partner A SA SB v hv he hi hd).height=
      ((position A SA SB v hv he' hj).point.widen (position A SA SB v hv he' hj).subA).height :=
    partner_height A SA SB v hv he hi hd
  have hxc : ((position A SA SB v hv he hi).point.widen (position A SA SB v hv he hi).subA).column=
      (partner A SA SB v hv he' hj hd').column :=
    (partner_column A SA SB v hv he' hj hd').symm
  have hxh : ((position A SA SB v hv he hi).point.widen (position A SA SB v hv he hi).subA).height=
      (partner A SA SB v hv he' hj hd').height :=
    (partner_height A SA SB v hv he' hj hd').symm
  exact ⟨OrdinaryData.descent_coordinates hD hJ _ _ hr.2.1 hyc hyh,
    OrdinaryData.descent_coordinates hD hJ _ _ hr.1 hxc hxh,
    OrdinaryData.noLow_coordinates hD hK _ _ _ _ hr.2.2.symm hyc hyh hxc hxh⟩
end PlanarL1.Columns.Model.PairGeometry

end



section

namespace PlanarL1.Columns.Model.Ambient
variable {k : ℕ} {M : Model (k+1)} (A : Ambient M)
lemma coordinate_dist_le {J : Set ℝ} {r : Fin (k+1)} (x y : M.Point J r) :
    dist (A.point x.column x.height) (A.point y.column y.height) ≤ dist x y := by
  calc
    _ = dist (x.widen (Set.subset_univ _)) (y.widen (Set.subset_univ _)) :=
      Point.dist_coordinates _ _ _ _ rfl rfl rfl rfl
    _ ≤ _ := x.dist_widen_le y (Set.subset_univ _)
end PlanarL1.Columns.Model.Ambient

namespace PlanarL1.Columns.Model.PairGeometry
open Parameters MeasureTheory VertexTests
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω} {ν : Measure Ξ}
variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)
variable (SB : BState M kappaB SecondaryGeometry.Group.lam Ξ ν)
variable (v : V → M.Point Set.univ A.root)
variable {L U : ℝ} (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q p : ℝ} {phaseD phaseG : MainFamily.BandComponent (M := M) q L U → ℝ}
variable {x y : V} (he : Eligible A SA SB v x y)
variable (hi : VertexBands.Interior A v (hv := hv) q p phaseD phaseG x)
variable (hc : Cutoffs A SA SB v x y) (hd : dist (v x) (v y)<2)

/-- The source component certificate on literal active labels and an actual
terminal link. Its labels, tip and positive mass are not extra input. -/
def Certificate (b : ℝ) : Prop :=
  ∃ (a c : Fin (k+1)) (H : ℝ) (E : Set Ω),
    H ∈ M.heights a c ∧ ¬Consecutive a c ∧
    Field.CircularTipSeparates a c (v x).column (v y).column ∧
    MeasurableSet E ∧ b ≤ μ.real E ∧
    (∀ ω ∈ E, (SA.sets.activity ω).active (v x).column (v x).height) ∧
    (∀ ω ∈ E, (SA.sets.activity ω).active (v y).column (v y).height) ∧
    (∀ ω ∈ E, ¬(SA.sets.activity ω).active a H)

include hc in
lemma certificate_of_excluded
    (hf : ¬(SA.chart (indexA A SA v x)).comparison.NoLowCircular
      ((position A SA SB v hv he hi).point.widen (position A SA SB v hv he hi).subA)
      (partner A SA SB v hv he hi hd) (BandTrees.band narrow (narrowLower A v p x)) j) :
    Certificate A SA v (x := x) (y := y) (kappaA*j/4) := by
  let u : M.Point (SA.chart (indexA A SA v x)).band
      (BandTrees.root M broad (VertexBands.lower A v L U hv q x) (VertexBands.component A v L U hv q x)) := (position A SA SB v hv he hi).point.widen (position A SA SB v hv he hi).subA
  let z := partner A SA SB v hv he hi hd
  have hxH : u.height ∈ Set.Icc (narrowLower A v p x) (narrowLower A v p x+a₂) :=
    narrow_height A v p x
  have hyH : z.height ∈ Set.Icc (narrowLower A v p x) (narrowLower A v p x+a₂) := by
    have hy := narrow_height A v p y
    rw [narrow_lower_eq A SA SB v hv hi hc] at hy
    simpa only [z,partner_height,BandTrees.band,narrow] using hy
  have hn : SA.name z.column z.height=indexA A SA v x := by
    rw [partner_column,partner_height]
    exact he.namesA A SA SB v
  have hnear (e : M.Point (SA.chart (indexA A SA v x)).band
      (BandTrees.root M broad (VertexBands.lower A v L U hv q x) (VertexBands.component A v L U hv q x)))
      (h : dist u e≤1 ∨ dist z e≤1) : SA.name e.column e.height=indexA A SA v x := by
    rcases h with h | h
    · have hb := (A.coordinate_dist_le u e).trans h
      change dist (A.point (v x).column (v x).height) (A.point e.column e.height)≤1 at hb
      rw [A.coordinate_point] at hb
      exact he.1 _ (hb.trans (by norm_num))
    · have hb := (A.coordinate_dist_le z e).trans h
      rw [partner_column,partner_height,A.coordinate_point] at hb
      exact he.2.1 _ (hb.trans (by norm_num))
  have hclose : |(SA.chart (indexA A SA v x)).comparison.eval u-
      (SA.chart (indexA A SA v x)).comparison.eval z|≤EA := by
    calc
      _ = |ordinaryValue A SA v x-ordinaryValue A SA v y| :=
        congrArg₂ (fun a b : ℝ => |a-b|) (position_value A SA SB v hv he hi)
          (partner_value A SA SB v hv he hi hd)
      _ ≤ _ := hc.2.1.le
  obtain ⟨e,c,E,hlink,hnot,hsep,_,hE,hm,hX,hY,hN⟩ :=
    SA.low_tip_certificate (indexA A SA v x) u z (narrowLower A v p x) rfl hn hxH hyH hclose hnear hf
  refine ⟨e.column,c,e.height,E,hlink,hnot,?_,hE,hm,hX,?_,hN⟩
  · change Field.CircularTipSeparates e.column c (v x).column z.column at hsep
    simpa only [z,partner_column] using hsep
  · simpa only [z,partner_column,partner_height] using hY
end PlanarL1.Columns.Model.PairGeometry

end



section

namespace PlanarL1.Columns.Model.MainFamily
open Parameters MeasureTheory
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*}
variable [MeasurableSpace Ω] {μ : Measure Ω}
variable (A : Ambient M) (S : OrdinaryState M kappaA Ω μ)
variable {q L U : ℝ} (phase : BandComponent (M := M) q L U → ℝ)

/-- The literal radius-five eligibility test suffices for the full closed
one-neighborhood availability of every cell containing this endpoint. -/
lemma available_of_ball5 (c : CellIndex q L U phase) (x : M.Point Set.univ A.root)
    (hx : x.height ∈ domain phase c x.column) {a : Fin (S.count+1)}
    (hname : A.Common S.name x 5 a) : Available A S phase c := by
  refine ⟨a,fun y hy => hname y ?_⟩
  obtain ⟨i,H,hi,hd⟩ := hy
  have hxpoint : A.point x.column x.height=x := A.coordinate_point x
  have hc := cell_diameter A phase c hx hi
  rw [hxpoint] at hc
  have ht := dist_triangle x (A.point i H) y
  rw [dist_comm (A.point i H) y] at ht
  linarith

lemma distinct_cells (x y : M.Point Set.univ A.root)
    (ha : 1≤dist x y) (c d : CellIndex q L U phase)
    (hx : x.height ∈ domain phase c x.column) (hy : y.height ∈ domain phase d y.column) : c≠d := by
  intro he
  subst d
  have h := cell_diameter A phase c hx hy
  rw [A.coordinate_point x,A.coordinate_point y] at h
  linarith

end PlanarL1.Columns.Model.MainFamily

end

end OAI
