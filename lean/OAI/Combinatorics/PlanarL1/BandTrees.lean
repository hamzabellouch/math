import OAI.Combinatorics.PlanarL1.Tiling
import OAI.Combinatorics.PlanarL1.Ambient

namespace OAI


section

namespace PlanarL1.Columns.Model
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (M : Model n)

namespace BandTrees
variable (P : Parameters.Interpolation) (lo : ℝ)

def band : Set ℝ := Set.Icc lo (lo+P.width)
abbrev Component := (M.activeGraph (band P lo)).ConnectedComponent
noncomputable def root (C : Component M P lo) : Fin n := C.nonempty_supp.choose
lemma root_mem (C : Component M P lo) : root M P lo C ∈ C.supp := C.nonempty_supp.choose_spec

noncomputable def middle : ℝ := lo+P.width/2
lemma middle_mem : middle P lo ∈ band P lo := by
  constructor <;> dsimp [middle] <;> linarith [P.width_pos]

noncomputable def point (C : Component M P lo) (i : C.supp) :
    M.Point (band P lo) (root M P lo C) :=
  ⟨i.val,middle P lo,middle_mem P lo,C.reachable_of_mem_supp (root_mem M P lo C) i.property⟩
noncomputable def base (C : Component M P lo) : M.Point (band P lo) (root M P lo C) :=
  point M P lo C ⟨root M P lo C,root_mem M P lo C⟩
noncomputable def tree (C : Component M P lo) :
    Point.RadialTree (M := M) (J := band P lo) (root := root M P lo C) where
  base := base M P lo C
  δ := P.error/8
  a := P.width
  ζ := P.zeta
  delta_pos := div_pos P.error_pos (by norm_num)
  width_pos := P.width_pos
  zeta_pos := P.zeta_pos
  zeta_lt_one := P.zeta_lt
  width_bound := P.width_bound
  half_width := by
    intro T hT
    change |lo+P.width/2-T|≤P.width/2
    obtain ⟨h1,h2⟩ := hT
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  closed_band := isClosed_Icc
  interval_band := Set.ordConnected_Icc

lemma reachable_mem (C : Component M P lo) {i : Fin n}
    (hi : (M.activeGraph (band P lo)).Reachable (root M P lo C) i) : i ∈ C.supp := by
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
  exact (SimpleGraph.ConnectedComponent.sound hi).symm.trans
    ((SimpleGraph.ConnectedComponent.mem_supp_iff C _).mp (root_mem M P lo C))

/-- Only the radial layers meeting a column occur. No infinite layer family
or arbitrary cut-off is added to the finite random step. -/
noncomputable def levels (C : Component M P lo) (phase width : ℝ) : Finset ℤ :=
  Finset.univ.image (fun i : C.supp => Tiling.index width phase (dist (base M P lo C) (point M P lo C i)))

lemma level_of_mem (C : Component M P lo) {phase width : ℝ} (hw : 0 < width) (k : ℤ)
    {i : Fin n} (hi : i ∈ (base M P lo C).layer (middle P lo) (middle_mem P lo)
      (phase+(k:ℝ)*width) width) : k ∈ levels M P lo C phase width := by
  obtain ⟨hr,hl,hu⟩ := hi
  let u : C.supp := ⟨i,reachable_mem M P lo C hr⟩
  have hind : Tiling.index width phase (dist (base M P lo C) (point M P lo C u))=k := by
    apply Int.floor_eq_iff.mpr
    constructor
    · apply (le_div_iff₀ hw).mpr
      change phase+(k:ℝ)*width≤dist (base M P lo C) (point M P lo C u) at hl
      linarith
    · apply (div_lt_iff₀ hw).mpr
      change dist (base M P lo C) (point M P lo C u)<phase+(k:ℝ)*width+width at hu
      nlinarith
  exact Finset.mem_image.mpr ⟨u,Finset.mem_univ _,hind⟩

lemma same_level (C : Component M P lo) {phase width : ℝ} (hw : 0 < width)
    {k l : ℤ} {i : Fin n}
    (hi : i ∈ (base M P lo C).layer (middle P lo) (middle_mem P lo) (phase+k*width) width)
    (hj : i ∈ (base M P lo C).layer (middle P lo) (middle_mem P lo) (phase+l*width) width) : k=l := by
  obtain ⟨hr,hl,hu⟩ := hi
  obtain ⟨hr',hl',hu'⟩ := hj
  by_contra hn
  rcases lt_or_gt_of_ne hn with hk | hk
  · have hh : (k:ℝ)+1≤l := by exact_mod_cast hk
    have hmul := mul_le_mul_of_nonneg_right hh hw.le
    linarith
  · have hh : (l:ℝ)+1≤k := by exact_mod_cast hk
    have hmul := mul_le_mul_of_nonneg_right hh hw.le
    linarith

abbrev MainIndex (C : Component M P lo) (phase : ℝ) :=
  Σ k : levels M P lo C phase (1/1000), MainCell.Cell (tree M P lo C) (phase+k.val*(1/1000))

noncomputable instance (C : Component M P lo) (phase : ℝ) :
    Fintype (MainIndex M P lo C phase) := Fintype.ofFinite _

noncomputable def anchor (C : Component M P lo) (phase : ℝ) (K : MainIndex M P lo C phase) :
    M.Point (band P lo) (root M P lo C) :=
  let i := K.2.nonempty_supp.choose
  ⟨i.val,middle P lo,middle_mem P lo,i.property.choose⟩

lemma anchor_mem (C : Component M P lo) (phase : ℝ) (K : MainIndex M P lo C phase) :
    (anchor M P lo C phase K).column ∈ ColumnOrder.componentColumns K.2 :=
  ⟨K.2.nonempty_supp.choose,K.2.nonempty_supp.choose_spec,rfl⟩

lemma same_component {V : Type*} {G : SimpleGraph V} {S : Set V}
    {C D : (G.induce S).ConnectedComponent} {i : V}
    (hi : i ∈ ColumnOrder.componentColumns C) (hj : i ∈ ColumnOrder.componentColumns D) : C=D := by
  obtain ⟨u,hu,rfl⟩ := hi
  obtain ⟨v,hv,he⟩ := hj
  have hvu : v=u := Subtype.ext he
  subst v
  exact ((SimpleGraph.ConnectedComponent.mem_supp_iff C u).mp hu).symm.trans
    ((SimpleGraph.ConnectedComponent.mem_supp_iff D u).mp hv)

lemma main_disjoint (C : Component M P lo) (phase : ℝ) {K L : MainIndex M P lo C phase}
    (hne : K≠L) : Disjoint (ColumnOrder.componentColumns K.2) (ColumnOrder.componentColumns L.2) := by
  apply Set.disjoint_left.mpr
  intro i hi hj
  have hk := ColumnOrder.componentColumns_subset K.2 hi
  have hl := ColumnOrder.componentColumns_subset L.2 hj
  have he : K.1=L.1 := Subtype.ext (same_level M P lo C (by norm_num) hk hl)
  obtain ⟨K,Ck⟩ := K
  obtain ⟨L,Cl⟩ := L
  dsimp only at he
  subst L
  have he' : Ck=Cl := same_component hi hj
  subst Cl
  exact hne rfl

end BandTrees
end PlanarL1.Columns.Model

end


section

namespace PlanarL1.Columns.Model
variable {n : ℕ} {M : Model n} {I J : Set ℝ} {i j r s : Fin n}

namespace Path
/-- A short path stays in a height interval containing its entire permitted
height deviation. This restricts the actual switching path, not a metric model. -/
lemma restrict_of_length (p : M.Path I i j) (a b c t : ℝ)
    (hJ : ∀ H, |H-c|≤t → H ∈ J) (hp : |a-c|+p.length a b≤t) :
    ∃ q : M.Path J i j, q.length a b=p.length a b := by
  induction p generalizing a with
  | nil i => exact ⟨.nil i,rfl⟩
  | @cons i u j H hH hs p ih =>
    have htri := abs_sub_le H a c
    rw [abs_sub_comm H a] at htri
    have htail : |H-c|+p.length H b≤t := by
      change |a-c|+(|a-H|+p.length H b)≤t at hp
      linarith
    have hh : H ∈ J := hJ H (by linarith [p.length_nonneg H b])
    obtain ⟨q,hq⟩ := ih H htail
    exact ⟨.cons H hh hs q,by simp only [length,hq]⟩
end Path

namespace Point
lemma dist_coordinates (x y : M.Point J r) (x' y' : M.Point J s)
    (hx : x.column=x'.column) (hX : x.height=x'.height)
    (hy : y.column=y'.column) (hY : y.height=y'.height) : dist x y=dist x' y' := by
  change (⨅ p : M.Path J x.column y.column, p.length x.height y.height)=
    (⨅ p : M.Path J x'.column y'.column, p.length x'.height y'.height)
  rw [hx,hX,hy,hY]

/-- On a ball farther from the band ends than its radius, unrestricted shortest
paths give exact intrinsic distances from its center. -/
lemma local_point (x y : M.Point I r) (x' : M.Point J s)
    (hx : x'.column=x.column) (hX : x'.height=x.height)
    (hI : IsClosed I) (hJI : J ⊆ I) {t : ℝ}
    (hJ : ∀ H, |H-x.height|≤t → H ∈ J) (hxy : dist x y≤t) :
    ∃ y' : M.Point J s, y'.column=y.column ∧ y'.height=y.height ∧ dist x' y'=dist x y := by
  obtain ⟨p,_,hp⟩ := x.exists_shortest hI y
  obtain ⟨q,hq⟩ := p.restrict_of_length x.height y.height x.height t hJ (by simpa [hp] using hxy)
  have hyJ : y.height ∈ J := hJ _ (by
    rw [abs_sub_comm]
    exact (x.height_change_le y).trans hxy)
  let yy : M.Point J s := ⟨y.column,y.height,hyJ,x'.reachable.trans (hx ▸ q.word.reachable)⟩
  refine ⟨yy,rfl,rfl,le_antisymm ?_ ?_⟩
  · have hh := x'.distance_le yy (hx ▸ q)
    change dist x' yy ≤ (hx ▸ q).length x'.height yy.height at hh
    have he : (hx ▸ q).length x'.height yy.height=q.length x.height y.height := by
      obtain ⟨xc,xh,xi,xr⟩ := x'
      dsimp only at hx hX
      subst xc
      subst xh
      rfl
    rw [he,hq,hp] at hh
    exact hh
  · have h := x'.dist_widen_le yy hJI
    have he := dist_coordinates (x'.widen hJI) (yy.widen hJI) x y hx hX rfl rfl
    exact he ▸ h
end Point
end PlanarL1.Columns.Model

end


section

namespace PlanarL1.Columns.Model
open MeasureTheory
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)}

namespace Field
lemma constant_ordered {I : Set ℝ} (c : ℝ) (a b : Fin (k+1)) :
    (constant M I c).OrderedFrom a b := by
  exact ⟨fun _ _ => le_rfl,fun _ _ _ _ _ => le_rfl,fun _ _ _ _ _ => le_rfl⟩
end Field

namespace OrdinaryData
/-- The support required by a secondary group is constructed from the actual
old point source. The comparison outside that source's component is never used. -/
lemma support_at (D : OrdinaryData M) (i : Fin (k+1)) (H : ℝ) (hi : D.Contains i H) :
    ∃ (F : M.Field D.band 1) (a b : Fin (k+1)), F.OrderedFrom a b ∧
      F.value i ⟨H,hi.1⟩=D.comparison.value i ⟨H,hi.1⟩ ∧
      ∀ (j : Fin (k+1)) (T : ℝ) (hj : D.Contains j T),
        F.value j ⟨T,hj.1⟩≤D.comparison.value j ⟨T,hj.1⟩ := by
  by_cases ho : D.origin=none
  ·
    refine ⟨Field.constant M D.band 0,0,0,Field.constant_ordered 0 0 0,?_,?_⟩
    · simp only [comparison,ho]
    · intro j T hj
      simp only [comparison,ho,Field.constant,le_refl]
  · obtain ⟨o,ho⟩ := Option.ne_none_iff_exists'.mp ho
    let w : M.Point D.band o.1 := ⟨i,H,hi.1,hi.2 o.1 o.2 ho⟩
    obtain ⟨F,hord,_,_,hw,hF⟩ := Point.exists_ordered_support D.closed o.2 w
    have hv (j : Fin (k+1)) (T : ℝ) (hj : D.Contains j T) :
        D.comparison.value j ⟨T,hj.1⟩=
          dist o.2 (⟨j,T,hj.1,hj.2 o.1 o.2 ho⟩ : M.Point D.band o.1) := by
      simp only [comparison,ho]
      exact o.2.radialField_eval (⟨j,T,hj.1,hj.2 o.1 o.2 ho⟩ : M.Point D.band o.1)
    refine ⟨F,o.2.column,w.column,hord,?_,?_⟩
    · rw [hv i H hi]
      exact hw
    · intro j T hj
      rw [hv j T hj]
      exact hF (⟨j,T,hj.1,hj.2 o.1 o.2 ho⟩ : M.Point D.band o.1)
end OrdinaryData

namespace Ambient
variable (A : Ambient M)

lemma coordinate_point (x : M.Point Set.univ A.root) : A.point x.column x.height=x := by
  cases x
  rfl

lemma point_dist_same (i : Fin (k+1)) (H T : ℝ) :
    dist (A.point i H) (A.point i T)=|H-T| := A.point_dist i H T

/-- A chart identifier is common on the actual unrestricted closed ball.
The test includes every representative, not merely the original vertices. -/
def Common {ι : Type*} (name : Fin (k+1) → ℝ → ι)
    (x : M.Point Set.univ A.root) (r : ℝ) (a : ι) : Prop :=
  ∀ y : M.Point Set.univ A.root, dist x y≤r → name y.column y.height=a

lemma Common.mono {ι : Type*} {name : Fin (k+1) → ℝ → ι}
    {x : M.Point Set.univ A.root} {r t : ℝ} {a : ι}
    (h : A.Common name x r a) (ht : t≤r) : A.Common name x t a :=
  fun y hy => h y (hy.trans ht)

lemma Common.center {ι : Type*} {name : Fin (k+1) → ℝ → ι}
    {x : M.Point Set.univ A.root} {r : ℝ} {a : ι}
    (h : A.Common name x r a) (hr : 0≤r) : name x.column x.height=a := by
  exact h x (by simpa using hr)

lemma Common.shift {ι : Type*} {name : Fin (k+1) → ℝ → ι}
    {x y : M.Point Set.univ A.root} {r t : ℝ} {a : ι}
    (h : A.Common name x r a) (ht : dist x y+t≤r) : A.Common name y t a := by
  intro z hz
  exact h z ((dist_triangle x y z).trans (by linarith))

end Ambient

namespace OrdinaryState
variable {κ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable (A : Ambient M) (S : OrdinaryState M κ Ω μ)

/-- Band containment follows from a common geometric ball and ordinary
vertical segments, rather than being assumed in a secondary update. -/
lemma ball_band {x : M.Point Set.univ A.root} {a : Fin (S.count+1)} {r : ℝ}
    (h : A.Common S.name x r a) {J : Set ℝ}
    (hJ : ∀ H ∈ J, |x.height-H|≤r) : J ⊆ (S.chart a).band := by
  intro H hH
  have hh := h (A.point x.column H) (by
    conv_lhs => lhs; rw [← A.coordinate_point x]
    rw [A.point_dist]
    exact hJ H hH)
  change S.name x.column H = a at hh
  simpa only [hh] using S.height_in x.column H
end OrdinaryState

namespace BState
variable {κ : ℝ} {lam : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable (A : Ambient M) (S : BState M κ lam Ω μ)

lemma height_named (i : Fin (k+1)) (H : ℝ) (a : Fin (S.count+1))
    (ha : S.name i H=a) : H ∈ (S.chart a).band := by
  subst a
  exact S.height_in i H

lemma uses_named (i : Fin (k+1)) (H : ℝ) (a : Fin (S.count+1))
    (ha : S.name i H=a) : (S.chart a).Uses i := by
  subst a
  exact S.component_in i H

lemma ball_band {x : M.Point Set.univ A.root} {a : Fin (S.count+1)} {r : ℝ}
    (h : A.Common S.name x r a) {J : Set ℝ}
    (hJ : ∀ H ∈ J, |x.height-H|≤r) : J ⊆ (S.chart a).band := by
  intro H hH
  have hh := h (A.point x.column H) (by
    conv_lhs => lhs; rw [← A.coordinate_point x]
    rw [A.point_dist]
    exact hJ H hH)
  exact S.height_named x.column H a hh
end BState
end PlanarL1.Columns.Model

end

end OAI
