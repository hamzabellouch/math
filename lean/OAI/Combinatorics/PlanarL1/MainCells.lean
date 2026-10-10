import OAI.Combinatorics.PlanarL1.Bands
import OAI.Combinatorics.PlanarL1.RadialTree
import OAI.Combinatorics.PlanarL1.Gluing
import OAI.Combinatorics.PlanarL1.Clipping

namespace OAI

section

namespace PlanarL1.Columns.Model

open scoped NNReal
variable {n : ℕ} {M : Model n} {I J : Set ℝ} {root : Fin n}

lemma Field.widen_lipschitz (F : M.Field I 1) (hJI : J ⊆ I) (hJ : IsClosed J) :
    LipschitzWith 1 (fun x : M.Point J root => F.eval (x.widen hJI)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  obtain ⟨p, _, hp⟩ := x.exists_shortest hJ y
  have hf := F.path_bound (p.widen hJI) ⟨x.height,hJI x.inBand⟩ ⟨y.height,hJI y.inBand⟩
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul, Path.length_widen,hp,Field.eval,Point.widen] using hf

namespace MainCell
variable (F : M.Field I 1) (hJI : J ⊆ I)
variable (R : Point.RadialTree (M := M) (J := J) (root := root)) (q : ℝ)
abbrev Cell := ((M.activeGraph J).induce (R.base.layer R.base.height R.base.inBand q (1/1000))).ConnectedComponent
variable (C : Cell R q)

noncomputable def old (x : M.Point J root) : ℝ := F.eval (x.widen hJI)

def boundary : Set (M.Point J root) :=
  {x | x.column ∈ Point.frontier (M := M) (J := J) (ColumnOrder.componentColumns C)}

noncomputable def input (v : M.Point J root) : M.Point J root → ℝ :=
  Clipping.envelope (boundary R q C) (old F hJI) (old F hJI v+1) (1-R.ζ)

noncomputable def proposal (v : M.Point J root) (α : Point.RadialTree.Noise (n := n))
    (E : ℝ) (x : M.Point J root) : ℝ :=
  (R.pasted (input F hJI R q C v) α x).value-4*E

lemma boundary_compact (hJ : IsCompact J) : IsCompact (boundary R q C) :=
  Point.fullColumns_compact hJ _

include R in
lemma old_lipschitz : LipschitzWith 1 (old F hJI : M.Point J root → ℝ) :=
  F.widen_lipschitz hJI R.closed_band

lemma input_lipschitz (hJ : IsCompact J) (v : M.Point J root) :
    R.InputLip (input F hJI R q C v) := by
  let t : ℝ≥0 := ⟨1-R.ζ,by linarith [R.zeta_lt_one]⟩
  have h := Clipping.envelope_lipschitz (boundary_compact R q C hJ)
    (old_lipschitz F hJI R).continuous.continuousOn (old F hJI v+1) t
  intro x y
  exact h.dist_le_mul x y

lemma proposal_accuracy (hJ : IsCompact J) (v x : M.Point J root)
    {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α) {E : ℝ} (hE : 0 ≤ E)
    (hδ : R.δ = E/8) :
    input F hJI R q C v x-5*E ≤ proposal F hJI R q C v α E x ∧
    proposal F hJI R q C v α E x ≤ input F hJI R q C v x-3*E := by
  have ha := abs_le.mp (R.pasted_accuracy (input_lipschitz F hJI R q C hJ v) hα x)
  dsimp only [proposal]
  rw [hδ] at ha
  constructor <;> linarith

lemma proposal_lipschitz (v : M.Point J root) {α : Point.RadialTree.Noise (n := n)}
    (hα : R.NoiseBounds α) (E : ℝ) : LipschitzWith 1 (proposal F hJI R q C v α E) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [proposal,dist_sub_right] using (R.pasted_lipschitz (input F hJI R q C v) hα).dist_le_mul x y

lemma frontier_margin (hJ : IsCompact J) (v : M.Point J root)
    {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α) {E : ℝ} (hE : 0 ≤ E)
    (hδ : R.δ = E/8) {z : M.Point J root} (hz : z ∈ boundary R q C) :
    proposal F hJI R q C v α E z ≤ old F hJI z-3*E := by
  have hf := Clipping.envelope_frontier (boundary_compact R q C hJ)
    (old_lipschitz F hJI R).continuous.continuousOn (old F hJI v+1) (1-R.ζ) hz
  have hp := (proposal_accuracy F hJI R q C hJ v z hα hE hδ).2
  change input F hJI R q C v z ≤ old F hJI z at hf
  linarith

lemma variation (hthin : R.a ≤ (1/1000:ℝ)/1000) (v x : M.Point J root)
    (hv : v.column ∈ ColumnOrder.componentColumns C)
    (hx : x.column ∈ ColumnOrder.componentColumns C) :
    |old F hJI v-old F hJI x| ≤ (1:ℝ)/100 := by
  have hd := R.base.radial_cell_diameter R.closed_band R.base.inBand
    R.width_pos hthin R.half_width C v x hv hx
  have hf := (old_lipschitz F hJI R).dist_le_mul v x
  rw [Real.dist_eq,NNReal.coe_one,one_mul] at hf
  exact hf.trans (by linarith)

lemma movement (hJ : IsCompact J) (hthin : R.a ≤ (1/1000:ℝ)/1000)
    (v x : M.Point J root) (hv : v.column ∈ ColumnOrder.componentColumns C)
    (hx : x.column ∈ ColumnOrder.componentColumns C)
    {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α) {E : ℝ} (hE : 0 ≤ E)
    (hδ : R.δ = E/8) (H : M.Point J root → ℝ) :
    0 ≤ Clipping.clip (old F hJI) (proposal F hJI R q C v α E) H x-old F hJI x ∧
    Clipping.clip (old F hJI) (proposal F hJI R q C v α E) H x-old F hJI x ≤ 1+(1:ℝ)/100 := by
  apply Clipping.clip_movement (by norm_num)
  have hf := (proposal_accuracy F hJI R q C hJ v x hα hE hδ).2
  have hc := Clipping.envelope_le_cap (boundary R q C) (old F hJI) (old F hJI v+1) (1-R.ζ) x
  have hvx := (abs_le.mp (variation F hJI R q C hthin v x hv hx)).2
  change input F hJI R q C v x ≤ old F hJI v+1 at hc
  linarith

/-- The literal main test: the proposal is the actual interpolated compact
frontier envelope, and failure to raise constructs an attaining path in J. -/
lemma raise_or_descent (hJ : IsCompact J) (v w : M.Point J root)
    (hv : v.column ∈ ColumnOrder.componentColumns C)
    (hw : w.column ∈ ColumnOrder.componentColumns C)
    {ε : ℝ} (hε : 0 < ε) (hεsmall : ε ≤ (1:ℝ)/100)
    (hζ : R.ζ = ε/100) (hδ : R.δ = (ε/1000)/8)
    {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α)
    (H : M.Point J root → ℝ) (hH : old F hJI v+2 ≤ H w)
    (hlow : q+(1:ℝ)/100000+2*R.a < dist R.base (w.withHeight R.base.height R.base.inBand))
    (hupp : dist R.base (w.withHeight R.base.height R.base.inBand) < q+(1:ℝ)/1000-(1:ℝ)/100000-2*R.a) :
    old F hJI w+2*(ε/1000) <
        Clipping.clip (old F hJI) (proposal F hJI R q C v α (ε/1000)) H w ∨
      Nonempty (F.BandDescent J (w.widen hJI) ε) := by
  have hthin : R.a ≤ (1/1000:ℝ)/1000 := by
    have hb := R.width_bound
    have hm := mul_lt_mul_of_pos_right R.zeta_lt_one R.delta_pos
    rw [hδ] at hb hm
    nlinarith
  have hvw := abs_le.mp (variation F hJI R q C hthin v w hv hw)
  have hrad : ∀ z ∈ boundary R q C, (0.00001:ℝ) ≤ dist w z ∧ dist w z ≤ 0.02 := by
    intro z hz
    have hl := R.base.radial_frontier_distance w z R.base.inBand R.half_width C hlow hupp hz
    have hu := R.base.radial_cell_diameter R.closed_band R.base.inBand R.width_pos hthin
      R.half_width C w z hw hz.1
    constructor <;> linarith
  have hraise := Clipping.raise_or_descending_endpoint (H := H) (boundary_compact R q C hJ)
    (old_lipschitz F hJI R).continuous.continuousOn w (old F hJI v+1) R.ζ (ε/1000) ε
    (proposal_accuracy F hJI R q C hJ v w hα (by linarith) hδ).1
    (by linarith) (by linarith) hrad R.zeta_pos.le (by rw [hζ]; linarith)
  rcases hraise with hh | ⟨z,hz,hlo,hup,hdrop⟩
  · exact Or.inl hh
  · right
    obtain ⟨p,_,hp⟩ := w.exists_shortest R.closed_band z
    refine ⟨{
      start_in := w.inBand
      target := z.widen hJI
      target_in := z.inBand
      path := p
      shortest := ?_
      lower := ?_
      upper := ?_
      drop := ?_ }⟩
    · intro p'
      change p.length w.height z.height ≤ p'.length w.height z.height
      rw [hp]
      exact w.distance_le z p'
    · change (1:ℝ)/100000 ≤ p.length w.height z.height
      rw [hp]
      linarith
    · change p.length w.height z.height ≤ (1:ℝ)/50
      rw [hp]
      linarith
    · change old F hJI z ≤ old F hJI w-p.length w.height z.height+ε
      rwa [hp]

end MainCell
end PlanarL1.Columns.Model


end

section

namespace PlanarL1.Columns.Model.MainCell
open scoped NNReal
open Set MeasureTheory
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {M : Model n} {I J : Set ℝ} {root : Fin n}
variable (F : M.Field I 1) (hJI : J ⊆ I)
variable (R : Point.RadialTree (M := M) (J := J) (root := root)) (q : ℝ)
variable (C : Cell R q)

noncomputable def replacement (v : M.Point J root)
    (α : Point.RadialTree.Noise (n := n)) (E β lo : ℝ) (x : M.Point J root) : ℝ :=
  Clipping.clip (old F hJI) (proposal F hJI R q C v α E)
    (fun x => Clipping.heightShield lo R.a (old F hJI v) β x.height) x

noncomputable def replacementConstant : ℝ≥0 :=
  max 1 ⟨3/(9*R.a/100), by positivity [R.width_pos]⟩

lemma replacement_lipschitz (v : M.Point J root)
    {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α) (E β lo : ℝ) :
    LipschitzWith (replacementConstant R) (replacement F hJI R q C v α E β lo) := by
  apply Clipping.clip_lipschitz
  · exact (old_lipschitz F hJI R).weaken (le_max_left _ _)
  · exact (proposal_lipschitz F hJI R q C v hα E).weaken (le_max_left _ _)
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    have h := (Clipping.heightShield_lipschitz lo (old F hJI v) β R.width_pos).dist_le_mul
      x.height y.height
    have hheight := x.height_change_le y
    change |x.height-y.height| ≤ dist x y at hheight
    change dist _ _ ≤ (replacementConstant R : ℝ)*dist x y
    change dist _ _ ≤ (3/(9*R.a/100))*dist x.height y.height at h
    rw [Real.dist_eq x.height y.height] at h
    exact h.trans ((mul_le_mul_of_nonneg_left hheight (by positivity [R.width_pos])).trans
      (mul_le_mul_of_nonneg_right (le_max_right (1:ℝ) (3/(9*R.a/100))) dist_nonneg))

lemma replacement_switch (v x y : M.Point J root)
    {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α) (E β lo : ℝ)
    (he : x.height = y.height) (hs : x.height ∈ M.heights x.column y.column) :
    replacement F hJI R q C v α E β lo x = replacement F hJI R q C v α E β lo y := by
  have hd := x.dist_le_switch y x.inBand hs
  rw [he,sub_self,abs_zero,add_zero] at hd
  have hh := (replacement_lipschitz F hJI R q C v hα E β lo).dist_le_mul x y
  rw [le_antisymm hd dist_nonneg,mul_zero] at hh
  exact dist_le_zero.mp hh

lemma replacement_frontier (hJ : IsCompact J) (v x : M.Point J root)
    {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α)
    {E : ℝ} (hE : 0 ≤ E) (hδ : R.δ = E/8) (β lo : ℝ)
    (hx : x ∈ boundary R q C) :
    replacement F hJI R q C v α E β lo x = old F hJI x := by
  apply Clipping.clip_unchanged
  left
  have h := frontier_margin F hJI R q C hJ v hα hE hδ hx
  linarith

lemma replacement_endpoint (hthin : R.a ≤ (1/1000:ℝ)/1000)
    (v x : M.Point J root) (hv : v.column ∈ ColumnOrder.componentColumns C)
    (hx : x.column ∈ ColumnOrder.componentColumns C)
    (α : Point.RadialTree.Noise (n := n)) (E β lo : ℝ) (hβ : β ≤ (1:ℝ)/100)
    (he : x.height = lo ∨ x.height = lo+R.a) :
    replacement F hJI R q C v α E β lo x = old F hJI x := by
  apply Clipping.clip_unchanged
  right
  have h := (abs_le.mp (variation F hJI R q C hthin v x hv hx)).2
  have hh : Clipping.heightShield lo R.a (old F hJI v) β x.height = old F hJI v-1+β := by
    rcases he with he | he
    · exact Clipping.heightShield_left (by rw [he])
    · exact Clipping.heightShield_right (by rw [he])
  rw [hh]
  linarith


lemma scaled_replacement_constant (ha : R.a ≤ 1) :
    (R.a/1000000) * (replacementConstant R : ℝ) ≤ 1 := by
  change (R.a/1000000) * max 1 (3/(9*R.a/100)) ≤ 1
  rw [mul_max_of_nonneg (1:ℝ) (3/(9*R.a/100)) (by positivity [R.width_pos])]
  apply max_le
  · linarith
  · have hpos : 0 < 9*R.a/100 := by positivity [R.width_pos]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hpos).mpr
    nlinarith [R.width_pos]

/-- Actual closed full-column update domain. -/
def domain (i : Fin n) : Set ℝ :=
  if i ∈ ColumnOrder.componentColumns C then J else ∅

lemma mem_domain {i : Fin n} {H : ℝ} :
    H ∈ domain R q C i ↔ i ∈ ColumnOrder.componentColumns C ∧ H ∈ J := by
  by_cases hi : i ∈ ColumnOrder.componentColumns C <;> simp [domain,hi]

lemma closed_domain (i : Fin n) : IsClosed (domain R q C i) := by
  by_cases hi : i ∈ ColumnOrder.componentColumns C <;>
    simp only [domain,hi,ite_true,ite_false]
  · exact R.closed_band
  · exact isClosed_empty

/-- The actual point in the broad component underlying a cell-domain point. -/
def cellPoint (i : Fin n) (H : ℝ) (h : H ∈ domain R q C i) : M.Point J root :=
  ⟨i,H,((mem_domain R q C).mp h).2,
    (ColumnOrder.componentColumns_subset C ((mem_domain R q C).mp h).1).choose⟩

noncomputable def converted (v : M.Point J root)
    (α : Point.RadialTree.Noise (n := n)) (E β lo c η κ : ℝ) (i : Fin n) (H : ℝ) : ℝ :=
  if h : H ∈ domain R q C i then
    κ * (c + η * replacement F hJI R q C v α E β lo (cellPoint R q C i H h)) else 0

lemma converted_on (v : M.Point J root)
    (α : Point.RadialTree.Noise (n := n)) (E β lo c η κ : ℝ) {i : Fin n} {H : ℝ}
    (h : H ∈ domain R q C i) :
    converted F hJI R q C v α E β lo c η κ i H =
    κ * (c + η * replacement F hJI R q C v α E β lo (cellPoint R q C i H h)) := by
  simp only [converted,dite_eq_left h]

lemma converted_lipschitz (v : M.Point J root)
    {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α) (E β lo c η κ : ℝ)
    (hη : |η| = 1) (hκ : 0 ≤ κ) (hκK : κ*(replacementConstant R : ℝ) ≤ 1) (i : Fin n) :
    LipschitzOnWith 1 (converted F hJI R q C v α E β lo c η κ i) (domain R q C i) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro H hH T hT
  rw [converted_on F hJI R q C v α E β lo c η κ hH,
    converted_on F hJI R q C v α E β lo c η κ hT]
  let x := cellPoint R q C i H hH
  let y := cellPoint R q C i T hT
  have h := (replacement_lipschitz F hJI R q C v hα E β lo).dist_le_mul x y
  rw [x.dist_same_column y rfl] at h
  simp only [Real.dist_eq,NNReal.coe_one,one_mul]
  change |κ*(c+η*replacement F hJI R q C v α E β lo x)-
    κ*(c+η*replacement F hJI R q C v α E β lo y)| ≤ |H-T|
  rw [show κ*(c+η*replacement F hJI R q C v α E β lo x)-
    κ*(c+η*replacement F hJI R q C v α E β lo y) =
    κ*η*(replacement F hJI R q C v α E β lo x-replacement F hJI R q C v α E β lo y) by ring,
      abs_mul,abs_mul,abs_of_nonneg hκ,hη,mul_one]
  rw [Real.dist_eq] at h
  change |_ - _| ≤ (replacementConstant R : ℝ) * |H-T| at h
  calc
    _ ≤ κ*((replacementConstant R : ℝ)*|H-T|) := mul_le_mul_of_nonneg_left h hκ
    _ = (κ*(replacementConstant R : ℝ))*|H-T| := by ring
    _ ≤ 1*|H-T| := mul_le_mul_of_nonneg_right hκK (abs_nonneg _)
    _ = _ := one_mul _


/-- A kept main cell, with the literal interpolated proposal and trapezoidal
shield, is an actual invariant-preserving measurable set update. The old
chart agreement is used only on its real update domain. -/
noncomputable def patch {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (A : SetSystem M Ω μ) (Z : Threshold.Variables Ω μ)
    (hJ : IsCompact J) (lo : ℝ) (hband : J = Icc lo (lo+R.a))
    (hthin : R.a ≤ (1/1000:ℝ)/1000)
    (v : M.Point J root) (hv : v.column ∈ ColumnOrder.componentColumns C)
    {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α)
    (E β c η κ : ℝ) (hE : 0 ≤ E) (hδ : R.δ = E/8) (hβ : β ≤ (1:ℝ)/100)
    (hη : |η| = 1) (hκ : 0 ≤ κ) (hκK : κ*(replacementConstant R : ℝ) ≤ 1)
    (hchart : ∀ ω i H (h : H ∈ domain R q C i),
      Threshold.active Z H (κ*(c+η*old F hJI (cellPoint R q C i H h))) ω ↔
        (A.activity ω).active i H) : SetPatch A := by
  apply Threshold.chartPatch A Z (domain R q C) (closed_domain R q C)
    (converted F hJI R q C v α E β lo c η κ)
    (converted_lipschitz F hJI R q C v hα E β lo c η κ hη hκ hκK)
  · intro ω i H hH
    have hd : H ∈ domain R q C i := (closed_domain R q C i).frontier_subset hH
    have hi := ((mem_domain R q C).mp hd).1
    rw [converted_on F hJI R q C v α E β lo c η κ hd]
    have he : H = lo ∨ H = lo+R.a := by
      simpa only [domain,ite_eq_left hi,hband,frontier_Icc (a := lo) (b := lo+R.a) (by linarith [R.width_pos]),
        mem_insert_iff,mem_singleton_iff] using hH
    rw [replacement_endpoint F hJI R q C hthin v (cellPoint R q C i H hd)
      hv hi α E β lo hβ he]
    exact hchart ω i H hd
  · intro i j H hs hi hj
    rw [converted_on F hJI R q C v α E β lo c η κ hi,
      converted_on F hJI R q C v α E β lo c η κ hj,
      replacement_switch F hJI R q C v (cellPoint R q C i H hi)
        (cellPoint R q C j H hj) hα E β lo rfl hs]
  · intro ω i j H hs hi hj
    have hmem := (mem_domain R q C).mp hi
    have hnj : j ∉ ColumnOrder.componentColumns C := by
      intro h
      exact hj ((mem_domain R q C).mpr ⟨h,hmem.2⟩)
    have hf : cellPoint R q C i H hi ∈ boundary R q C :=
      ⟨hmem.1,j,⟨H,hmem.2,hs⟩,hnj⟩
    rw [converted_on F hJI R q C v α E β lo c η κ hi,
      replacement_frontier F hJI R q C hJ v (cellPoint R q C i H hi) hα hE hδ β lo hf]
    exact hchart ω i H hi

end PlanarL1.Columns.Model.MainCell


end

section

namespace PlanarL1.Columns.Model.Point
variable {n : ℕ} {M : Model n} {J : Set ℝ} {root : Fin n}

/-- A shortest path leaving any full-column cell meets its actual frontier
before using more than its total length. No shape/convexity of the cell is used. -/
lemma near_frontier_of_not_mem (hJ : IsClosed J) (S : Set (Fin n))
    (x y : M.Point J root) (hx : x.column ∈ S) (hy : y.column ∉ S) :
    ∃ z : M.Point J root, z.column ∈ frontier (M := M) (J := J) S ∧ dist x z ≤ dist x y := by
  obtain ⟨p,_,hp⟩ := x.exists_shortest hJ y
  obtain ⟨u,v,T,hT,hs,hu,hv,q,r,hqr⟩ :=
    p.crosses_set Sᶜ (by simpa only [Set.mem_compl_iff,not_not] using hx) hy x.height y.height
  have huS : u ∈ S := by simpa only [Set.mem_compl_iff,not_not] using hu
  let z : M.Point J root := ⟨u,T,hT,x.reachable.trans q.word.reachable⟩
  refine ⟨z,⟨huS,v,⟨T,hT,hs⟩,hv⟩,?_⟩
  have hd := x.distance_le z q
  change dist x z ≤ q.length x.height T at hd
  rw [hp] at hqr
  linarith [r.length_nonneg T y.height]

end PlanarL1.Columns.Model.Point

namespace PlanarL1.Columns.Model.MainCell
open PlanarL1.Interpolation
open scoped NNReal
variable {n : ℕ} {M : Model n} {I J : Set ℝ} {root : Fin n}
variable (F : M.Field I 1) (hJI : J ⊆ I)
variable (R : Point.RadialTree (M := M) (J := J) (root := root)) (q : ℝ)
variable (C : Cell R q)

noncomputable def namedReplacement (v : M.Point J root)
    (α : Point.RadialTree.Noise (n := n)) (E β lo : ℝ) (x : M.Point J root) : NamedValue :=
  namedClip (fun z => let A := R.pasted (input F hJI R q C v) α z; ⟨A.name,A.value-4*E⟩)
    (old F hJI) (fun z => Clipping.heightShield lo R.a (old F hJI v) β z.height) x

lemma namedReplacement_value (v : M.Point J root)
    (α : Point.RadialTree.Noise (n := n)) (E β lo : ℝ) (x : M.Point J root) :
    (namedReplacement F hJI R q C v α E β lo x).value =
      replacement F hJI R q C v α E β lo x := by
  exact clippedNamed_value _ _ _

noncomputable def localClipAtom {k : ℕ} (A : R.Node k) (v : M.Point J root)
    (α : Point.RadialTree.Noise (n := n)) (E β lo : ℝ) : ℕ → M.Point J root → ℝ :=
  clipAtom (fun i z => (R.listedAtom (input F hJI R q C v) α A R.lookback i z).value-4*E)
    (old F hJI) (fun z => Clipping.heightShield lo R.a (old F hJI v) β z.height)

lemma shield_lipschitz (v : M.Point J root) (β lo : ℝ) :
    LipschitzWith (replacementConstant R)
      (fun z : M.Point J root => Clipping.heightShield lo R.a (old F hJI v) β z.height) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have ht := (Clipping.heightShield_lipschitz lo (old F hJI v) β R.width_pos).dist_le_mul x.height y.height
  have hx := x.height_change_le y
  change |x.height-y.height| ≤ dist x y at hx
  change dist _ _ ≤ (replacementConstant R : ℝ)*dist x y
  change dist _ _ ≤ (3/(9*R.a/100))*dist x.height y.height at ht
  rw [Real.dist_eq] at ht
  exact ht.trans ((mul_le_mul_of_nonneg_left hx (by positivity [R.width_pos])).trans
    (mul_le_mul_of_nonneg_right (le_max_right (1:ℝ) (3/(9*R.a/100))) dist_nonneg))

lemma localClipAtom_lipschitz {k : ℕ} (A : R.Node k) (v : M.Point J root)
    (α : Point.RadialTree.Noise (n := n)) (E β lo : ℝ) (i : ℕ) :
    LipschitzWith (replacementConstant R) (localClipAtom F hJI R q C A v α E β lo i) := by
  apply clipAtom_lipschitz
  · intro i
    apply LipschitzWith.weaken (K := 1) _ (le_max_left _ _)
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Real.dist_eq,sub_sub_sub_cancel_right] using
      (R.listedAtom_lipschitz (input F hJI R q C v) α A R.lookback i).dist_le_mul x y
  · exact (old_lipschitz F hJI R).weaken (le_max_left _ _)
  · exact shield_lipschitz F hJI R v β lo


lemma localClipPair_probability_lt {k : ℕ} (A : R.Node k) (v x : M.Point J root)
    (E lo B : ℝ) (hB : 0 < B) (cap m : ℕ) (hk : k < cap) (hm : 0 < m)
    (i j : ℕ) (hi : i ∈ clipNames (R.recentNames A R.lookback))
    (hj : j ∈ clipNames (R.recentNames A R.lookback)) (hij : i < j)
    {t : ℝ} (ht : 0 ≤ t) :
    FiniteRandom.prob (fun ω : Point.RadialTree.GridSample (n := n) cap m × Fin (m+1) =>
      |localClipAtom F hJI R q C A v (R.gridNoise cap m ω.1) E (B/m*ω.2.val) lo i x-
       localClipAtom F hJI R q C A v (R.gridNoise cap m ω.1) E (B/m*ω.2.val) lo j x| ≤ t) ≤
      (2*t+R.q/m)/R.q + (2*t+B/m)/B := by
  have hpos₁ : 0 ≤ (2*t+R.q/m)/R.q := by positivity [R.q_pos]
  have hpos₂ : 0 ≤ (2*t+B/m)/B := by positivity
  by_cases hjlow : j < 2
  · have hi0 : i = 0 := by omega
    have hj1 : j = 1 := by omega
    subst i; subst j
    apply FiniteRandom.prob_prod_bound
    intro ω
    let c := Clipping.heightShield lo R.a (old F hJI v) 0 x.height-old F hJI x
    apply (FiniteRandom.prob_mono (fun r h => ?_)).trans
      ((FiniteRandom.grid_probability m hm hB ht c).trans (le_add_of_nonneg_left hpos₁))
    have he : c+B/m*r.val =
        localClipAtom F hJI R q C A v (R.gridNoise cap m ω) E (B/m*r.val) lo 1 x-
        localClipAtom F hJI R q C A v (R.gridNoise cap m ω) E (B/m*r.val) lo 0 x := by
      simp only [localClipAtom,clipAtom,reduceCtorEq,ite_true,ite_false,c,Clipping.heightShield]
      ring
    rw [he,abs_sub_comm]
    exact h
  · have hj2 : 2 ≤ j := by omega
    have hj0 : j ≠ 0 := by omega
    have hj1 : j ≠ 1 := by omega
    have hjS : j-2 ∈ R.recentNames A R.lookback := by
      rcases mem_clipNames.mp hj with h | h | h
      · omega
      · omega
      · exact h.2
    apply FiniteRandom.prob_prod_bound_left
    intro r
    by_cases hi2 : 2 ≤ i
    · have hi0 : i ≠ 0 := by omega
      have hi1 : i ≠ 1 := by omega
      have hiS : i-2 ∈ R.recentNames A R.lookback := by
        rcases mem_clipNames.mp hi with h | h | h
        · omega
        · omega
        · exact h.2
      have hp := R.listedPair_probability (input F hJI R q C v) A R.lookback (i-2) (j-2)
        hiS hjS (by omega) x cap m hk hm ht
      apply (FiniteRandom.prob_mono (fun ω h => ?_)).trans
        (hp.trans (le_add_of_nonneg_right hpos₂))
      simpa only [localClipAtom,clipAtom,ite_eq_right hi0,ite_eq_right hi1,ite_eq_right hj0,ite_eq_right hj1,
        sub_sub_sub_cancel_right] using h
    · let c := if i = 0 then old F hJI x else Clipping.heightShield lo R.a (old F hJI v) (B/m*r.val) x.height
      have hc (ω : Point.RadialTree.GridSample (n := n) cap m) :
          localClipAtom F hJI R q C A v (R.gridNoise cap m ω) E (B/m*r.val) lo i x = c := by
        by_cases hi0 : i = 0
        · simp only [localClipAtom,clipAtom,ite_eq_left hi0,c]
        · have hi1 : i = 1 := by omega
          simp only [localClipAtom,clipAtom,ite_eq_right hi0,ite_eq_left hi1,c]
      have hp := R.listedConstant_probability (input F hJI R q C v) A R.lookback (j-2)
        hjS x (c+4*E) cap m hk hm ht
      apply (FiniteRandom.prob_mono (fun ω h => ?_)).trans
        (hp.trans (le_add_of_nonneg_right hpos₂))
      rw [hc] at h
      have he : (R.listedAtom (input F hJI R q C v) (R.gridNoise cap m ω) A R.lookback (j-2) x).value-(c+4*E) =
          localClipAtom F hJI R q C A v (R.gridNoise cap m ω) E (B/m*r.val) lo j x-c := by
        simp only [localClipAtom,clipAtom,ite_eq_right hj0,ite_eq_right hj1]
        ring
      rw [he,abs_sub_comm]
      exact h

lemma localClipPair_probability {k : ℕ} (A : R.Node k) (v x : M.Point J root)
    (E lo B : ℝ) (hB : 0 < B) (cap m : ℕ) (hk : k < cap) (hm : 0 < m)
    (i j : ℕ) (hi : i ∈ clipNames (R.recentNames A R.lookback))
    (hj : j ∈ clipNames (R.recentNames A R.lookback)) (hij : i ≠ j)
    {t : ℝ} (ht : 0 ≤ t) :
    FiniteRandom.prob (fun ω : Point.RadialTree.GridSample (n := n) cap m × Fin (m+1) =>
      |localClipAtom F hJI R q C A v (R.gridNoise cap m ω.1) E (B/m*ω.2.val) lo i x-
       localClipAtom F hJI R q C A v (R.gridNoise cap m ω.1) E (B/m*ω.2.val) lo j x| ≤ t) ≤
      (2*t+R.q/m)/R.q + (2*t+B/m)/B := by
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact localClipPair_probability_lt F hJI R q C A v x E lo B hB cap m hk hm i j hi hj hij ht
  · simpa only [abs_sub_comm] using
      localClipPair_probability_lt F hJI R q C A v x E lo B hB cap m hk hm j i hj hi hji ht


/-- The main clipping part of chart persistence. This is
for the literal interpolated, shifted, height-clipped proposal, including the
old field's retaining branch and inherited names through interpolation layers. -/
lemma namedReplacement_probability (hJ : IsCompact J) (v x : M.Point J root)
    (E lo B : ℝ) (hB : 0 < B) {ρ : ℝ} (hρ : 0 ≤ ρ) (hs : ρ ≤ R.radius)
    (m : ℕ) (hm : 0 < m) :
    FiniteRandom.prob (fun ω : Point.RadialTree.GridSample (n := n) R.depthCap m × Fin (m+1) =>
      ∃ z : M.Point J root, dist x z ≤ ρ ∧
        (namedReplacement F hJI R q C v (R.gridNoise R.depthCap m ω.1) E (B/m*ω.2.val) lo z).name ≠
        (namedReplacement F hJI R q C v (R.gridNoise R.depthCap m ω.1) E (B/m*ω.2.val) lo x).name) ≤
      (6*(R.lookback+1)+2 : ℕ)^2 *
        ((4*(replacementConstant R : ℝ)*ρ+R.q/m)/R.q +
          (4*(replacementConstant R : ℝ)*ρ+B/m)/B) := by
  classical
  obtain ⟨k,A,hlo,heq⟩ := R.common_formula x hρ hs
  have hk : k < R.depthCap :=
    (R.depth_le_layerDepth x (hlo x (by simpa using hρ))).trans_lt (R.layerDepth_lt_cap x)
  have hlist (ω : Point.RadialTree.GridSample (n := n) R.depthCap m × Fin (m+1))
      (z : M.Point J root) (hz : dist x z ≤ ρ) :
      (namedReplacement F hJI R q C v (R.gridNoise R.depthCap m ω.1) E (B/m*ω.2.val) lo z).name ∈
        clipNames (R.recentNames A R.lookback) ∧
      (namedReplacement F hJI R q C v (R.gridNoise R.depthCap m ω.1) E (B/m*ω.2.val) lo z).value =
        localClipAtom F hJI R q C A v (R.gridNoise R.depthCap m ω.1) E (B/m*ω.2.val) lo
          (namedReplacement F hJI R q C v (R.gridNoise R.depthCap m ω.1) E (B/m*ω.2.val) lo z).name z := by
    let p := input F hJI R q C v
    let α := R.gridNoise R.depthCap m ω.1
    have hα := R.gridNoise_bounds R.depthCap m hm ω.1
    have hp := input_lipschitz F hJI R q C hJ v
    have ha : |(R.formula p α k A z).value-p z| ≤ 6*R.δ := by
      rw [← heq p α hα z hz]
      exact R.pasted_accuracy hp hα z
    have hn : (R.pasted p α z).name ∈ R.recentNames A R.lookback := by
      rw [heq p α hα z hz]
      exact R.formula_name_recent hp hα k A z (hlo z hz) ha
    have hv : R.pasted p α z = R.listedAtom p α A R.lookback (R.pasted p α z).name z := by
      rw [heq p α hα z hz]
      exact R.formula_eq_listed hp hα k A z (hlo z hz) ha
    apply namedClip_list
      (fun z => ⟨(R.pasted p α z).name,(R.pasted p α z).value-4*E⟩)
      (fun i z => (R.listedAtom p α A R.lookback i z).value-4*E)
      (old F hJI) (fun z => Clipping.heightShield lo R.a (old F hJI v) (B/m*ω.2.val) z.height)
      (R.recentNames A R.lookback) z hn
    exact congrArg (fun Z : NamedValue => Z.value-4*E) hv
  let b : ℝ := (4*(replacementConstant R : ℝ)*ρ+R.q/m)/R.q +
      (4*(replacementConstant R : ℝ)*ρ+B/m)/B
  have hb : 0 ≤ b := by dsimp [b]; positivity [R.q_pos]
  have hF (ω : Point.RadialTree.GridSample (n := n) R.depthCap m × Fin (m+1)) :
      LipschitzWith (replacementConstant R)
        (fun z => (namedReplacement F hJI R q C v (R.gridNoise R.depthCap m ω.1) E (B/m*ω.2.val) lo z).value) := by
    simpa only [namedReplacement_value] using
      replacement_lipschitz F hJI R q C v (R.gridNoise_bounds _ _ hm ω.1) E (B/m*ω.2.val) lo
  have hp := selection_probability
    (fun ω : Point.RadialTree.GridSample (n := n) R.depthCap m × Fin (m+1) =>
      namedReplacement F hJI R q C v (R.gridNoise R.depthCap m ω.1) E (B/m*ω.2.val) lo)
    (fun ω => localClipAtom F hJI R q C A v (R.gridNoise R.depthCap m ω.1) E (B/m*ω.2.val) lo)
    (clipNames (R.recentNames A R.lookback)) hF
    (fun ω i _ => localClipAtom_lipschitz F hJI R q C A v _ E _ lo i) x hρ hb hlist
    (fun i hi j hj hij => by
      simpa only [show 2*(2*(replacementConstant R : ℝ)*ρ) = 4*(replacementConstant R : ℝ)*ρ by ring] using
        localClipPair_probability F hJI R q C A v x E lo B hB R.depthCap m hk hm i j hi hj hij
          (t := 2*(replacementConstant R : ℝ)*ρ) (by positivity))
  refine hp.trans ?_
  apply mul_le_mul_of_nonneg_right _ hb
  apply pow_le_pow_left₀ (Nat.cast_nonneg _)
  exact_mod_cast (clipNames_card (R.recentNames A R.lookback)).trans
    (Nat.add_le_add_right (R.recentNames_card A R.lookback) 2)


lemma namedReplacement_near_frontier (hJ : IsCompact J) (v x z : M.Point J root)
    {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α)
    {E : ℝ} (hE : 0 ≤ E) (hδ : R.δ = E/8) (β lo : ℝ)
    (hz : z ∈ boundary R q C) (hd : 2*dist x z < 3*E) :
    namedReplacement F hJI R q C v α E β lo x = ⟨0,old F hJI x⟩ := by
  apply clippedNamed_retains
  change proposal F hJI R q C v α E x < old F hJI x
  have hm := frontier_margin F hJI R q C hJ v hα hE hδ hz
  have hxz := (proposal_lipschitz F hJI R q C v hα E).dist_le_mul x z
  have hs := (old_lipschitz F hJI R).dist_le_mul z x
  simp only [Real.dist_eq,NNReal.coe_one,one_mul] at hxz hs
  rw [dist_comm z x] at hs
  have hp := (abs_le.mp hxz).2
  have ho := (abs_le.mp hs).2
  linarith

/-- Crossing a main-cell boundary causes no identifier loss at all. This is
exactly why no radial padding error proportional to the band width is needed
in the source persistence bound. -/
lemma namedReplacement_retained_on_touched_ball (hJ : IsCompact J)
    (v x : M.Point J root) {ρ : ℝ} {α : Point.RadialTree.Noise (n := n)}
    (hα : R.NoiseBounds α) {E : ℝ} (hE : 0 ≤ E) (hδ : R.δ = E/8)
    (β lo : ℝ) (hρ : 4*ρ < 3*E)
    (hex : ∃ y : M.Point J root, dist x y ≤ ρ ∧ y.column ∉ ColumnOrder.componentColumns C) :
    ∀ w : M.Point J root, dist x w ≤ ρ → w.column ∈ ColumnOrder.componentColumns C →
      namedReplacement F hJI R q C v α E β lo w = ⟨0,old F hJI w⟩ := by
  intro w hw hwC
  obtain ⟨y,hy,hyC⟩ := hex
  obtain ⟨z,hz,hd⟩ := Point.near_frontier_of_not_mem R.closed_band
    (ColumnOrder.componentColumns C) w y hwC hyC
  apply namedReplacement_near_frontier F hJI R q C hJ v w z hα hE hδ β lo hz
  have ht := dist_triangle w x y
  rw [dist_comm w x] at ht
  linarith

end PlanarL1.Columns.Model.MainCell



end

section

namespace PlanarL1.Columns.Model.MainCell
open PlanarL1.Interpolation
open scoped NNReal
variable {n : ℕ} {M : Model n} {I J : Set ℝ} {root : Fin n}
variable (F : M.Field I 1) (hJI : J ⊆ I)
variable (R : Point.RadialTree (M := M) (J := J) (root := root)) (q : ℝ)
variable (C : Cell R q)

lemma namedReplacement_cases (v : M.Point J root)
    (α : Point.RadialTree.Noise (n := n)) (E β lo : ℝ) (x : M.Point J root) :
    (namedReplacement F hJI R q C v α E β lo x = ⟨0,old F hJI x⟩) ∨
    (namedReplacement F hJI R q C v α E β lo x =
      ⟨1,Clipping.heightShield lo R.a (old F hJI v) β x.height⟩) ∨
    (namedReplacement F hJI R q C v α E β lo x =
      ⟨(R.pasted (input F hJI R q C v) α x).name+2,
        (R.pasted (input F hJI R q C v) α x).value-4*E⟩) := by
  rcases clippedNamed_mem ⟨0,old F hJI x⟩
    ⟨(R.pasted (input F hJI R q C v) α x).name+2,
        (R.pasted (input F hJI R q C v) α x).value-4*E⟩
    ⟨1,Clipping.heightShield lo R.a (old F hJI v) β x.height⟩ with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

lemma namedReplacement_bound (v : M.Point J root)
    (α : Point.RadialTree.Noise (n := n)) (E β lo : ℝ) (x : M.Point J root) :
    (namedReplacement F hJI R q C v α E β lo x).name < 3*n*R.depthCap+2 := by
  rcases namedReplacement_cases F hJI R q C v α E β lo x with h | h | h
  · rw [h]; simp only; omega
  · rw [h]; simp only; omega
  · rw [h]
    exact Nat.add_lt_add_right
      ((R.formula_name_bound (input F hJI R q C v) α
        (R.layerDepth x) (R.layerNode x) x).trans_le
        (Nat.mul_le_mul_left (3*n) (R.layerDepth_lt_cap x))) 2

lemma namedReplacement_congr_zero (v x y : M.Point J root)
    {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α) (E β lo : ℝ)
    (hxy : dist x y=0) :
    namedReplacement F hJI R q C v α E β lo x =
      namedReplacement F hJI R q C v α E β lo y := by
  have hp := R.pasted_congr_zero (input F hJI R q C v) hα x y hxy
  have ho : old F hJI x=old F hJI y := by
    apply dist_le_zero.mp
    have ht := (old_lipschitz F hJI R).dist_le_mul x y
    simpa only [hxy,mul_zero] using ht
  have hh : x.height=y.height := by
    have ht : |x.height-y.height| ≤ dist x y := x.height_change_le y
    rw [hxy] at ht
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm ht (abs_nonneg _)))
  simp only [namedReplacement,namedClip,hp,ho,hh]


/-- A local winner other than the old field receives exactly one new name.
The height-only branch is zero in the fresh block, and spatial atom a is a+1. -/
noncomputable def choose (v : M.Point J root)
    (α : Point.RadialTree.Noise (n := n)) (E β lo : ℝ) (i : Fin n) (H : ℝ) :
    Option (Fin (3*n*R.depthCap+1)) := by
  classical
  exact if hd : H ∈ domain R q C i then
    let t := namedReplacement F hJI R q C v α E β lo (cellPoint R q C i H hd)
    if ht : t.name=0 then none else some ⟨t.name-1,by
      have hb := namedReplacement_bound F hJI R q C v α E β lo (cellPoint R q C i H hd)
      dsimp only [t] at ht ⊢
      omega⟩
    else none

lemma choose_spec (v : M.Point J root)
    (α : Point.RadialTree.Noise (n := n)) (E β lo : ℝ) (i : Fin n) (H : ℝ)
    (a : Fin (3*n*R.depthCap+1)) (ha : choose F hJI R q C v α E β lo i H=some a) :
    ∃ hd : H ∈ domain R q C i,
      (namedReplacement F hJI R q C v α E β lo (cellPoint R q C i H hd)).name=a.val+1 := by
  classical
  by_cases hd : H ∈ domain R q C i
  · simp only [choose,dite_eq_left hd] at ha
    split_ifs at ha with ht
    refine ⟨hd,?_⟩
    have he := congrArg Fin.val (Option.some.inj ha)
    dsimp only at he ht
    omega
  · simp only [choose,dite_eq_right hd] at ha
    cases ha

lemma choose_none_inside (v : M.Point J root)
    (α : Point.RadialTree.Noise (n := n)) (E β lo : ℝ) (i : Fin n) (H : ℝ)
    (hd : H ∈ domain R q C i) (hc : choose F hJI R q C v α E β lo i H=none) :
    (namedReplacement F hJI R q C v α E β lo (cellPoint R q C i H hd)).name=0 := by
  classical
  by_contra hn
  simp only [choose,dite_eq_left hd,dite_eq_right hn] at hc
  cases hc

lemma choose_none_outside (v : M.Point J root)
    (α : Point.RadialTree.Noise (n := n)) (E β lo : ℝ) (i : Fin n) (H : ℝ)
    (hd : H ∉ domain R q C i) : choose F hJI R q C v α E β lo i H=none := by
  simp only [choose,dite_eq_right hd]

lemma choose_none_frontier (hJ : IsCompact J) (v : M.Point J root)
    {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α)
    {E : ℝ} (hE : 0<E) (hδ : R.δ=E/8) (β lo : ℝ) (i : Fin n) (H : ℝ)
    (hd : H ∈ domain R q C i) (hf : cellPoint R q C i H hd ∈ boundary R q C) :
    choose F hJI R q C v α E β lo i H=none := by
  have hm := frontier_margin F hJI R q C hJ v hα hE.le hδ hf
  have hn : namedReplacement F hJI R q C v α E β lo (cellPoint R q C i H hd) =
      ⟨0,old F hJI (cellPoint R q C i H hd)⟩ := by
    apply clippedNamed_retains
    change proposal F hJI R q C v α E _ < old F hJI _
    linarith
  simp [choose,hd,hn]

lemma choose_switch (hJ : IsCompact J) (v : M.Point J root)
    {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α)
    {E : ℝ} (hE : 0<E) (hδ : R.δ=E/8) (β lo : ℝ) (i j : Fin n) (H : ℝ)
    (hs : H ∈ M.heights i j) :
    choose F hJI R q C v α E β lo i H=choose F hJI R q C v α E β lo j H := by
  classical
  by_cases hi : H ∈ domain R q C i <;> by_cases hj : H ∈ domain R q C j
  · have hd : dist (cellPoint R q C i H hi) (cellPoint R q C j H hj)=0 := by
      apply le_antisymm _ dist_nonneg
      have ht := (cellPoint R q C i H hi).dist_le_switch (cellPoint R q C j H hj)
        ((mem_domain R q C).mp hi).2 hs
      simpa only [cellPoint,sub_self,abs_zero,add_zero] using ht
    have hn := namedReplacement_congr_zero F hJI R q C v
      (cellPoint R q C i H hi) (cellPoint R q C j H hj) hα E β lo hd
    simp only [choose,dite_eq_left hi,dite_eq_left hj]
    simp only [hn]
  · have hx := (mem_domain R q C).mp hi
    have hn : j ∉ ColumnOrder.componentColumns C := by
      intro h
      exact hj ((mem_domain R q C).mpr ⟨h,hx.2⟩)
    rw [choose_none_frontier F hJI R q C hJ v hα hE hδ β lo i H hi
      ⟨hx.1,j,⟨H,hx.2,hs⟩,hn⟩,choose_none_outside F hJI R q C v α E β lo j H hj]
  · have hx := (mem_domain R q C).mp hj
    have hn : i ∉ ColumnOrder.componentColumns C := by
      intro h
      exact hi ((mem_domain R q C).mpr ⟨h,hx.2⟩)
    have hs' : H ∈ M.heights j i := by rwa [M.symm]
    rw [choose_none_outside F hJI R q C v α E β lo i H hi,
      choose_none_frontier F hJI R q C hJ v hα hE hδ β lo j H hj
        ⟨hx.1,i,⟨H,hx.2,hs'⟩,hn⟩]
  · rw [choose_none_outside F hJI R q C v α E β lo i H hi,
      choose_none_outside F hJI R q C v α E β lo j H hj]

end PlanarL1.Columns.Model.MainCell



end

end OAI
