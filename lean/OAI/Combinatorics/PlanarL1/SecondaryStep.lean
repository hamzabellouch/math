import OAI.Combinatorics.PlanarL1.SecondaryCells
import OAI.Combinatorics.PlanarL1.Ambient

namespace OAI

section

namespace PlanarL1.Columns.Model
open MeasureTheory
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)}

namespace BData
noncomputable def isOrdinary : BData M → Bool
  | .ordinary _ => true
  | .ordered _ => false

noncomputable def comparison (D : BData M) (lam : ℝ≥0) (hlam : lam ≤ (1:ℝ≥0)/100)
    (positive : Bool) : M.Field D.band 5 :=
  match D with
  | .ordinary C => C.comparison.weaken (by norm_num)
  | .ordered C => if positive then C.field lam hlam else (C.field lam hlam).negate

noncomputable def offset : BData M → ℝ
  | .ordinary C => C.constant
  | .ordered _ => 0

noncomputable def orientation (positive : Bool) : BData M → ℝ
  | .ordinary C => C.orientation
  | .ordered _ => if positive then 1 else -1

lemma orientation_unit (positive : Bool) (D : BData M) : |D.orientation positive|=1 := by
  cases D with
  | ordinary C => exact C.unit_orientation
  | ordered C => cases positive <;> norm_num [orientation]

lemma comparison_convert (D : BData M) (lam : ℝ≥0) (hlam : lam ≤ (1:ℝ≥0)/100)
    (positive : Bool) (i : Fin (k+1)) (H : D.band) :
    D.value lam i H = D.offset+D.orientation positive*(D.comparison lam hlam positive).value i H := by
  cases D with
  | ordinary C => rfl
  | ordered C =>
    cases positive
    · change C.value lam i H = 0+(-1)*(-(C.field lam hlam).value i H)
      erw [OrderedData.field_value]; ring
    · change C.value lam i H = 0+1*(C.field lam hlam).value i H
      erw [OrderedData.field_value]; ring
end BData

namespace OrdinaryData
/-- The affine conversion constants, without manufacturing a point source. -/
noncomputable def conversion (M : Model (k+1)) (c η : ℝ) (hη : |η|=1) : OrdinaryData M where
  band := Set.univ
  closed := isClosed_univ
  convex := Set.ordConnected_univ
  origin := none
  constant := c
  orientation := η
  unit_orientation := hη
end OrdinaryData

namespace Point.RadialTree
variable {J : Set ℝ} {root : Fin (k+1)} (R : RadialTree (M := M) (J := J) (root := root))
namespace AtomSource
variable {R} {a : ℕ}
/-- Exact shallow-secondary ordinary chart: c+η(pc+R/20−Q_F). -/
noncomputable def secondaryChart (A : R.AtomSource a) (c η : ℝ) (hη : |η|=1)
    (p : M.Point J root → ℝ) (α : Noise (n := k+1)) (pc radius : ℝ) : OrdinaryData M :=
  (OrdinaryData.conversion M c η hη).atom J R.closed_band R.interval_band A.center
    (pc+radius/20-A.intercept p α) (-A.sign) (by rw [abs_neg,A.sign_unit])

lemma secondaryChart_value (A : R.AtomSource a) (c η : ℝ) (hη : |η|=1)
    (p : M.Point J root → ℝ) (α : Noise (n := k+1)) (pc radius : ℝ) (x : M.Point J root) :
    (A.secondaryChart c η hη p α pc radius).value x.column ⟨x.height,x.inBand⟩ =
      c+η*(pc+radius/20-(A.eval p α x).value) := by
  change ((OrdinaryData.conversion M c η hη).atom J R.closed_band R.interval_band A.center
    (pc+radius/20-A.intercept p α) (-A.sign) _).value x.column ⟨x.height,x.inBand⟩ = _
  rw [OrdinaryData.atom_value,A.eval_formula]
  dsimp only [OrdinaryData.conversion]
  ring
end AtomSource

noncomputable def secondaryChart (c η : ℝ) (hη : |η|=1)
    (p : M.Point J root → ℝ) (α : Noise (n := k+1)) (pc radius : ℝ) (a : ℕ) : OrdinaryData M :=
  if h : Nonempty (R.AtomSource a) then h.some.secondaryChart c η hη p α pc radius
  else OrdinaryData.initial M

lemma secondaryChart_value (c η : ℝ) (hη : |η|=1)
    (p : M.Point J root → ℝ) (α : Noise (n := k+1)) (pc radius : ℝ) (x : M.Point J root) :
    ∃ h : x.height ∈ (R.secondaryChart c η hη p α pc radius (R.pasted p α x).name).band,
      (R.secondaryChart c η hη p α pc radius (R.pasted p α x).name).value x.column ⟨x.height,h⟩ =
        c+η*(pc+radius/20-(R.pasted p α x).value) := by
  have h := R.pasted_has_source p α x
  let Q : OrdinaryData M → Prop := fun T => ∃ hi : x.height ∈ T.band,
    T.value x.column ⟨x.height,hi⟩ = c+η*(pc+radius/20-(R.pasted p α x).value)
  change Q (R.secondaryChart c η hη p α pc radius (R.pasted p α x).name)
  rw [show R.secondaryChart c η hη p α pc radius (R.pasted p α x).name =
    h.some.secondaryChart c η hη p α pc radius from dite_eq_left h]
  exact ⟨x.inBand,(h.some.secondaryChart_value c η hη p α pc radius x).trans
    (by rw [R.source_eval_pasted])⟩

lemma secondaryChart_contains (c η : ℝ) (hη : |η|=1)
    (p : M.Point J root → ℝ) (α : Noise (n := k+1)) (pc radius : ℝ) (x : M.Point J root) :
    (R.secondaryChart c η hη p α pc radius (R.pasted p α x).name).Contains x.column x.height := by
  have h := R.pasted_has_source p α x
  rw [show R.secondaryChart c η hη p α pc radius (R.pasted p α x).name =
    h.some.secondaryChart c η hη p α pc radius from dite_eq_left h]
  exact OrdinaryData.atom_contains _ _ _ _ _ x _ _ _
end Point.RadialTree

namespace OrderedData
/-- The source ordered-support branch, including the old affine chart
conversion. The auxiliary field is zero and the circular order reverses exactly
when η is negative. -/
noncomputable def secondaryInstall {I : Set ℝ} (hI : IsClosed I) (hc : I.OrdConnected)
    (L : M.Field I 1) (a b : Fin (k+1)) (ho : L.OrderedFrom a b)
    (c η pc radius α : ℝ) (_hη : |η|=1) : OrderedData M :=
  install hI hc L a b ho (η*c+pc+radius/20-4*pc+α) (decide (η=1))

lemma secondaryInstall_value {I : Set ℝ} (hI : IsClosed I) (hc : I.OrdConnected)
    (L : M.Field I 1) (a b : Fin (k+1)) (ho : L.OrderedFrom a b)
    (c η pc radius α : ℝ) (hη : |η|=1) (lam : ℝ≥0) (i : Fin (k+1)) (H : I) :
    (secondaryInstall hI hc L a b ho c η pc radius α hη).value lam i H =
      c+η*(pc+radius/20+4*(L.value i H-pc)+α) := by
  change (install hI hc L a b ho (η*c+pc+radius/20-4*pc+α) (decide (η=1))).value lam i H = _
  rw [install_value]
  rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hη with he | he
  · simp only [he,decide_true,ite_true]; ring
  · norm_num [he]; ring
end OrderedData
end PlanarL1.Columns.Model

namespace PlanarL1.Columns.Model.SecondaryCell
open PlanarL1.Interpolation
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {M : Model n} {J : Set ℝ} {root : Fin n}
variable (R : Point.RadialTree (M := M) (J := J) (root := root))
variable (S : Finset (M.Point J root))
variable (old L : M.Point J root → ℝ) (ordinary : Bool)

lemma namedReplacement_cases (pc radius αo αh lo : ℝ)
    (α : Point.RadialTree.Noise (n := n)) (x : M.Point J root) :
    namedReplacement R S old L ordinary pc radius αo αh lo α x=⟨0,old x⟩ ∨
    namedReplacement R S old L ordinary pc radius αo αh lo α x=
      ⟨1,Clipping.heightShield lo R.a pc αh x.height⟩ ∨
    namedReplacement R S old L ordinary pc radius αo αh lo α x=
      ⟨2,Clipping.orderedBranch pc radius αo L x⟩ ∨
    namedReplacement R S old L ordinary pc radius αo αh lo α x=
      ⟨(R.pasted (input S) α x).name+3,shallow R S pc radius α x⟩ :=
  secondaryNamed_mem _ _ _ _ _ x

lemma namedReplacement_bound (pc radius αo αh lo : ℝ)
    (α : Point.RadialTree.Noise (n := n)) (x : M.Point J root) :
    (namedReplacement R S old L ordinary pc radius αo αh lo α x).name < 3*n*R.depthCap+3 := by
  rcases namedReplacement_cases R S old L ordinary pc radius αo αh lo α x with h | h | h | h
  · rw [h]; simp only; omega
  · rw [h]; simp only; omega
  · rw [h]; simp only; omega
  · rw [h]
    exact Nat.add_lt_add_right (R.pasted_name_lt (input S) α x) 3

lemma namedReplacement_congr_zero (hOld : LipschitzWith 5 old) (hL : LipschitzWith 1 L)
    (pc radius αo αh lo : ℝ) {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α)
    (x y : M.Point J root) (hxy : dist x y=0) :
    namedReplacement R S old L ordinary pc radius αo αh lo α x =
      namedReplacement R S old L ordinary pc radius αo αh lo α y := by
  have hp := R.pasted_congr_zero (input S) hα x y hxy
  have ho : old x=old y := dist_le_zero.mp (by simpa only [hxy,mul_zero] using hOld.dist_le_mul x y)
  have hl : L x=L y := dist_le_zero.mp (by simpa only [hxy,mul_zero] using hL.dist_le_mul x y)
  have hh : x.height=y.height := by
    have ht : |x.height-y.height| ≤ dist x y := x.height_change_le y
    rw [hxy] at ht
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm ht (abs_nonneg _)))
  simp only [namedReplacement,secondaryNamed,shallow,approx,hp,ho,hh,Clipping.orderedBranch,hl]

noncomputable def choose (pc radius αo αh lo : ℝ)
    (α : Point.RadialTree.Noise (n := n)) (i : Fin n) (H : ℝ) :
    Option (Fin (3*n*R.depthCap+2)) :=
  if hd : H ∈ domain S radius i then
    let t := namedReplacement R S old L ordinary pc radius αo αh lo α (point S radius i H hd)
    if ht : t.name=0 then none else some ⟨t.name-1,by
      have hb := namedReplacement_bound R S old L ordinary pc radius αo αh lo α (point S radius i H hd)
      dsimp only [t] at ht ⊢
      omega⟩
  else none

lemma choose_spec (pc radius αo αh lo : ℝ) (α : Point.RadialTree.Noise (n := n))
    (i : Fin n) (H : ℝ) (a : Fin (3*n*R.depthCap+2))
    (h : choose R S old L ordinary pc radius αo αh lo α i H=some a) :
    ∃ hd : H ∈ domain S radius i,
      (namedReplacement R S old L ordinary pc radius αo αh lo α (point S radius i H hd)).name=a.val+1 := by
  by_cases hd : H ∈ domain S radius i
  · simp only [choose,dite_eq_left hd] at h
    split_ifs at h with ht
    refine ⟨hd,?_⟩
    have he := congrArg Fin.val (Option.some.inj h)
    dsimp only at he ht
    omega
  · simp only [choose,dite_eq_right hd] at h
    cases h

lemma choose_none (pc radius αo αh lo : ℝ) (α : Point.RadialTree.Noise (n := n))
    (i : Fin n) (H : ℝ) (hd : H ∈ domain S radius i)
    (h : choose R S old L ordinary pc radius αo αh lo α i H=none) :
    (namedReplacement R S old L ordinary pc radius αo αh lo α (point S radius i H hd)).name=0 := by
  unfold choose at h
  simp only [dite_eq_left hd] at h
  split_ifs at h with ht
  exact ht

lemma choose_switch (hOld : LipschitzWith 5 old) (hL : LipschitzWith 1 L)
    (pc radius αo αh lo : ℝ) {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α)
    (i j : Fin n) (H : ℝ) (hs : H ∈ M.heights i j) :
    choose R S old L ordinary pc radius αo αh lo α i H =
      choose R S old L ordinary pc radius αo αh lo α j H := by
  by_cases hi : H ∈ domain S radius i
  · have hj := switch_mem S radius hs hi
    have he := namedReplacement_congr_zero R S old L ordinary hOld hL pc radius αo αh lo hα
      (point S radius i H hi) (point S radius j H hj) (point_dist_switch S hi hj hs)
    simp only [choose,dite_eq_left hi,dite_eq_left hj]
    simp only [he]
  · have hj : H ∉ domain S radius j := fun hj => hi (switch_mem S radius (M.symm i j ▸ hs) hj)
    simp only [choose,dite_eq_right hi,dite_eq_right hj]
end PlanarL1.Columns.Model.SecondaryCell


namespace PlanarL1.Columns.Model
open MeasureTheory
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {κ : ℝ} {lam : ℝ≥0}
  {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

namespace BState
lemma represents_named (S : BState M κ lam Ω μ) (ω : Ω) (i : Fin (k+1)) (H : ℝ)
    (a : Fin (S.count+1)) (ha : S.name i H=a) (hi : H ∈ (S.chart a).band) :
    (S.sets.activity ω).active i H ↔ Threshold.active (S.labels a) H
      (κ*(S.chart a).value lam i ⟨H,hi⟩) ω := by
  subst a
  exact S.represents ω i H

/-- One kept group's literal secondary clipping. Only the geometric admission,
seed and eligibility data enter; every new chart below is constructed from the
winning formula, not postulated. -/
structure SecondaryStep (S : BState M κ lam Ω μ) (J : Set ℝ) (root : Fin (k+1)) where
  index : Fin (S.count+1)
  positive : Bool
  lambda_bound : lam ≤ (1:ℝ≥0)/100
  tree : Point.RadialTree (M := M) (J := J) (root := root)
  lo : ℝ
  band_eq : J=Set.Icc lo (lo+tree.a)
  sub_old : J ⊆ (S.chart index).band
  seeds : Finset (M.Point J root)
  seeds_nonempty : seeds.Nonempty
  pc : ℝ
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  radius_small : radius ≤ (1:ℝ)/100
  support : M.Field (S.chart index).band 1
  lower : Fin (k+1)
  upper : Fin (k+1)
  support_ordered : support.OrderedFrom lower upper
  support_le : (S.chart index).isOrdinary=true → ∀ x : M.Point J root,
    support.value x.column ⟨x.height,sub_old x.inBand⟩ ≤
      ((S.chart index).comparison lam lambda_bound positive).value x.column ⟨x.height,sub_old x.inBand⟩
  admitted : (S.chart index).isOrdinary=false → ∀ w ∈ seeds, ∀ x : M.Point J root,
    dist w x=radius → pc-(65/100:ℝ)*radius ≤
      ((S.chart index).comparison lam lambda_bound positive).value x.column ⟨x.height,sub_old x.inBand⟩
  seed_near : ∀ w ∈ seeds,
    |((S.chart index).comparison lam lambda_bound positive).value w.column ⟨w.height,sub_old w.inBand⟩-pc| ≤
      (60/1000000:ℝ)*radius
  zeta_eq : tree.ζ=(1:ℝ)/10
  delta_eq : tree.δ=(radius/1000)/8
  noise : Point.RadialTree.Noise (n := k+1)
  noise_bounds : tree.NoiseBounds noise
  ordered_offset : ℝ
  shield_offset : ℝ
  ordered_bound : ordered_offset ≤ radius/1000
  shield_bound : shield_offset ≤ radius/1000
  same_name : ∀ i H, H ∈ SecondaryCell.domain seeds radius i → S.name i H=index
  kappa_nonneg : 0 ≤ κ
  vertical_bound : κ*(SecondaryCell.replacementConstant tree : ℝ) ≤ 1
  shield_strict : κ*(3/(9*tree.a/100)) < 1

namespace SecondaryStep
variable {S : BState M κ lam Ω μ} {J : Set ℝ} {root : Fin (k+1)}
variable (U : SecondaryStep S J root)

noncomputable def data : BData M := S.chart U.index
noncomputable def comparison : M.Field U.data.band 5 := U.data.comparison lam U.lambda_bound U.positive
noncomputable def old (x : M.Point J root) : ℝ := U.comparison.value x.column ⟨x.height,U.sub_old x.inBand⟩
noncomputable def supportValue (x : M.Point J root) : ℝ := U.support.value x.column ⟨x.height,U.sub_old x.inBand⟩

lemma old_lipschitz : LipschitzWith 5 U.old :=
  (U.comparison.restrict U.sub_old).lipschitz U.tree.closed_band root
lemma support_lipschitz : LipschitzWith 1 U.supportValue :=
  (U.support.restrict U.sub_old).lipschitz U.tree.closed_band root
include U in
lemma compact_band : IsCompact J := by rw [U.band_eq]; exact isCompact_Icc

lemma old_agreement (ω : Ω × Bool) (i : Fin (k+1)) (H : ℝ)
    (hi : H ∈ SecondaryCell.domain U.seeds U.radius i) :
    Threshold.active (S.labels U.index).lift H
      (κ*(U.data.offset+U.data.orientation U.positive*U.old (SecondaryCell.point U.seeds U.radius i H hi))) ω ↔
        (S.lift.sets.activity ω).active i H := by
  have he := U.data.comparison_convert lam U.lambda_bound U.positive i
    ⟨H,U.sub_old (SecondaryCell.inBand_of_mem U.seeds U.radius hi)⟩
  have hr := S.represents_named ω.1 i H U.index (U.same_name i H hi)
    (U.sub_old (SecondaryCell.inBand_of_mem U.seeds U.radius hi))
  dsimp only [data] at he
  rw [he] at hr
  change Threshold.active (S.labels U.index) H
    (κ*(U.data.offset+U.data.orientation U.positive*U.old (SecondaryCell.point U.seeds U.radius i H hi))) ω.1 ↔
      (S.sets.activity ω.1).active i H
  simpa only [old,comparison,data,SecondaryCell.point_column,SecondaryCell.point_height] using hr.symm

noncomputable def patch : SetPatch S.lift.sets :=
  SecondaryCell.patch U.tree U.seeds U.old U.supportValue U.data.isOrdinary
    S.lift.sets (S.labels U.index).lift U.compact_band U.lo U.band_eq
    U.seeds_nonempty U.old_lipschitz U.support_lipschitz U.zeta_eq
    U.pc U.radius U.ordered_offset U.shield_offset U.data.offset (U.data.orientation U.positive) κ
    U.radius_nonneg U.radius_small U.ordered_bound U.shield_bound U.delta_eq U.noise_bounds
    U.support_le U.admitted U.seed_near (U.data.orientation_unit U.positive)
    U.kappa_nonneg U.vertical_bound U.old_agreement

noncomputable def input : M.Point J root → ℝ := SecondaryCell.input U.seeds
noncomputable def replacement := SecondaryCell.replacement U.tree U.seeds U.old U.supportValue
  U.data.isOrdinary U.pc U.radius U.ordered_offset U.shield_offset U.lo U.noise
noncomputable def named := SecondaryCell.namedReplacement U.tree U.seeds U.old U.supportValue
  U.data.isOrdinary U.pc U.radius U.ordered_offset U.shield_offset U.lo U.noise
noncomputable def shield (H : ℝ) : ℝ :=
  κ*(U.data.offset+U.data.orientation U.positive*Clipping.heightShield U.lo U.tree.a U.pc U.shield_offset H)
noncomputable def shieldConstant : ℝ≥0 :=
  ⟨κ*(3/(9*U.tree.a/100)),mul_nonneg U.kappa_nonneg (by positivity [U.tree.width_pos])⟩

lemma shield_lipschitz : LipschitzWith U.shieldConstant U.shield := by
  apply LipschitzWith.of_dist_le_mul
  intro H T
  have ht := (Clipping.heightShield_lipschitz U.lo U.pc U.shield_offset U.tree.width_pos).dist_le_mul H T
  rw [Real.dist_eq] at ht
  change |shield U H-shield U T| ≤ (κ*(3/(9*U.tree.a/100)))*dist H T
  unfold shield
  rw [show κ*(U.data.offset+U.data.orientation U.positive*Clipping.heightShield U.lo U.tree.a
      U.pc U.shield_offset H)-κ*(U.data.offset+U.data.orientation U.positive*Clipping.heightShield U.lo U.tree.a
      U.pc U.shield_offset T) = κ*U.data.orientation U.positive*(Clipping.heightShield U.lo U.tree.a
      U.pc U.shield_offset H-Clipping.heightShield U.lo U.tree.a U.pc U.shield_offset T) by ring,
    abs_mul,abs_mul,abs_of_nonneg U.kappa_nonneg,U.data.orientation_unit,mul_one]
  exact (mul_le_mul_of_nonneg_left ht U.kappa_nonneg).trans_eq (mul_assoc _ _ _).symm

noncomputable def orderedChart : OrderedData M :=
  OrderedData.secondaryInstall U.data.closed U.data.convex U.support U.lower U.upper U.support_ordered
    U.data.offset (U.data.orientation U.positive) U.pc U.radius U.ordered_offset (U.data.orientation_unit U.positive)

noncomputable def newData (a : Fin (3*(k+1)*U.tree.depthCap+2)) : BData M :=
  if a.val=0 then .ordinary (OrdinaryData.initial M) else
  if a.val=1 then .ordered U.orderedChart else
    .ordinary (U.tree.secondaryChart U.data.offset (U.data.orientation U.positive)
      (U.data.orientation_unit U.positive) U.input U.noise U.pc U.radius (a.val-2))

noncomputable def newLabels [SFinite μ] (a : Fin (3*(k+1)*U.tree.depthCap+2)) :
    Threshold.Variables (Ω × Bool) (μ.prod Threshold.fair) :=
  if a.val=0 then (S.labels U.index).rebase (K := U.shieldConstant) U.shield_strict U.shield_lipschitz
  else (S.labels U.index).lift

noncomputable def choose := SecondaryCell.choose U.tree U.seeds U.old U.supportValue
  U.data.isOrdinary U.pc U.radius U.ordered_offset U.shield_offset U.lo U.noise

lemma patch_inside (ω : Ω × Bool) (i : Fin (k+1)) (H : ℝ)
    (hi : H ∈ SecondaryCell.domain U.seeds U.radius i) :
    (U.patch.apply.activity ω).active i H ↔ Threshold.active (S.labels U.index).lift H
      (κ*(U.data.offset+U.data.orientation U.positive*U.replacement (SecondaryCell.point U.seeds U.radius i H hi))) ω := by
  apply (U.patch.inside hi ω).trans
  change Threshold.active _ H (SecondaryCell.converted U.tree U.seeds U.old U.supportValue U.data.isOrdinary
    U.pc U.radius U.ordered_offset U.shield_offset U.lo U.data.offset (U.data.orientation U.positive) κ U.noise i H) ω ↔ _
  rw [SecondaryCell.converted_on _ _ _ _ _ _ _ _ _ _ _ _ _ _ hi]
  rfl

lemma chosen_description [SFinite μ] (i : Fin (k+1)) (H : ℝ)
    (a : Fin (3*(k+1)*U.tree.depthCap+2)) (hc : U.choose i H=some a) :
    (H ∈ (U.newData a).band ∧ (U.newData a).Uses i) ∧
      ∀ (ω : Ω × Bool) (hi : H ∈ (U.newData a).band),
        (U.patch.apply.activity ω).active i H ↔
          Threshold.active (U.newLabels a) H (κ*(U.newData a).value lam i ⟨H,hi⟩) ω := by
  let Q (D : BData M) (Z : Threshold.Variables (Ω × Bool) (μ.prod Threshold.fair)) : Prop :=
    (H ∈ D.band ∧ D.Uses i) ∧ ∀ (ω : Ω × Bool) (hi : H ∈ D.band),
      (U.patch.apply.activity ω).active i H ↔ Threshold.active Z H (κ*D.value lam i ⟨H,hi⟩) ω
  change Q (U.newData a) (U.newLabels a)
  obtain ⟨hd,hn⟩ := SecondaryCell.choose_spec U.tree U.seeds U.old U.supportValue U.data.isOrdinary
    U.pc U.radius U.ordered_offset U.shield_offset U.lo U.noise i H a hc
  let x := SecondaryCell.point U.seeds U.radius i H hd
  have hcol : x.column=i := SecondaryCell.point_column _ _ hd
  have hheight : x.height=H := SecondaryCell.point_height _ _ hd
  change (SecondaryCell.namedReplacement U.tree U.seeds U.old U.supportValue U.data.isOrdinary
    U.pc U.radius U.ordered_offset U.shield_offset U.lo U.noise x).name=a.val+1 at hn
  rcases SecondaryCell.namedReplacement_cases U.tree U.seeds U.old U.supportValue U.data.isOrdinary
    U.pc U.radius U.ordered_offset U.shield_offset U.lo U.noise x with ho | hh | hq | hp
  · have hn' := congrArg PlanarL1.Interpolation.NamedValue.name ho
    change _=0 at hn'
    omega
  · have hn' := congrArg PlanarL1.Interpolation.NamedValue.name hh
    change _=1 at hn'
    have ha0 : a.val=0 := by omega
    simp only [newData,newLabels,ite_eq_left ha0]
    refine ⟨OrdinaryData.initial_contains i H,?_⟩
    intro ω hi
    have hv : U.replacement x=Clipping.heightShield U.lo U.tree.a U.pc U.shield_offset H := by
      change SecondaryCell.replacement _ _ _ _ _ _ _ _ _ _ _ _ = _
      rw [← SecondaryCell.namedReplacement_value U.tree U.seeds U.old U.supportValue U.data.isOrdinary
        U.pc U.radius U.ordered_offset U.shield_offset U.lo U.noise x,hh]
      change Clipping.heightShield _ _ _ _ x.height = _
      rw [hheight]
    have h0 := U.patch_inside ω i H hd
    change _ ↔ Threshold.active _ H (κ*(U.data.offset+U.data.orientation U.positive*U.replacement x)) ω at h0
    rw [hv] at h0
    change _ ↔ Threshold.active _ H (κ*(OrdinaryData.initial M).value i ⟨H,hi⟩) ω
    have hz : (OrdinaryData.initial M).value i ⟨H,hi⟩ = 0 := OrdinaryData.initial_value M i H
    rw [hz,mul_zero]
    exact h0.trans ((S.labels U.index).active_rebase (K := U.shieldConstant) U.shield_strict U.shield_lipschitz H ω)
  · have hn' := congrArg PlanarL1.Interpolation.NamedValue.name hq
    change _=2 at hn'
    have ha0 : a.val≠0 := by omega
    have ha1 : a.val=1 := by omega
    simp only [newData,newLabels,ite_eq_right ha0,ite_eq_left ha1]
    refine ⟨⟨U.sub_old (SecondaryCell.inBand_of_mem U.seeds U.radius hd),trivial⟩,?_⟩
    intro ω hi
    have hv : U.replacement x=Clipping.orderedBranch U.pc U.radius U.ordered_offset U.supportValue x := by
      change SecondaryCell.replacement _ _ _ _ _ _ _ _ _ _ _ _ = _
      rw [← SecondaryCell.namedReplacement_value U.tree U.seeds U.old U.supportValue U.data.isOrdinary
        U.pc U.radius U.ordered_offset U.shield_offset U.lo U.noise x,hq]
    have h0 := U.patch_inside ω i H hd
    change _ ↔ Threshold.active _ H (κ*(U.data.offset+U.data.orientation U.positive*U.replacement x)) ω at h0
    rw [hv] at h0
    have he := OrderedData.secondaryInstall_value U.data.closed U.data.convex U.support U.lower U.upper
      U.support_ordered U.data.offset (U.data.orientation U.positive) U.pc U.radius U.ordered_offset
      (U.data.orientation_unit U.positive) lam i ⟨H,hi⟩
    change _ ↔ Threshold.active _ H (κ*U.orderedChart.value lam i ⟨H,hi⟩) ω
    rw [show U.orderedChart.value lam i ⟨H,hi⟩ = _ from he]
    have hs : U.supportValue x=U.support.value i ⟨H,hi⟩ := by
      dsimp only [supportValue]
      congr 1
      exact Subtype.ext hheight
    simp only [Clipping.orderedBranch,hs] at h0
    exact h0
  · have hn' := congrArg PlanarL1.Interpolation.NamedValue.name hp
    change _=(U.tree.pasted U.input U.noise x).name+3 at hn'
    have ha0 : a.val≠0 := by omega
    have ha1 : a.val≠1 := by omega
    have ha2 : a.val-2=(U.tree.pasted U.input U.noise x).name := by omega
    simp only [newData,newLabels,ite_eq_right ha0,ite_eq_right ha1,ha2]
    refine ⟨?_,?_⟩
    · change (U.tree.secondaryChart _ _ _ _ _ _ _ _).Contains i H
      simpa only [hcol,hheight] using U.tree.secondaryChart_contains U.data.offset
        (U.data.orientation U.positive) (U.data.orientation_unit U.positive) U.input U.noise U.pc U.radius x
    · intro ω hi
      obtain ⟨hb,hvalue⟩ := U.tree.secondaryChart_value U.data.offset (U.data.orientation U.positive)
        (U.data.orientation_unit U.positive) U.input U.noise U.pc U.radius x
      have hv : U.replacement x=SecondaryCell.shallow U.tree U.seeds U.pc U.radius U.noise x := by
        change SecondaryCell.replacement _ _ _ _ _ _ _ _ _ _ _ _ = _
        rw [← SecondaryCell.namedReplacement_value U.tree U.seeds U.old U.supportValue U.data.isOrdinary
          U.pc U.radius U.ordered_offset U.shield_offset U.lo U.noise x,hp]
      have h0 := U.patch_inside ω i H hd
      change _ ↔ Threshold.active _ H (κ*(U.data.offset+U.data.orientation U.positive*U.replacement x)) ω at h0
      rw [hv] at h0
      simp only [hcol,hheight] at hvalue
      exact h0.trans (Iff.of_eq (congrArg (fun p => Threshold.active (S.labels U.index).lift H (κ*p) ω)
        hvalue.symm))

lemma unchosen (ω : Ω × Bool) (i : Fin (k+1)) (H : ℝ) (hc : U.choose i H=none) :
    (U.patch.apply.activity ω).active i H ↔ (S.lift.sets.activity ω).active i H := by
  by_cases hd : H ∈ SecondaryCell.domain U.seeds U.radius i
  · have hn := SecondaryCell.choose_none U.tree U.seeds U.old U.supportValue U.data.isOrdinary
      U.pc U.radius U.ordered_offset U.shield_offset U.lo U.noise i H hd hc
    let x := SecondaryCell.point U.seeds U.radius i H hd
    change (SecondaryCell.namedReplacement U.tree U.seeds U.old U.supportValue U.data.isOrdinary
      U.pc U.radius U.ordered_offset U.shield_offset U.lo U.noise x).name=0 at hn
    have hv : U.replacement x=U.old x := by
      rcases SecondaryCell.namedReplacement_cases U.tree U.seeds U.old U.supportValue U.data.isOrdinary
        U.pc U.radius U.ordered_offset U.shield_offset U.lo U.noise x with ho | hh | hq | hp
      · change SecondaryCell.replacement _ _ _ _ _ _ _ _ _ _ _ _ = _
        rw [← SecondaryCell.namedReplacement_value U.tree U.seeds U.old U.supportValue U.data.isOrdinary
          U.pc U.radius U.ordered_offset U.shield_offset U.lo U.noise x,ho]
      · have he := congrArg PlanarL1.Interpolation.NamedValue.name hh
        change _=1 at he
        omega
      · have he := congrArg PlanarL1.Interpolation.NamedValue.name hq
        change _=2 at he
        omega
      · have he := congrArg PlanarL1.Interpolation.NamedValue.name hp
        change _=_+3 at he
        omega
    have ht := U.patch_inside ω i H hd
    change _ ↔ Threshold.active _ H (κ*(U.data.offset+U.data.orientation U.positive*U.replacement x)) ω at ht
    rw [hv] at ht
    exact ht.trans (U.old_agreement ω i H hd)
  · exact U.patch.unchanged hd ω

lemma choose_switch (i j : Fin (k+1)) (H : ℝ) (hs : H ∈ M.heights i j) : U.choose i H=U.choose j H :=
  SecondaryCell.choose_switch U.tree U.seeds U.old U.supportValue U.data.isOrdinary U.old_lipschitz
    U.support_lipschitz U.pc U.radius U.ordered_offset U.shield_offset U.lo U.noise_bounds i j H hs

/-- Actual one-group secondary installation with old identifiers retained and
fresh ordinary, ordered, and rebased height chart data supplied by their formulas. -/
noncomputable def apply [SFinite μ] : BState M κ lam (Ω × Bool) (μ.prod Threshold.fair) :=
  S.lift.append U.patch.apply (3*(k+1)*U.tree.depthCap+2) U.newData U.newLabels U.choose
    (fun i H a hc => (U.chosen_description i H a hc).1.1)
    (fun i H a hc => (U.chosen_description i H a hc).1.2)
    U.choose_switch U.unchosen
    (fun ω i H a hc => (U.chosen_description i H a hc).2 ω _)

lemma apply_sets [SFinite μ] : U.apply.sets=U.patch.apply := rfl

end SecondaryStep
end BState
end PlanarL1.Columns.Model

namespace PlanarL1.Columns.Model.BState.SecondaryStep
open MeasureTheory Set
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {κ : ℝ} {lam : ℝ≥0}
  {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {S : BState M κ lam Ω μ} {J : Set ℝ} {root : Fin (k+1)}
variable (U : SecondaryStep S J root)

lemma point_old {i : Fin (k+1)} {H : ℝ} (hd : H ∈ SecondaryCell.domain U.seeds U.radius i) :
    U.old (SecondaryCell.point U.seeds U.radius i H hd) =
      U.comparison.value i ⟨H,U.sub_old (SecondaryCell.inBand_of_mem U.seeds U.radius hd)⟩ := by
  simp only [old,SecondaryCell.point_column,SecondaryCell.point_height]

lemma replacement_lipschitz : LipschitzWith (SecondaryCell.replacementConstant U.tree) U.replacement :=
  SecondaryCell.replacement_lipschitz U.tree U.seeds U.old U.supportValue U.data.isOrdinary
    U.old_lipschitz U.support_lipschitz U.pc U.radius U.ordered_offset U.shield_offset U.lo U.noise_bounds

lemma replacement_frontier {i : Fin (k+1)} {H : ℝ}
    (hf : H ∈ frontier (SecondaryCell.domain U.seeds U.radius i))
    (hd : H ∈ SecondaryCell.domain U.seeds U.radius i) :
    U.replacement (SecondaryCell.point U.seeds U.radius i H hd) =
      U.old (SecondaryCell.point U.seeds U.radius i H hd) := by
  obtain ⟨_,he⟩ := SecondaryCell.equal_radius_or_endpoint U.seeds U.radius U.compact_band U.lo U.tree.a
    U.tree.width_pos U.band_eq hf
  rcases he with he | he
  · exact SecondaryCell.replacement_boundary U.tree U.seeds U.old U.supportValue U.data.isOrdinary
      U.seeds_nonempty U.zeta_eq U.radius_nonneg U.ordered_bound U.delta_eq U.noise_bounds
      U.support_le U.admitted U.shield_offset U.lo he
  · exact SecondaryCell.replacement_endpoint U.tree U.seeds U.old U.supportValue U.data.isOrdinary
      U.seeds_nonempty U.old_lipschitz U.radius_small U.shield_bound U.seed_near U.noise
      (SecondaryCell.point_distance U.seeds U.radius hd)
      (by rw [SecondaryCell.point_height U.seeds U.radius hd]; exact he)

/-- The literal clamped proposal, extended by the old comparison on the rest
of the old band. This is the extension whose finite maximum is required for
simultaneous overlapping secondary groups. -/
noncomputable def fullReplacement (i : Fin (k+1)) (H : U.data.band) : ℝ :=
  if hd : H.val ∈ SecondaryCell.domain U.seeds U.radius i then
    U.replacement (SecondaryCell.point U.seeds U.radius i H.val hd)
  else U.comparison.value i H

lemma fullReplacement_inside (i : Fin (k+1)) (H : U.data.band)
    (hd : H.val ∈ SecondaryCell.domain U.seeds U.radius i) :
    U.fullReplacement i H=U.replacement (SecondaryCell.point U.seeds U.radius i H.val hd) := dite_eq_left hd

lemma fullReplacement_outside (i : Fin (k+1)) (H : U.data.band)
    (hd : H.val ∉ SecondaryCell.domain U.seeds U.radius i) :
    U.fullReplacement i H=U.comparison.value i H := dite_eq_right hd

lemma fullReplacement_ge (i : Fin (k+1)) (H : U.data.band) :
    U.comparison.value i H ≤ U.fullReplacement i H := by
  by_cases hd : H.val ∈ SecondaryCell.domain U.seeds U.radius i
  · rw [U.fullReplacement_inside i H hd,← U.point_old hd]
    exact le_max_left _ _
  · rw [U.fullReplacement_outside i H hd]

lemma fullReplacement_vertical (i : Fin (k+1)) :
    LipschitzWith (SecondaryCell.replacementConstant U.tree) (U.fullReplacement i) := by
  let oldColumn (H : ℝ) := if h : H ∈ U.data.band then U.comparison.value i ⟨H,h⟩ else 0
  have ho : LipschitzOnWith 5 oldColumn U.data.band := by
    apply LipschitzOnWith.of_dist_le_mul
    intro H hH T hT
    simpa only [oldColumn,dite_eq_left hH,dite_eq_left hT,Subtype.dist_eq] using
      (U.comparison.vertical i).dist_le_mul ⟨H,hH⟩ ⟨T,hT⟩
  obtain ⟨g,hg,he⟩ := ho.extend_real
  let proposal (H : ℝ) := if hd : H ∈ SecondaryCell.domain U.seeds U.radius i then
    U.replacement (SecondaryCell.point U.seeds U.radius i H hd) else 0
  have hp : LipschitzOnWith (SecondaryCell.replacementConstant U.tree) proposal
      (SecondaryCell.domain U.seeds U.radius i) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro H hH T hT
    have h := U.replacement_lipschitz.dist_le_mul
      (SecondaryCell.point U.seeds U.radius i H hH) (SecondaryCell.point U.seeds U.radius i T hT)
    simpa only [proposal,dite_eq_left hH,dite_eq_left hT,SecondaryCell.point_dist,Real.dist_eq] using h
  have hb : EqOn proposal g (frontier (SecondaryCell.domain U.seeds U.radius i)) := by
    intro H hH
    have hd := (SecondaryCell.compact_domain U.seeds U.radius U.compact_band i).isClosed.frontier_subset hH
    have hi := U.sub_old (SecondaryCell.inBand_of_mem U.seeds U.radius hd)
    simp only [proposal,dite_eq_left hd,U.replacement_frontier hH hd,U.point_old hd]
    have hv : oldColumn H = U.comparison.value i ⟨H,hi⟩ := dite_eq_left hi
    exact hv.symm.trans (he hi)
  have hl := PlanarL1.Gluing.lipschitz_piecewise
    (SecondaryCell.compact_domain U.seeds U.radius U.compact_band i).isClosed
    (hg.weaken (show (5:ℝ≥0) ≤ SecondaryCell.replacementConstant U.tree from le_max_left _ _)) hp hb
  have hv (H : U.data.band) : U.fullReplacement i H=
      (SecondaryCell.domain U.seeds U.radius i).piecewise proposal g H.val := by
    by_cases hd : H.val ∈ SecondaryCell.domain U.seeds U.radius i
    · simp only [fullReplacement,dite_eq_left hd,piecewise_eq_of_mem _ _ _ hd,proposal]
    · rw [U.fullReplacement_outside i H hd,piecewise_eq_of_notMem _ _ _ hd]
      simpa only [oldColumn,dite_eq_left H.property] using he H.property
  apply LipschitzWith.of_dist_le_mul
  intro H T
  rw [hv H,hv T]
  exact hl.dist_le_mul H.val T.val

lemma fullReplacement_switch (i j : Fin (k+1)) (H : U.data.band)
    (hs : H.val ∈ M.heights i j) : U.fullReplacement i H=U.fullReplacement j H := by
  by_cases hi : H.val ∈ SecondaryCell.domain U.seeds U.radius i
  · have hj := SecondaryCell.switch_mem U.seeds U.radius hs hi
    rw [U.fullReplacement_inside i H hi,U.fullReplacement_inside j H hj]
    apply dist_le_zero.mp
    have h := U.replacement_lipschitz.dist_le_mul
      (SecondaryCell.point U.seeds U.radius i H.val hi) (SecondaryCell.point U.seeds U.radius j H.val hj)
    simpa only [SecondaryCell.point_dist_switch U.seeds hi hj hs,mul_zero] using h
  · have hj : H.val ∉ SecondaryCell.domain U.seeds U.radius j := fun hj => hi
      (SecondaryCell.switch_mem U.seeds U.radius (M.symm i j ▸ hs) hj)
    rw [U.fullReplacement_outside i H hi,U.fullReplacement_outside j H hj]
    exact U.comparison.switch i j H hs

noncomputable def fullField : M.Field U.data.band (SecondaryCell.replacementConstant U.tree) where
  value := U.fullReplacement
  vertical := U.fullReplacement_vertical
  switch := U.fullReplacement_switch

end PlanarL1.Columns.Model.BState.SecondaryStep

namespace PlanarL1.Columns.Model.BState.SecondaryStep
open MeasureTheory Set
open scoped NNReal
open PlanarL1.Interpolation
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {κ : ℝ} {lam : ℝ≥0}
  {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {S : BState M κ lam Ω μ} {J : Set ℝ} {root : Fin (k+1)}
variable (U : SecondaryStep S J root)

noncomputable def fullNamed (i : Fin (k+1)) (H : U.data.band) : NamedValue :=
  if hd : H.val ∈ SecondaryCell.domain U.seeds U.radius i then
    U.named (SecondaryCell.point U.seeds U.radius i H.val hd)
  else ⟨0,U.comparison.value i H⟩

lemma fullNamed_value (i : Fin (k+1)) (H : U.data.band) :
    (U.fullNamed i H).value = U.fullReplacement i H := by
  unfold fullNamed fullReplacement
  split_ifs with hd
  · exact SecondaryCell.namedReplacement_value _ _ _ _ _ _ _ _ _ _ _ _
  · rfl

lemma fullNamed_switch (i j : Fin (k+1)) (H : U.data.band)
    (hs : H.val ∈ M.heights i j) : U.fullNamed i H=U.fullNamed j H := by
  by_cases hi : H.val ∈ SecondaryCell.domain U.seeds U.radius i
  · have hj := SecondaryCell.switch_mem U.seeds U.radius hs hi
    simp only [fullNamed,dite_eq_left hi,dite_eq_left hj]
    exact SecondaryCell.namedReplacement_congr_zero U.tree U.seeds U.old U.supportValue U.data.isOrdinary
      U.old_lipschitz U.support_lipschitz U.pc U.radius U.ordered_offset U.shield_offset U.lo U.noise_bounds
      _ _ (SecondaryCell.point_dist_switch U.seeds hi hj hs)
  · have hj : H.val ∉ SecondaryCell.domain U.seeds U.radius j := fun hj => hi
      (SecondaryCell.switch_mem U.seeds U.radius (M.symm i j ▸ hs) hj)
    simp only [fullNamed,dite_eq_right hi,dite_eq_right hj,U.comparison.switch i j H hs]

lemma fullNamed_zero (i : Fin (k+1)) (H : U.data.band)
    (h : (U.fullNamed i H).name=0) :
    (U.fullNamed i H).value=U.comparison.value i H := by
  by_cases hd : H.val ∈ SecondaryCell.domain U.seeds U.radius i
  · simp only [fullNamed,dite_eq_left hd] at h ⊢
    rw [← U.point_old hd]
    rcases SecondaryCell.namedReplacement_cases U.tree U.seeds U.old U.supportValue U.data.isOrdinary
      U.pc U.radius U.ordered_offset U.shield_offset U.lo U.noise
      (SecondaryCell.point U.seeds U.radius i H.val hd) with ho | hh | hq | hp
    · exact congrArg NamedValue.value ho
    · change (U.named _).name=0 at h
      have hn := congrArg NamedValue.name hh
      change (U.named _).name=1 at hn
      omega
    · have hn := congrArg NamedValue.name hq
      change (U.named _).name=2 at hn
      omega
    · have hn := congrArg NamedValue.name hp
      change (U.named _).name=_+3 at hn
      omega
  · simp only [fullNamed,dite_eq_right hd]

lemma fullNamed_choice (i : Fin (k+1)) (H : U.data.band)
    (h : (U.fullNamed i H).name ≠ 0) :
    ∃ a, U.choose i H.val=some a ∧ (U.fullNamed i H).name=a.val+1 ∧
      H.val ∈ SecondaryCell.domain U.seeds U.radius i := by
  have hd : H.val ∈ SecondaryCell.domain U.seeds U.radius i := by
    by_contra hd
    simp only [fullNamed,dite_eq_right hd] at h
    exact h rfl
  have ht : (U.named (SecondaryCell.point U.seeds U.radius i H.val hd)).name ≠ 0 := by
    simpa only [fullNamed,dite_eq_left hd] using h
  let a : Fin (3*(k+1)*U.tree.depthCap+2) :=
    ⟨(U.named (SecondaryCell.point U.seeds U.radius i H.val hd)).name-1,by
      have hb := SecondaryCell.namedReplacement_bound U.tree U.seeds U.old U.supportValue U.data.isOrdinary
        U.pc U.radius U.ordered_offset U.shield_offset U.lo U.noise
        (SecondaryCell.point U.seeds U.radius i H.val hd)
      change (U.named _).name < _ at hb
      omega⟩
  refine ⟨a,?_,?_,hd⟩
  · change (SecondaryCell.namedReplacement _ _ _ _ _ _ _ _ _ _ _ _).name ≠ 0 at ht
    simp only [choose,SecondaryCell.choose,dite_eq_left hd,dite_eq_right ht]
    rfl
  · simp only [fullNamed,dite_eq_left hd,a]
    omega

lemma fullReplacement_scaled_vertical (i : Fin (k+1)) :
    LipschitzWith 1 (fun H : U.data.band => κ*U.fullReplacement i H) := by
  apply LipschitzWith.of_dist_le_mul
  intro H T
  have h := (U.fullReplacement_vertical i).dist_le_mul H T
  rw [Real.dist_eq] at h ⊢
  rw [← mul_sub,abs_mul,abs_of_nonneg U.kappa_nonneg]
  calc
    _ ≤ κ*((SecondaryCell.replacementConstant U.tree : ℝ)*dist H T) :=
      mul_le_mul_of_nonneg_left h U.kappa_nonneg
    _ = (κ*(SecondaryCell.replacementConstant U.tree : ℝ))*dist H T := by ring
    _ ≤ 1*dist H T := mul_le_mul_of_nonneg_right U.vertical_bound dist_nonneg
    _ = _ := by simp

end PlanarL1.Columns.Model.BState.SecondaryStep


end

end OAI
