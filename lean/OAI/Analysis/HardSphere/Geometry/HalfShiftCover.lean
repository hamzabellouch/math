import Mathlib
import OAI.Analysis.HardSphere.Geometry.CubeCell

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open Set Function MeasureTheory
open scoped ENNReal
namespace HardSphere.GridGeometry

lemma half_shift_cover {x y : ℝ} (h : |x-y|<1/2) :
    ⌊x⌋=⌊y⌋ ∨ ⌊x-1/2⌋=⌊y-1/2⌋ := by
  wlog hxy : x≤y
  · have he := this (x := y) (y := x) (by simpa only [abs_sub_comm] using h) (le_of_not_ge hxy)
    exact he.imp Eq.symm Eq.symm
  have hx := Int.floor_le x
  have hx' := Int.lt_floor_add_one x
  have hd := (abs_lt.mp h).1
  by_cases hy : y<(⌊x⌋:ℝ)+1
  · left
    exact (Int.floor_eq_iff.mpr ⟨hx.trans hxy,hy⟩).symm
  · right
    have hxf : ⌊x-1/2⌋=⌊x⌋ := Int.floor_eq_iff.mpr ⟨by linarith,by linarith⟩
    have hyf : ⌊y-1/2⌋=⌊x⌋ := Int.floor_eq_iff.mpr ⟨by linarith,by linarith⟩
    exact hxf.trans hyf.symm

lemma floor_grid_periodic {j : ℕ} {L l : ℝ} (hl : 0<l) (hL : L=(j:ℝ)*l) (b : ℝ) :
    Function.Periodic (fun x : ℝ ↦ (⌊(x-b)/l⌋ : ZMod j)) L := by
  intro x
  have he : (x+L-b)/l=(x-b)/l+(j:ℝ) := by rw [hL]; field_simp; ring
  change (⌊(x+L-b)/l⌋ : ZMod j)=(⌊(x-b)/l⌋ : ZMod j)
  rw [he,Int.floor_add_natCast,Int.cast_add]
  simp

noncomputable def index {j : ℕ} {L l : ℝ} (hl : 0<l) (hL : L=(j:ℝ)*l) (b : ℝ) :
    AddCircle L → ZMod j := (floor_grid_periodic hl hL b).lift

lemma index_coe {j : ℕ} {L l : ℝ} (hl : 0<l) (hL : L=(j:ℝ)*l) (b x : ℝ) :
    index hl hL b (x : AddCircle L)=(⌊(x-b)/l⌋ : ZMod j) := rfl

lemma index_pair_cover {j : ℕ} {L l : ℝ} (hl : 0<l) (hL : L=(j:ℝ)*l)
    (x y : AddCircle L) (hd : dist x y<l/2) :
    index hl hL 0 x=index hl hL 0 y ∨
      index hl hL (l/2) x=index hl hL (l/2) y := by
  obtain ⟨d,hdq,hdr⟩ := QuotientAddGroup.exists_norm_mk_lt (x-y) (sub_pos.mpr hd)
  obtain ⟨v,rfl⟩ := QuotientAddGroup.mk_surjective y
  have he : ((d+v : ℝ) : AddCircle L)=x := by
    rw [QuotientAddGroup.mk_add,hdq]
    abel
  rw [←he]
  simp only [index_coe]
  have hb : |(d+v)/l-v/l|<1/2 := by
    rw [← sub_div,add_sub_cancel_right,abs_div,abs_of_pos hl,div_lt_iff₀ hl]
    have hn : |d|<l/2 := by
      rw [Real.norm_eq_abs,←dist_eq_norm] at hdr
      linarith
    linarith
  have hg := half_shift_cover hb
  rcases hg with hg | hg
  · left
    simpa only [sub_zero] using congrArg (fun z : ℤ ↦ (z : ZMod j)) hg
  · right
    have h₁ : (d+v-l/2)/l=(d+v)/l-1/2 := by field_simp
    have h₂ : (v-l/2)/l=v/l-1/2 := by field_simp
    rw [h₁,h₂]
    exact congrArg (fun z : ℤ ↦ (z : ZMod j)) hg

lemma measurable_index {j : ℕ} {L l : ℝ} [Fact (0<L)] (hl : 0<l) (hL : L=(j:ℝ)*l) (b : ℝ) :
    Measurable (index hl hL b) := by
  have he : index hl hL b=(fun x : AddCircle L ↦ (⌊(((AddCircle.equivIco L 0) x).val-b)/l⌋ : ZMod j)) := by
    funext x
    rw [← AddCircle.coe_equivIco (p := L) (a := 0) (y := x),index_coe]
    simp only [AddCircle.coe_equivIco]
  rw [he]
  have hm := ((measurable_subtype_coe.comp (AddCircle.measurableEquivIco L 0).measurable).sub_const b).div_const l
  exact (measurable_of_countable (fun z : ℤ ↦ (z : ZMod j))).comp hm.floor

lemma index_in_cell {j : ℕ} [NeZero j] {L l : ℝ} (hl : 0<l) (hL : L=(j:ℝ)*l)
    (b : ℝ) (v : Fin j) {x : ℝ} (hx : x∈Ico (b+(v:ℝ)*l) (b+(v:ℝ)*l+l)) :
    index hl hL b (x : AddCircle L)=ZMod.finEquiv j v := by
  rw [index_coe]
  have he : ⌊(x-b)/l⌋=(v.val:ℤ) := Int.floor_eq_iff.mpr ⟨by
    rw [Int.cast_natCast,le_div_iff₀ hl]; linarith [hx.1],by
    rw [Int.cast_natCast,div_lt_iff₀ hl]; nlinarith [hx.2]⟩
  rw [he,Int.cast_natCast]
  apply ZMod.val_injective j
  rw [ZMod.val_natCast_of_lt v.isLt]
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne j)
  rfl
end HardSphere.GridGeometry
namespace HardSphere.SphericalCoordinates
open scoped BigOperators
lemma pointFin_preserving_base (b : Point) (h : ℝ) :
    MeasurePreserving pointFin (volume.restrict (cube b h))
      (Measure.pi (fun q : Fin 3 ↦ (volume : Measure ℝ).restrict (Icc (pointFin b q) (pointFin b q+h)))) := by
  rw [cube_volume]
  let μ := fun q : Fin 3 ↦ (volume : Measure ℝ).restrict (Icc (pointFin b q) (pointFin b q+h))
  have hp := (measurePreserving_piFinSuccAbove μ 0).symm
  have hq := (MeasurePreserving.id (μ 0)).prod (measurePreserving_piFinTwo (fun q : Fin 2 ↦ μ (Fin.succ q))).symm
  convert hp.comp hq using 1 <;> try rfl
  funext x i
  fin_cases i <;> rfl

lemma configurationFin_preserving_base (n : ℕ) (b : Point) (h : ℝ) :
    MeasurePreserving (configurationFin n)
      (Measure.pi (fun _ : Fin n ↦ volume.restrict (cube b h)))
      (Measure.pi (fun _ : Fin n ↦ Measure.pi (fun q : Fin 3 ↦ (volume : Measure ℝ).restrict (Icc (pointFin b q) (pointFin b q+h))))) :=
  measurePreserving_pi _ _ (fun _ ↦ pointFin_preserving_base b h)
end HardSphere.SphericalCoordinates

namespace HardSphere
open SphericalCoordinates
open scoped BigOperators
lemma cubeParameter_preserving_base (n : ℕ) (L : Length) (b : Point) :
    MeasurePreserving (cubeParameter n L)
      (Measure.pi (fun _ : Fin n ↦ volume.restrict (cube b L.val))) volume := by
  have hp := measurePreserving_pi (fun q : Fin 3 ↦ (volume : Measure ℝ).restrict (Icc (pointFin b q) (pointFin b q+L.val)))
    (fun _ : Fin 3 ↦ (volume : Measure (AddCircle L.val)))
    (f := fun _ x ↦ (x : AddCircle L.val)) (fun q ↦ by
      simpa only [restrict_Ioc_eq_restrict_Icc] using AddCircle.measurePreserving_mk L.val (pointFin b q))
  exact (measurePreserving_pi _ _ (fun _ : Fin n ↦ hp)).comp (configurationFin_preserving_base n b L.val)

noncomputable def gridSectorMeasure (n j : ℕ) (b : Point) (l : ℝ) (σ : Fin n → CubeCell j) : Measure (Fin n → Point) :=
  Measure.pi (fun i ↦ volume.restrict (cube (subcubeBase b l (σ i)) l))

lemma gridSectorMeasure_le {n j : ℕ} {L : Length} {l : ℝ} (hl : 0≤l) (hL : L.val=(j:ℝ)*l) (b : Point) (σ : Fin n → CubeCell j) :
    gridSectorMeasure n j b l σ≤Measure.pi (fun _ : Fin n ↦ volume.restrict (cube b L.val)) := by
  rw [hL,cube_configuration_subdivision b hl]
  exact Measure.le_sum _ σ

noncomputable def gridSectorRestriction {n j : ℕ} {L : Length} {l : ℝ} (hl : 0≤l) (hL : L.val=(j:ℝ)*l)
    (b : Point) (σ : Fin n → CubeCell j) : ScalarL2 n L →L[ℝ] Lp ℂ 2 (gridSectorMeasure n j b l σ) :=
  (Lp.LpToLpOfMeasureLeSMul (c := (1:ℝ≥0∞)) (by norm_num)
    (show gridSectorMeasure n j b l σ≤1 • Measure.pi (fun _ : Fin n ↦ volume.restrict (cube b L.val)) by
      simpa only [one_smul] using gridSectorMeasure_le hl hL b σ)).comp
    (Lp.compMeasurePreservingₗᵢ ℝ (cubeParameter n L) (cubeParameter_preserving_base n L b)).toContinuousLinearMap

lemma gridSectorRestriction_ae {n j : ℕ} {L : Length} {l : ℝ} (hl : 0≤l) (hL : L.val=(j:ℝ)*l)
    (b : Point) (σ : Fin n → CubeCell j) (u : ScalarL2 n L) :
    gridSectorRestriction hl hL b σ u=ᵐ[gridSectorMeasure n j b l σ] fun X ↦ u (cubeParameter n L X) := by
  have h₁ := Lp.coeFn_LpToLpOfMeasureLeSMul (c := (1:ℝ≥0∞)) (by norm_num)
    (show gridSectorMeasure n j b l σ≤1 • Measure.pi (fun _ : Fin n ↦ volume.restrict (cube b L.val)) by
      simpa only [one_smul] using gridSectorMeasure_le hl hL b σ)
    ((Lp.compMeasurePreservingₗᵢ ℝ (cubeParameter n L) (cubeParameter_preserving_base n L b)) u)
  apply h₁.trans
  apply (Measure.absolutelyContinuous_of_le (gridSectorMeasure_le hl hL b σ)).ae_eq
  exact Lp.coeFn_compMeasurePreserving u (cubeParameter_preserving_base n L b)

lemma gridSector_norm {n j : ℕ} {L : Length} {l : ℝ} (hl : 0≤l) (hL : L.val=(j:ℝ)*l)
    (b : Point) (σ : Fin n → CubeCell j) (u : ScalarL2 n L) :
    ENNReal.ofReal (‖gridSectorRestriction hl hL b σ u‖^2)=
      ∫⁻ X,ENNReal.ofReal (‖u (cubeParameter n L X)‖^2) ∂gridSectorMeasure n j b l σ := by
  have hn := smooth_norm_lintegral (Lp.memLp (gridSectorRestriction hl hL b σ u))
  rw [Lp.toLp_coeFn] at hn
  rw [hn]
  apply lintegral_congr_ae
  filter_upwards [gridSectorRestriction_ae hl hL b σ u] with X hX
  rw [hX]

lemma SmoothTest.gridSector_norm {n j : ℕ} {L : Length} {a l : ℝ} (f : SmoothTest n L a)
    (hl : 0≤l) (hL : L.val=(j:ℝ)*l) (b : Point) (σ : Fin n → CubeCell j) :
    ENNReal.ofReal (‖gridSectorRestriction hl hL b σ f.jet.1‖^2)=
      ∫⁻ X,ENNReal.ofReal (‖f.toFun (cubeParameter n L X)‖^2) ∂gridSectorMeasure n j b l σ := by
  rw [HardSphere.gridSector_norm]
  apply lintegral_congr_ae
  have h₂ : (fun X ↦ f.jet.1 (cubeParameter n L X))=ᵐ[gridSectorMeasure n j b l σ]
      fun X ↦ f.toFun (cubeParameter n L X) := by
    apply (Measure.absolutelyContinuous_of_le (gridSectorMeasure_le hl hL b σ)).ae_eq
    exact (cubeParameter_preserving_base n L b).quasiMeasurePreserving.ae_eq_comp f.memLp.coeFn_toLp
  filter_upwards [h₂] with X hX
  rw [hX]

lemma SmoothTest.cube_gradient_lintegral_base {n : ℕ} {L : Length} {a : ℝ} (f : SmoothTest n L a)
    (b : Point) (i : Fin n) :
    (∫⁻ X, ENNReal.ofReal (particleGradSq (fun X ↦ f.toFun (cubeParameter n L X)) i X)
      ∂Measure.pi (fun _ ↦ volume.restrict (cube b L.val)))=
        ∑ q : Fin 3, ENNReal.ofReal (‖f.jet.2 (i,q)‖^2) := by
  simp_rw [f.cube_gradient,ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ sq_nonneg _)]
  rw [lintegral_finsetSum _ (fun q _ ↦ by
    exact (((f.continuous_partial (i,q)).measurable.comp (cubeParameter_preserving_base n L b).measurable).norm.pow_const 2).ennreal_ofReal)]
  apply Finset.sum_congr rfl
  intro q _
  rw [(cubeParameter_preserving_base n L b).lintegral_comp
    (f := fun x ↦ ENNReal.ofReal (‖coordDerivative n L f.toFun (i,q) x‖^2))
    (((f.continuous_partial (i,q)).measurable.norm.pow_const 2).ennreal_ofReal),← smooth_norm_lintegral (f.partial_memLp (i,q))]
  rfl
end HardSphere

end

end OAI
