import Mathlib
import OAI.Geometry.CAT0Fillings.Charts.DomainRestriction
import OAI.Geometry.CAT0Fillings.Charts.Reparametrization
import OAI.Geometry.CAT0Fillings.Charts.StraightPieces
import OAI.Geometry.CAT0Fillings.Currents.DisjointUnions

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings.IntegerChart
open Set MeasureTheory Filter BorelRestriction EuclideanStraightening
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ}
omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma paramExtended_disjoint_images (C : IntegerChart X k) {s t : Set (Euc k)}
    (hs : s ⊆ C.domain) (ht : t ⊆ C.domain) (hd : Disjoint s t) :
    Disjoint (C.paramExtended '' s) (C.paramExtended '' t) := by
  rw [Set.disjoint_left] at hd ⊢
  rintro _ ⟨x,hx,rfl⟩ ⟨y,hy,heq⟩
  have hy' : C.paramExtended x ∈ C.paramExtended '' t := ⟨y,hy,heq⟩
  exact hd hx ((C.paramExtended_mem_image_iff ht (hs hx)).mp hy')

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma restrictDomain_image (C : IntegerChart X k) {t : Set (Euc k)}
    (ht : MeasurableSet t) (hts : t ⊆ C.domain) :
    (C.restrictDomain ht hts).image = C.paramExtended '' t := by
  ext x
  constructor
  · rintro ⟨z,rfl⟩
    exact ⟨z,z.property,by simp [paramExtended,restrictDomain,hts z.property]⟩
  · rintro ⟨z,hz,rfl⟩
    refine ⟨⟨z,hz⟩,?_⟩
    simp [paramExtended,restrictDomain,hts hz]

theorem exists_scalar_straightened_charts (C : IntegerChart X (k+1))
    {u : X → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u) :
    ∃ D : ℕ → IntegerChart X (k+1),
      Pairwise (fun i j => Disjoint (D i).image (D j).image) ∧
      (∀ i, (D i).image ⊆ C.image) ∧
      (∀ i z (hz : z ∈ (D i).domain),
        u ((D i).param ⟨z,hz⟩) = (Prism.split k z).1) ∧
      Summable (fun i => mass (D i).action) ∧
      (∑' i, mass (D i).action) ≤ mass C.action ∧
      ∀ b π, Admissible b π →
        C.action b (Matrix.vecCons u π) = ∑' i, (D i).action b (Matrix.vecCons u π) := by
  classical
  obtain ⟨L,U,hL,_hU⟩ := C.bilipschitz
  obtain ⟨g,hg,hug⟩ := (C.scalar_lipschitzOn hL hK).extend_real
  obtain ⟨t,dir,J,hts,ht,hd,hbilip,hzero⟩ :=
    exists_straightened_pieces C.borel C.bounded.measure_lt_top.ne hg
  let E i := C.paramExtended '' t i
  have hE i : MeasurableSet (E i) := C.measurableSet_paramExtended_image (ht i) (hts i)
  have hEd : Pairwise (fun i j => Disjoint (E i) (E j)) :=
    fun i j hij => C.paramExtended_disjoint_images (hts i) (hts j) (hd hij)
  let R i := C.restrictDomain (ht i) (hts i)
  let F i := straightenMap (dir i) g
  have hF i : LipschitzOnWith
      (1+K*L+‖(EuclideanSpace.proj (dir i) : Euc (k+1) →L[ℝ] ℝ)‖₊) (F i) (R i).domain :=
    lipschitzOnWith_iff_restrict.mpr (hbilip i).1
  have hA i : ∀ x ∈ (R i).domain, ∀ y ∈ (R i).domain,
      dist x y ≤ (J i:ℝ) * dist (F i x) (F i y) := by
    intro x hx y hy
    exact (hbilip i).2.le_mul_dist ⟨x,hx⟩ ⟨y,hy⟩
  let D i := (R i).reparam (F i) (hF i) (hA i)
  have hDact i : (D i).action = restrictCurrent C.action_isMetricCurrent (E i) := by
    rw [show (D i).action = (R i).action from (R i).reparam_action _ _ _]
    exact C.restrictDomain_action _ _ C.action_isMetricCurrent
  have hDimage i : (D i).image = E i := by
    rw [show (D i).image = (R i).image from (R i).reparam_image _ _ _]
    exact C.restrictDomain_image _ _
  refine ⟨D,?_,?_,?_,?_,?_,?_⟩
  · intro i j hij
    rw [hDimage,hDimage]
    exact hEd hij
  · intro i x hx
    rw [hDimage] at hx
    obtain ⟨z,hz,rfl⟩ := hx
    exact ⟨⟨z,hts i hz⟩,by simp [paramExtended,hts i hz]⟩
  · intro i y hy
    let x := Function.invFunOn (F i) (R i).domain y
    have hx : x ∈ (R i).domain := Function.invFunOn_mem hy
    have heq : F i x = y := Function.invFunOn_eq hy
    change u (C.param ⟨x,hts i hx⟩) = (Prism.split k y).1
    have hcx : x ∈ C.domain := hts i hx
    calc
      u (C.param ⟨x,hcx⟩) = C.scalar u x := (C.scalar_eq (f := u) hcx).symm
      _ = g x := hug hcx
      _ = (Prism.split k y).1 := by
        have hc := congrArg (fun w : Euc (k+1) => w 0) heq
        simpa only [F,straightenMap_zero,Prism.split_apply] using hc
  · simp_rw [hDact]
    exact summable_restriction_mass C.action_isMetricCurrent E hE hEd
  · simp_rw [hDact]
    exact tsum_restriction_mass_le C.action_isMetricCurrent E hE hEd
  · intro b π hab
    have hab' : Admissible b (Matrix.vecCons u π) := ⟨hab.1,fun i => by
      cases i using Fin.cases with
      | zero => exact ⟨K,hK⟩
      | succ i => exact hab.2 i⟩
    simp_rw [hDact]
    rw [←restrictCurrent_iUnion C.action_isMetricCurrent E hE hEd,
      ←C.restrictMultiplicity_action C.action_isMetricCurrent (MeasurableSet.iUnion hE)]
    rw [action,action,ite_eq_left hab',ite_eq_left hab']
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem C.borel,hzero,
      ae_fderivWithin_eq_fderiv_extension volume C.borel hg hug] with z hz hz0 hder
    change (C.multiplicity z:ℝ)*C.scalar b z*C.jacobian (Matrix.vecCons u π) z =
      ↑((C.paramExtended ⁻¹' ⋃ i, E i).indicator C.multiplicity z)*
        C.scalar b z*C.jacobian (Matrix.vecCons u π) z
    by_cases hzi : z ∈ ⋃ i, t i
    · have him : z ∈ C.paramExtended ⁻¹' ⋃ i, E i := by
        obtain ⟨i,hi⟩ := mem_iUnion.mp hzi
        exact mem_iUnion.mpr ⟨i,⟨z,hi,rfl⟩⟩
      rw [indicator_of_mem him]
    · have hj : C.jacobian (Matrix.vecCons u π) z = 0 := by
        apply Matrix.det_eq_zero_of_row_eq_zero 0
        intro j
        change (fderivWithin ℝ (C.scalar u) C.domain z) (EuclideanSpace.single j 1) = 0
        rw [hder,hz0 hzi]
        rfl
      rw [hj,mul_zero,mul_zero]

end CAT0Fillings.IntegerChart

end

end OAI
