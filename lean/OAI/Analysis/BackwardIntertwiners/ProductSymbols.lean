import OAI.Analysis.BackwardIntertwiners.AtomicAlgebras

namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

open Topology MeasureTheory Set
open scoped ENNReal

open scoped Classical

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] realOperatorTower realOperatorCommute complexNormalCalculus complexClosedCalculus realSelfAdjointCalculus

open InnerProductSpace ContinuousLinearMap

lemma linfty_ae_norm_le {X : Type*} [MeasurableSpace X] {μ : Measure X} (g : Lp ℂ ∞ μ) :
    ∀ᵐ z ∂μ, ‖g z‖ ≤ ‖g‖ := by
  filter_upwards [enorm_ae_le_eLpNormEssSup g μ] with z hz
  have hg : eLpNormEssSup g μ ≠ ∞ := by
    simpa only [eLpNorm_exponent_top (Lp.aestronglyMeasurable g)] using Lp.eLpNorm_ne_top g
  have hh := ENNReal.toReal_mono hg hz
  simpa only [Lp.norm_def,eLpNorm_exponent_top (Lp.aestronglyMeasurable g), toReal_enorm] using hh

lemma ae_prod_count_iff {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {p : X × ℤ → Prop} (hp : MeasurableSet {z | p z}) :
    (∀ᵐ z ∂μ.prod Measure.count, p z) ↔ ∀ᵐ x ∂μ, ∀ j : ℤ, p (x,j) := by
  rw [Measure.ae_prod_iff_ae_ae hp]
  simp_rw [Measure.ae_count_iff]



abbrev productMeasure : Measure (Base × ℤ) := baseMeasure.prod Measure.count

def IsProductMultiplier (T : GlobalHilbert →L[ℂ] GlobalHilbert) : Prop :=
  ∃ g : Lp ℂ ∞ productMeasure, ∀ f : GlobalHilbert,
    ∀ᵐ x ∂baseMeasure, ∀ j : ℤ, T f x j = g (x,j) * f x j

lemma DiagonalSymbol.product_measurable (a : DiagonalSymbol) :
    Measurable (fun z : Base × ℤ => a z.1 z.2) :=
  measurable_from_prod_countable_left a.measurable
lemma DiagonalSymbol.product_memLp (a : DiagonalSymbol) :
    MemLp (fun z : Base × ℤ => a z.1 z.2) ∞ productMeasure :=
  memLp_top_of_bound a.product_measurable.aestronglyMeasurable a.bound
    (Eventually.of_forall fun z => a.norm_le_bound z.1 z.2)
lemma diagonalOperator_isProductMultiplier (a : DiagonalSymbol) :
    IsProductMultiplier (diagonalOperator a) := by
  let g : Lp ℂ ∞ productMeasure := a.product_memLp.toLp (fun z : Base × ℤ => a z.1 z.2)
  have hg : ∀ᵐ x ∂baseMeasure, ∀ j : ℤ, g (x,j) = a x j := by
    have hh := Measure.ae_ae_of_ae_prod (MemLp.coeFn_toLp a.product_memLp)
    simpa only [Measure.ae_count_iff] using hh
  refine ⟨g,fun f => ?_⟩
  filter_upwards [diagonalOperator_coord a f,hg] with x hx hgx j
  rw [hx,hgx]

def productBoundedSymbol (g : Lp ℂ ∞ productMeasure) : DiagonalSymbol :=
  ⟨fun x j => if ‖g (x,j)‖ ≤ ‖g‖ then g (x,j) else 0,
    (by
      refine ⟨?_,‖g‖,norm_nonneg _,?_⟩
      · intro j
        have hm : Measurable (fun x : Base => g (x,j)) :=
          (Lp.stronglyMeasurable g).measurable.comp (measurable_id.prodMk measurable_const)
        exact Measurable.ite (measurableSet_le hm.norm measurable_const) hm measurable_const
      · intro x j
        dsimp only
        split_ifs with h
        · exact h
        · simp)⟩
lemma productBoundedSymbol_ae (g : Lp ℂ ∞ productMeasure) :
    ∀ᵐ x ∂baseMeasure, ∀ j : ℤ, productBoundedSymbol g x j = g (x,j) := by
  have hh := Measure.ae_ae_of_ae_prod (linfty_ae_norm_le g)
  simp_rw [Measure.ae_count_iff] at hh
  filter_upwards [hh] with x hx j
  exact ite_eq_left (hx j)
lemma isProductMultiplier_mem_full {T : GlobalHilbert →L[ℂ] GlobalHilbert}
    (hT : IsProductMultiplier T) : T ∈ fullMultiplierAlgebra := by
  obtain ⟨g,hg⟩ := hT
  refine ⟨productBoundedSymbol g,?_⟩
  ext1 f
  apply Lp.ext
  filter_upwards [diagonalOperator_coord (productBoundedSymbol g) f,
    productBoundedSymbol_ae g,hg f] with x ha hsym hT
  ext j
  change diagonalOperator (productBoundedSymbol g) f x j = T f x j
  rw [ha,hsym,hT]
lemma fullMultiplier_mem_iff_productMultiplier (T : GlobalHilbert →L[ℂ] GlobalHilbert) :
    T ∈ fullMultiplierAlgebra ↔ IsProductMultiplier T := by
  constructor
  · rintro ⟨a,rfl⟩
    exact diagonalOperator_isProductMultiplier a
  · exact isProductMultiplier_mem_full



theorem polarAlgebra_mem_iff_productMultiplier (T : GlobalHilbert →L[ℂ] GlobalHilbert) :
    T ∈ polarAlgebra ↔ IsProductMultiplier T := by
  rw [polarAlgebra_eq_fullMultiplier]
  exact fullMultiplier_mem_iff_productMultiplier T




end
end BackwardIntertwiners

end OAI
