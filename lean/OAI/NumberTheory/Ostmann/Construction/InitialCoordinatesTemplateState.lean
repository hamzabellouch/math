import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightState
import OAI.NumberTheory.Ostmann.Construction.InitialCoordinatesTemplate

namespace OAI

noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
namespace Ostmann.Construction.InitialCoordinatesTemplate
open Arithmetic Characters.RationalHistory
open Arithmetic.HistorySymbolicState Arithmetic.HistorySymbolicStep

variable {b s k : ℕ} {a : State} {outside : List ℕ} {ι : Type*}

def expressionCoordinates
    (ha : Template.Matches (Template.initial (2*b) k) a.small)
    (hout : outside.length = 2*s) (e : StateExpr a ι) (x : ι → ℝ) : InitialCoordinates b s k :=
  coordinates ha hout (e.plus.realEval x) (e.minus.realEval x)
    (fun i => (e.small i).realEval x) (fun i => (outside.get i : ℝ))

theorem outside_real_product (outside : List ℕ) :
    (∏i : Fin outside.length,(outside.get i : ℝ)) = (outsideProduct outside : ℝ) := by
  simp only [outsideProduct]
  have he : List.ofFn (fun i : Fin outside.length => outside.get i) = outside := by simp
  have hp := congrArg (fun l : List ℕ => (l.prod : ℝ)) he
  simpa only [List.prod_ofFn, Nat.cast_prod] using hp

theorem expressionCoordinates_product
    (ha : Template.Matches (Template.initial (2*b) k) a.small)
    (hout : outside.length = 2*s) (e : StateExpr a ι) (x : ι → ℝ) :
    (expressionCoordinates ha hout e x).product = e.realPeriod outside x := by
  simp only [expressionCoordinates, coordinates_product, outside_real_product,
    StateExpr.realPeriod, product_realEval, List.map_ofFn, List.prod_ofFn, Function.comp_def]

theorem expressionCoordinates_bins
    (ha : Template.Matches (Template.initial (2*b) k) a.small)
    (hout : outside.length = 2*s) (e : StateExpr a ι) (x : ι → ℝ) (tb td : ℝ) :
    realLeafBins (expressionCoordinates ha hout e x) tb td =
      realStateBins b s tb td a outside (fun i => (e.small i).realEval x)
        (fun i => (outside.get i : ℝ)) :=
  coordinates_bins ha hout _ _ tb td _ _

theorem expressionCoordinates_scalar
    (ha : Template.Matches (Template.initial (2*b) k) a.small)
    (hout : outside.length = 2*s) (e : StateExpr a ι) (x : ι → ℝ) (X tb td : ℝ) :
    realLeafScalar (expressionCoordinates ha hout e x) X a.frequency tb td =
      e.realScalar b s X tb td outside x := by
  simp only [realLeafScalar, StateExpr.realScalar,
    expressionCoordinates_product, expressionCoordinates_bins]

theorem coordinates_sourceStateBins
    (ha : Template.Matches (Template.initial (2*b) k) a.small)
    (hout : outside.length = 2*s) (plus minus tb td : ℝ) :
    realLeafBins (coordinates ha hout plus minus
      (fun i => ((a.small.get i).value : ℝ)) (fun i => (outside.get i : ℝ))) tb td =
      sourceStateBins b s tb td outside a :=
  coordinates_bins ha hout plus minus tb td _ _

theorem expressionCoordinates_positive
    (ha : Template.Matches (Template.initial (2*b) k) a.small)
    (hout : outside.length = 2*s) (e : StateExpr a ι) (x : ι → ℝ)
    (hp : 0 < e.plus.realEval x) (hm : 0 < e.minus.realEval x)
    (hy : ∀i,0 < (e.small i).realEval x) (hz : ∀n∈outside,0 < n) :
    (expressionCoordinates ha hout e x).Positive := by
  apply coordinates_positive ha hout _ _ _ _ hp hm hy
  intro i
  exact_mod_cast hz (outside.get i) (List.get_mem outside i)

theorem expressionCoordinates_log_support
    (ha : Template.Matches (Template.initial (2*b) k) a.small)
    (hout : outside.length = 2*s) (e : StateExpr a ι) (x : ι → ℝ)
    (hpos : (expressionCoordinates ha hout e x).Positive)
    (G tb td : ℝ) (topCenter : Bool → Fin 3 → ℝ)
    (compCenter : Bool → Fin k → Fin 2 → ℝ)
    (hg : ∀h, |Real.log ((expressionCoordinates ha hout e x).giant h) - G| ≤ 1)
    (ht : ∀h i, |Real.log ((expressionCoordinates ha hout e x).top h i) - topCenter h i| ≤ 1)
    (hc : ∀h j i, |Real.log ((expressionCoordinates ha hout e x).compensation h j i) -
      compCenter h j i| ≤ 1)
    (hb : realStateBins b s tb td a outside (fun i => (e.small i).realEval x)
      (fun i => (outside.get i : ℝ)) ≠ 0) :
    |Real.log (e.realPeriod outside x) - (2*G+2*tb+2*td+
      (∑h,∑i,topCenter h i)+(∑h,∑j,∑i,compCenter h j i))| ≤ 12+4*k := by
  have hbins := realStateBins_support b s tb td a outside
    (fun i => (e.small i).realEval x) (fun i => (outside.get i : ℝ)) hb
  have hbulk : ∀h, |(∑i,Real.log ((expressionCoordinates ha hout e x).bulk h i))-tb| ≤ 1 := by
    intro h
    simpa only [bulk_log_sum ha, expressionCoordinates, coordinates] using (hbins h).1
  have hspec : ∀h, |(∑i,Real.log ((expressionCoordinates ha hout e x).spectator h i))-td| ≤ 1 := by
    intro h
    simpa only [spectator_log_sum hout, expressionCoordinates, coordinates] using (hbins h).2
  have he := initial_log_product_support (expressionCoordinates ha hout e x)
    hpos G tb td topCenter compCenter hg hbulk hspec ht hc
  simpa only [expressionCoordinates_product] using he

end Ostmann.Construction.InitialCoordinatesTemplate

end

end OAI
