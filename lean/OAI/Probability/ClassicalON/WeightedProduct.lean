import OAI.Probability.ClassicalON.ProductGrouping

namespace OAI

universe uA uK uV

noncomputable section
open MeasureTheory Set
open scoped BigOperators Classical
namespace ClassicalON
variable {V : Type uV} {K : Type uK} [Fintype V] [Fintype K]
variable (A : V → Type uA) [∀ v,MeasurableSpace (A v)] (label : V → K)

theorem weightedMean_grouped_product (μ : (v : V) → Measure (A v)) [∀ v,SigmaFinite (μ v)]
    (w f : (k : K) → ((v : {v // label v=k}) → A v.val) → ℝ) :
    weightedMean (Measure.pi μ) (fun s => ∏ k,w k (fun v => s v.val))
      (fun s => ∏ k,f k (fun v => s v.val))=
      ∏ k,weightedMean (Measure.pi (fun v : {v // label v=k} => μ v.val)) (w k) (f k) := by
  unfold weightedMean
  simp_rw [← Finset.prod_mul_distrib]
  rw [integral_grouped_product A label μ (fun k s => w k s*f k s),
    integral_grouped_product A label μ w,Finset.prod_div_distrib]

end ClassicalON

end

end OAI
