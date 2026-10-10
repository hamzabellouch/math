import OAI.NumberTheory.Ostmann.QuadraticCenter.WitnessProbabilityBounds
import OAI.NumberTheory.Ostmann.QuadraticCenter.WitnessStatistics

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem quadraticWitnessProducts_probability_of_array_bounds {F P : Finset ℕ}
    [NeZero (∏p:F,p.val)] {Z k l : ℕ} (hZ : 1≤Z) (hFZ : (∏p∈F,p)≤Z)
    (hP : ∀p∈P,p.Prime) (hk : k≤P.card) (hl : 0<l)
    (A : ∀p:ℕ,Finset (ZMod p)) (X K C : ℝ) (t : ℕ→ℤ)
    (hmargin : 1+Real.exp ((7/1000:ℝ)*K)+1+1≤Real.exp ((3/200:ℝ)*K))
    (hfull : Real.exp ((3/200:ℝ)*K) ≤
      primeProductMean P k (fun q => ‖primeProductArraySum F A (1/16) X t (Z^14) q‖))
    (hlarge : primeProductMean P k (fun q =>
      ‖primeProductLargeSum (∏p:F,p.val) Z A (1/16) X t q‖)≤Real.exp ((7/1000:ℝ)*K))
    (hrest : primeProductMean P k (fun q =>
      ‖primeProductNontrivialSum (∏p:F,p.val) Z A (1/16) X t q‖)≤1)
    (hoff : primeProductMean P k
      (primeProductSmallOffEventNorm (∏p:F,p.val) A (1/16) X K t)≤1)
    (hmoment : primeProductMean P k (fun q =>
      ‖primeProductSmallSum (∏p:F,p.val) A (1/16) X t q‖^(2*l))≤
        (Real.exp (C*K))^(2*l)) :
    Real.exp (-(2*C)*K) ≤
      (quadraticWitnessProducts P k (∏p:F,p.val) A X K t).card / (Nat.choose P.card k:ℝ) := by
  classical
  let L := ∏p:F,p.val
  let E := primeProductWitness L A X K t
  let small := fun q => ‖primeProductSmallSum L A (1/16) X t q‖
  have hsplit : ∀q∈primeProductSamples P k,
      ‖primeProductArraySum F A (1/16) X t (Z^14) q‖ ≤ small q+
        ‖primeProductLargeSum L Z A (1/16) X t q‖+
        ‖primeProductNontrivialSum L Z A (1/16) X t q‖ := by
    intro q hq
    exact primeProductArraySum_norm_le_split hZ hFZ
      (primeProductSamples_primeFactors hP hq).1.ne_zero A (1/16) X t
  have hoff' : primeProductMean P k (fun q => if E q then 0 else small q)≤1 := hoff
  have hmean := primeProduct_event_mean_lower P k E
    (fun q => ‖primeProductArraySum F A (1/16) X t (Z^14) q‖) small
    (fun q => ‖primeProductLargeSum L Z A (1/16) X t q‖)
    (fun q => ‖primeProductNontrivialSum L Z A (1/16) X t q‖)
    hsplit hfull hlarge hrest hoff' hmargin
  rw [quadraticWitnessProducts_probability]
  exact primeProductProbability_exp_lower hP hk hl E small C K hmean hmoment

end Ostmann.QuadraticCenter

end

end OAI
