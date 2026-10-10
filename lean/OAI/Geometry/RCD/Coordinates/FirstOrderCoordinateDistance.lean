import OAI.Geometry.RCD.Harmonic.NearbyGramColumn
import OAI.Geometry.RCD.Harmonic.NearColumnDistance
import OAI.Geometry.RCD.Coordinates.SplittingCoordinateLipschitz

namespace OAI

/-! # The original coordinates do not increase distance in the limit -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal InnerProductSpace
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.first_order_coordinate_distance {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n) (hK : K≤0)
    (p x y : ℕ → X) (r ε : ℕ → ℝ) (hr : ∀ k, 0<r k) (hr0 : Tendsto r atTop (𝓝 0))
    (hcurv : ∀ k, -1≤K*(16*r k)^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hε0 : Tendsto ε atTop (𝓝 0))
    (u : ℕ → Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (v : ℕ → X → Euclidean n)
    (hsplit : ∀ k, FirstOrderSplittingOn (hausdorff n X) hX.quadratic
      (p k) (16*r k) (ε k) (u k) (v k))
    (hx : ∀ k, dist (x k) (p k)≤r k/48) (hy : ∀ k, dist (y k) (p k)≤r k/48) :
    Tendsto (fun k => max 0 (dist (v k (x k)) (v k (y k))/r k-
      dist (x k) (y k)/r k)) atTop (𝓝 0) := by
  obtain ⟨δ,e,γ,hδ,hδ0,he,he0,hnear,hcol⟩ := hX.nearby_gram_column hn hK p x y r ε
    hr hr0 hcurv hε hε1 hε0 u v hsplit hx hy (fun k => v k (y k)-v k (x k))
  let E k := |Real.sqrt (1+e k)-1|+(δ k/12)*Real.sqrt (1+e k)+(2*(n:ℝ))*(δ k/12)
  have hE (k : ℕ) : 0≤E k := by
    have hd := (hδ k).1.le
    dsimp [E]
    positivity
  have hE0 : Tendsto E atTop (𝓝 0) := by
    have hs := (he0.const_add 1).sqrt
    have hδ' := hδ0.div_const 12
    simpa only [E,add_zero,Real.sqrt_one,sub_self,abs_zero,zero_div,zero_mul,mul_zero]
      using (((hs.sub_const 1).abs.add (hδ'.mul hs)).add (hδ'.const_mul (2*(n:ℝ))))
  apply squeeze_zero (fun k => le_max_left _ _) (g := E)
  · intro k
    apply max_le (hE k)
    have hs : FirstOrderSplittingOn (hausdorff n X) hX.quadratic
        (p k) (8*(2*r k)) (ε k) (u k) (v k) := by
      simpa only [show (8:ℝ)*(2*r k)=16*r k by ring] using hsplit k
    have hLip := hX.splitting_coordinate_lipschitz hn (mul_pos (by norm_num) (hr k)) (hε k) hs
    have hC : (n:ℝ)*(1+ε k)≤2*(n:ℝ) := by nlinarith [Nat.cast_nonneg (α:=ℝ) n,hε1 k]
    have hγ0 : γ k 0∈ball (p k) (2*r k) := by
      change dist (γ k 0) (p k)<2*r k
      linarith [(hnear k).2.2 0,hr k]
    have hγ1 : γ k 1∈ball (p k) (2*r k) := by
      change dist (γ k 1) (p k)<2*r k
      linarith [(hnear k).2.2 1,hr k]
    have hx' : x k∈ball (p k) (2*r k) := by
      change dist (x k) (p k)<2*r k
      linarith [hx k,hr k]
    have hy' : y k∈ball (p k) (2*r k) := by
      change dist (y k) (p k)<2*r k
      linarith [hy k,hr k]
    have hdx := (hLip.dist_le_mul _ hγ0 _ hx').trans
      (mul_le_mul_of_nonneg_right hC dist_nonneg)
    have hdy := (hLip.dist_le_mul _ hγ1 _ hy').trans
      (mul_le_mul_of_nonneg_right hC dist_nonneg)
    have hclose : dist (γ k 0) (x k)+dist (γ k 1) (y k)≤(δ k/12)*r k := by
      linarith [(hnear k).1,(hnear k).2.1]
    have hb := near_column_distance (v k) (x k) (y k) (γ k 0) (γ k 1)
      (by positivity : 0≤2*(n:ℝ)) (hr k) (he k) hclose hdx hdy (hcol k)
    have hB : dist (x k) (y k)/r k≤1 := by
      apply (div_le_one (hr k)).mpr
      have ht := dist_triangle (x k) (p k) (y k)
      rw [dist_comm (p k) (y k)] at ht
      linarith [hx k,hy k,hr k]
    have hB0 : 0≤dist (x k) (y k)/r k := div_nonneg dist_nonneg (hr k).le
    have ha := mul_le_mul_of_nonneg_right
      (le_abs_self (Real.sqrt (1+e k)-1)) hB0
    have hb' := mul_le_mul_of_nonneg_left hB (abs_nonneg (Real.sqrt (1+e k)-1))
    dsimp [E]
    nlinarith
  · exact hE0

end RegularPointCoordinates

end

end OAI
