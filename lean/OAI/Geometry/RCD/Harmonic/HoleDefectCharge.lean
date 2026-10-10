import OAI.Geometry.RCD.Metric.NearbySmallBallMass
import OAI.Geometry.RCD.Sobolev.FiniteDisjointIntegral

namespace OAI

/-! # Charging a finite disjoint hole family to the actual RCD defect

Only relative Bishop--Gromov volume is used. The source balls and their
large defect averages are explicit, so no coordinate-surjectivity result
is hidden in this estimate.
-/

open Set Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.hole_defect_charge {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) {ι : Type*} [Fintype ι]
    {p : X} {R t : ℝ} (hR : 0 < R) (ht : 0 < t) (hcurv : -1 ≤ K*(2*R)^2)
    {Ω : Set X} {f : X → ℝ} (hf : IntegrableOn f Ω (hausdorff n X))
    (hf0 : ∀ᵐ x ∂(hausdorff n X).restrict Ω, 0 ≤ f x)
    {z : ι → X} {r s : ι → ℝ} (hz : ∀ i, dist (z i) p ≤ R)
    (hr : ∀ i, 0 < r i) (hrs : ∀ i, r i ≤ s i) (hsR : ∀ i, s i ≤ R)
    (hsub : ∀ i, ball (z i) (s i) ⊆ Ω)
    (hdisj : Pairwise (fun i j => Disjoint (ball (z i) (s i)) (ball (z j) (s j))))
    (havg : ∀ i, t*(hausdorff n X).real (ball (z i) (s i)) ≤
      ∫ x in ball (z i) (s i), f x ∂hausdorff n X) :
    (∑ i, (r i)^n) ≤
      ((Real.cosh 1^(n-1)*2^n)*R^n/(t*(hausdorff n X).real (ball p R)))*
        ∫ x in Ω, f x ∂hausdorff n X := by
  let μ := hausdorff n X
  let A := (Real.cosh 1^(n-1)*2^n)*R^n
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hm : 0 < μ.real (ball p R) := ENNReal.toReal_pos
    (hX.fullSupport p R hR).ne' (hX.finiteOnBounded _ isBounded_ball).ne
  have hi (i : ι) : (t*μ.real (ball p R))*(r i)^n ≤
      A*(∫ x in ball (z i) (s i), f x ∂μ) := by
    have hv : μ.real (ball p R)*(r i)^n ≤ A*μ.real (ball (z i) (s i)) := by
      apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hr i).le (hrs i) n)
        (measureReal_nonneg)).trans
      exact hX.nearby_small_ball_mass hn hR (hz i) ((hr i).trans_le (hrs i)) (hsR i) hcurv
    calc
      _ = t*(μ.real (ball p R)*(r i)^n) := by ring
      _ ≤ t*(A*μ.real (ball (z i) (s i))) := mul_le_mul_of_nonneg_left hv ht.le
      _ = A*(t*μ.real (ball (z i) (s i))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (havg i) hA
  have hsums : (∑ i, ∫ x in ball (z i) (s i), f x ∂μ) ≤ ∫ x in Ω, f x ∂μ :=
    finite_disjoint_setIntegral_le μ hf hf0 (fun _ => measurableSet_ball) hsub hdisj
  have htot : (∑ i, (r i)^n)*(t*μ.real (ball p R)) ≤ A*∫ x in Ω, f x ∂μ := by
    calc
      _ = ∑ i, (t*μ.real (ball p R))*(r i)^n := by rw [mul_comm,Finset.mul_sum]
      _ ≤ ∑ i, A*(∫ x in ball (z i) (s i), f x ∂μ) := Finset.sum_le_sum (fun i _ => hi i)
      _ = A*(∑ i, ∫ x in ball (z i) (s i), f x ∂μ) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hsums hA
  calc
    _ ≤ (A*∫ x in Ω, f x ∂μ)/(t*μ.real (ball p R)) :=
      (le_div_iff₀ (mul_pos ht hm)).mpr htot
    _ = _ := by dsimp only [A]; ring

end RegularPointCoordinates

end

end OAI
