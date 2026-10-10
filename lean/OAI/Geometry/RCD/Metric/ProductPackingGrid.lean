import OAI.Geometry.RCD.Metric.EuclideanPackingGrid
import Mathlib.Analysis.Normed.Lp.ProdLp

namespace OAI

/-! # A finite packing obtained from an extra metric direction -/

open Set Metric
noncomputable section
namespace RegularPointCoordinates

theorem metric_product_distance_L2 {A Z : Type*} [MetricSpace A] [MetricSpace Z]
    (x y : WithLp 2 (A × Z)) :
    dist x y=Real.sqrt (dist x.fst y.fst^2+dist x.snd y.snd^2) := by
  have h := WithLp.prod_dist_eq_add (p := 2) (by norm_num) x y
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,Real.sqrt_eq_rpow] using h

def productPackingGrid {Z : Type*} {n m : ℕ} (b : ℝ) (z : Fin m → Z)
    (i : Fin m × (Fin n → Fin m)) : WithLp 2 (Euclidean n × Z) :=
  WithLp.toLp 2 (euclideanPackingGrid b i.2,z i.1)

theorem productPackingGrid_separated {Z : Type*} [MetricSpace Z] {n m : ℕ}
    {b : ℝ} (hb : 0 ≤ b) {z : Fin m → Z}
    (hz : Pairwise (fun i j => b ≤ dist (z i) (z j))) :
    Pairwise (fun i j : Fin m × (Fin n → Fin m) =>
      b ≤ dist (productPackingGrid b z i) (productPackingGrid b z j)) := by
  intro i j hij
  by_cases hfirst : i.1=j.1
  · have hsecond : i.2 ≠ j.2 := fun h => hij (Prod.ext hfirst h)
    exact (euclideanPackingGrid_separated hb hsecond).trans
      (WithLp.dist_fst_le (productPackingGrid b z i) (productPackingGrid b z j))
  · exact (hz hfirst).trans
      (WithLp.dist_snd_le (productPackingGrid b z i) (productPackingGrid b z j))

theorem productPackingGrid_bounded {Z : Type*} [MetricSpace Z] {n m : ℕ}
    (hn : 0 < n) {b D : ℝ} (hb : 0 ≤ b) {z : Fin m → Z} {z₀ : Z}
    (hz : ∀ i, dist (z i) z₀ ≤ D) (i : Fin m × (Fin n → Fin m)) :
    dist (productPackingGrid b z i) (WithLp.toLp 2 (0,z₀)) ≤ (n:ℝ)*m*b+D := by
  let mid : WithLp 2 (Euclidean n × Z) := WithLp.toLp 2 (0,z i.1)
  have hh : dist (productPackingGrid b z i) mid=‖euclideanPackingGrid b i.2‖ := by
    rw [metric_product_distance_L2]
    simp only [productPackingGrid,mid,WithLp.fst,WithLp.snd,dist_self,dist_zero_right,
      zero_pow (by norm_num : (2:ℕ)≠0),add_zero,Real.sqrt_sq (norm_nonneg _)]
  have hv : dist mid (WithLp.toLp 2 (0,z₀))=dist (z i.1) z₀ := by
    rw [metric_product_distance_L2]
    simp only [mid,WithLp.fst,WithLp.snd,dist_self,zero_pow (by norm_num : (2:ℕ)≠0),
      zero_add,Real.sqrt_sq dist_nonneg]
  calc
    _ ≤ dist (productPackingGrid b z i) mid+dist mid (WithLp.toLp 2 (0,z₀)) := dist_triangle _ _ _
    _ ≤ _ := by rw [hh,hv]; exact add_le_add (euclideanPackingGrid_norm_le hn hb _) (hz i.1)

theorem NoncollapsedRCD.product_grid_obstruction {X Z : Type*}
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X] [MetricSpace Z]
    {K : ℝ} {n m : ℕ} (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    {p : X} {z₀ : Z} {ρ b D ε : ℝ} (hρ : 0 < ρ) (hb : 0 < b) (hb2 : b ≤ 2)
    (he : ε ≤ b/6) (hcurv : -1 ≤ K*(4*ρ)^2) (z : Fin m → Z)
    (hz : Pairwise (fun i j => b ≤ dist (z i) (z j)))
    (hzD : ∀ i, dist (z i) z₀ ≤ D) (hroom : (n:ℝ)*m*b+D ≤ 1-ε)
    {f : X → WithLp 2 (Euclidean n × Z)}
    (hf : IsPointedApproximation p (WithLp.toLp 2 (0,z₀)) ρ 1 ε f) :
    ((m:ℝ)^(n+1))*(b/2)^n ≤ Real.cosh 1^(n-1)*8^n := by
  have h := hX.approximate_target_packing hn hρ hb hb2 he hcurv hf (productPackingGrid b z)
    (fun i => (productPackingGrid_bounded (by omega) hb.le hzD i).trans hroom)
    (productPackingGrid_separated hb.le hz)
  simpa only [Fintype.card_prod,Fintype.card_pi,Fintype.card_fin,Finset.prod_const,
    Finset.card_univ,Nat.cast_mul,Nat.cast_pow,pow_succ,mul_comm] using h

end RegularPointCoordinates

end

end OAI
