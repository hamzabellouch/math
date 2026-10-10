import Mathlib
import OAI.Probability.LatticeSurface.Convexity.CubePrekopa
import OAI.Probability.LatticeSurface.Convexity.QuantileTransport
import OAI.Probability.LatticeSurface.Convexity.WeightedPrekopa
import OAI.Probability.LatticeSurface.Dynamics.DisplacementInequality

namespace OAI

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

namespace FacetVolume

def distanceApprox {n : ℕ} (K : Set (Fin n → ℝ)) (k : ℕ) (x : Fin n → ℝ) : ℝ :=
  Real.exp (-(k : ℝ) * Metric.infDist x K)

lemma continuous_distanceApprox {n : ℕ} (K : Set (Fin n → ℝ)) (k : ℕ) :
    Continuous (distanceApprox K k) := by
  exact Real.continuous_exp.comp (continuous_const.mul (Metric.continuous_infDist_pt K))

lemma distanceApprox_pos {n : ℕ} (K : Set (Fin n → ℝ)) (k : ℕ) (x : Fin n → ℝ) :
    0 < distanceApprox K k x := Real.exp_pos _

lemma distanceApprox_le_one {n : ℕ} (K : Set (Fin n → ℝ)) (k : ℕ) (x : Fin n → ℝ) :
    distanceApprox K k x ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) Metric.infDist_nonneg

lemma tendsto_distanceApprox {n : ℕ} {K : Set (Fin n → ℝ)} (hK : IsClosed K)
    (hne : K.Nonempty) (x : Fin n → ℝ) :
    Tendsto (fun k => distanceApprox K k x) atTop (𝓝 (K.indicator (fun _ => (1 : ℝ)) x)) := by
  by_cases hx : x ∈ K
  · simp only [distanceApprox, Metric.infDist_zero_of_mem hx, mul_zero, Real.exp_zero,
      indicator_of_mem hx]
    exact tendsto_const_nhds
  · rw [indicator_of_notMem hx]
    have hd : 0 < Metric.infDist x K := (hK.notMem_iff_infDist_pos hne).mp hx
    convert Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop).atTop_mul_const hd) using 1
    simp only [distanceApprox, Function.comp_def, neg_mul]

lemma tendsto_cubeIntegral_distanceApprox {n : ℕ} {K : Set (Fin n → ℝ)}
    {a b : ℝ} (hK : IsCompact K) (hne : K.Nonempty) (hsub : K ⊆ cube n a b) :
    Tendsto (fun k => cubeIntegral (distanceApprox K k) a b) atTop
      (𝓝 ((volume K).toReal)) := by
  have hbound : IntegrableOn (fun _ : Fin n → ℝ => (1 : ℝ)) (cube n a b) :=
    continuous_const.continuousOn.integrableOn_compact (compact_cube _ _ _)
  have hlim := tendsto_integral_of_dominated_convergence (μ := volume.restrict (cube n a b))
    (fun _ => (1 : ℝ))
    (fun k => (continuous_distanceApprox K k).aestronglyMeasurable) hbound
    (fun k => Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, abs_of_pos (distanceApprox_pos K k x)] using
        distanceApprox_le_one K k x)
    (Filter.Eventually.of_forall fun x => tendsto_distanceApprox hK.isClosed hne x)
  have hint : (∫ x in cube n a b, K.indicator (fun _ => (1 : ℝ)) x) = (volume K).toReal := by
    rw [integral_indicator hK.measurableSet, Measure.restrict_restrict hK.measurableSet,
      inter_eq_left.mpr hsub, integral_const]
    simp [Measure.real]
  simpa only [cubeIntegral, hint] using hlim

lemma infDist_weighted_combination {n : ℕ} {K L M : Set (Fin n → ℝ)} {s t : ℝ}
    (hK : IsCompact K) (hL : IsCompact L) (hKn : K.Nonempty) (hLn : L.Nonempty)
    (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hcomb : ∀ x ∈ K, ∀ y ∈ L, s • x+t • y ∈ M) (x y : Fin n → ℝ) :
    Metric.infDist (s • x+t • y) M ≤ s*Metric.infDist x K+t*Metric.infDist y L := by
  rcases hK.exists_infDist_eq_dist hKn x with ⟨u, hu, hxu⟩
  rcases hL.exists_infDist_eq_dist hLn y with ⟨v, hv, hyv⟩
  calc
    Metric.infDist (s • x+t • y) M ≤ dist (s • x+t • y) (s • u+t • v) :=
      Metric.infDist_le_dist_of_mem (hcomb u hu v hv)
    _ = ‖s • (x-u)+t • (y-v)‖ := by rw [dist_eq_norm]; congr 1; module
    _ ≤ ‖s • (x-u)‖+‖t • (y-v)‖ := norm_add_le _ _
    _ = s*Metric.infDist x K+t*Metric.infDist y L := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg hs, Real.norm_of_nonneg ht,
        hxu, hyv, dist_eq_norm, dist_eq_norm]

lemma distanceApprox_combination {n : ℕ} {K L M : Set (Fin n → ℝ)} {s t : ℝ}
    (hK : IsCompact K) (hL : IsCompact L) (hKn : K.Nonempty) (hLn : L.Nonempty)
    (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hcomb : ∀ x ∈ K, ∀ y ∈ L, s • x+t • y ∈ M) (k : ℕ) (x y : Fin n → ℝ) :
    (distanceApprox K k x)^s*(distanceApprox L k y)^t ≤ distanceApprox M k (s • x+t • y) := by
  simp only [distanceApprox, ← Real.exp_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hd := infDist_weighted_combination hK hL hKn hLn hs ht hcomb x y
  nlinarith [Nat.cast_nonneg (α := ℝ) k]

theorem compact_volume_bm_in_cube {n : ℕ} {K L M : Set (Fin n → ℝ)} {a b s t : ℝ}
    (hK : IsCompact K) (hL : IsCompact L) (hM : IsCompact M)
    (hKn : K.Nonempty) (hLn : L.Nonempty) (hMn : M.Nonempty)
    (hKs : K ⊆ cube n a b) (hLs : L ⊆ cube n a b) (hMs : M ⊆ cube n a b)
    (hab : a < b) (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s+t=1)
    (hcomb : ∀ x ∈ K, ∀ y ∈ L, s • x+t • y ∈ M) :
    ((volume K).toReal)^s*((volume L).toReal)^t ≤ (volume M).toReal := by
  have hPL (k : ℕ) := cube_prekopa_leindler n
    (continuous_distanceApprox K k) (continuous_distanceApprox L k) (continuous_distanceApprox M k)
    hab hs ht hst (fun x _ => distanceApprox_pos K k x) (fun x _ => distanceApprox_pos L k x)
    (fun x _ => (distanceApprox_pos M k x).le)
    (fun x _ y _ => distanceApprox_combination hK hL hKn hLn hs ht hcomb k x y)
  exact le_of_tendsto_of_tendsto
    (((tendsto_cubeIntegral_distanceApprox hK hKn hKs).rpow_const (.inr hs)).mul
      ((tendsto_cubeIntegral_distanceApprox hL hLn hLs).rpow_const (.inr ht)))
    (tendsto_cubeIntegral_distanceApprox hM hMn hMs) (Eventually.of_forall hPL)

theorem compact_volume_brunn_minkowski {n : ℕ} {K L M : Set (Fin n → ℝ)} {s t : ℝ}
    (hK : IsCompact K) (hL : IsCompact L) (hM : IsCompact M)
    (hKn : K.Nonempty) (hLn : L.Nonempty) (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s+t=1)
    (hcomb : ∀ x ∈ K, ∀ y ∈ L, s • x+t • y ∈ M) :
    ((volume K).toReal)^s*((volume L).toReal)^t ≤ (volume M).toReal := by
  obtain ⟨R, hR, hbd⟩ := ((hK.union hL).union hM).isBounded.exists_pos_norm_le
  have hsub : K ∪ L ∪ M ⊆ cube n (-R) R := by
    intro x hx
    apply mem_cube.mpr
    intro i
    have hi : |x i| ≤ R := (norm_le_pi_norm x i).trans (hbd x hx)
    exact abs_le.mp hi
  have hMn : M.Nonempty := by
    obtain ⟨x,hx⟩ := hKn
    obtain ⟨y,hy⟩ := hLn
    exact ⟨_,hcomb x hx y hy⟩
  exact compact_volume_bm_in_cube hK hL hM hKn hLn hMn
    (fun x hx => hsub (Or.inl (Or.inl hx)))
    (fun x hx => hsub (Or.inl (Or.inr hx)))
    (fun x hx => hsub (Or.inr hx)) (by linarith) hs ht hst hcomb

end FacetVolume

end

end OAI
