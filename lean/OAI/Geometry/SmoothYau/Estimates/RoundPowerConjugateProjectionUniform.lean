import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.CompactMetricInverseJets

namespace OAI

noncomputable section
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
variable {d : ℕ}
local instance : Fact (Module.finrank ℝ (Euclidean (d+1)) = d+1) := ⟨by simp [Euclidean]⟩
theorem roundPower_conjugate_projection_uniform
    (g : SmoothMetric (Euclidean d) (Sphere d)) (a b : Euclidean (d+1)) (p : Sphere d)
    (ha : inner ℝ a a=1) (hb : inner ℝ b b=1) (hab : inner ℝ a b=0)
    {K : Set (Euclidean d)} (hK : IsCompact K) (hKO : K ⊆ (chartAt (Euclidean d) p).target)
    (hg : ∀ y ∈ K, ∀ v z : TangentSpace 𝓘(ℝ,Euclidean d) ((chartAt (Euclidean d) p).symm y),
      g.inner _ v z = (inner ℝ : Euclidean (d+1) → Euclidean (d+1) → ℝ)
        (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1))
          (fun q : Sphere d => (q : Euclidean (d+1))) _ v)
        (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1))
          (fun q : Sphere d => (q : Euclidean (d+1))) _ z))
    (h : ℕ) {r t D : ℝ} (hr : 0 < r) (ht : t < 1) (hD : 0 ≤ D)
    (hKr : ∀ y ∈ K, r ≤ ‖roundPlanarChart a b p y‖)
    (hKt : ∀ y ∈ K, Complex.normSq (roundPlanarChart a b p y) ≤ t)
    : ∃ C : ℝ, 0 < C ∧ ∀ (w : Sphere d → ℝ),
      ContMDiff 𝓘(ℝ,Euclidean d) 𝓘(ℝ,ℝ) ∞ w →
      (∀ x, w x ≠ 0) →
      (∀ y ∈ K, 1/2 ≤ w ((chartAt (Euclidean d) p).symm y)) →
      (∀ y ∈ K, w ((chartAt (Euclidean d) p).symm y) ≤ 2) →
      (∀ j : ℕ, 1 ≤ j → j ≤ h+1 → ∀ y ∈ K,
        ‖iteratedFDeriv ℝ j (w ∘ (chartAt (Euclidean d) p).symm) y‖ ≤ D) →
      (∀ y ∈ K, coordinateGradientPair g w w ((chartAt (Euclidean d) p).symm y) ≤ (1-t)/16) →
    ∀ n : ℕ, 1 ≤ n → ∀ y ∈ K, ∀ i j : CoordIndex (Euclidean d),
      ‖iteratedFDeriv ℝ h (chartGradientProjection g
        (fun x => roundPower a b n x/w x) p i j) y‖ ≤ C*(n:ℝ)^h := by
  obtain ⟨C0,hC0,hCj⟩ := roundPower_annular_chart_jets a b p hK hKO (h+1) hr hKr
  obtain ⟨A,hA,hAj⟩ := compact_metric_inverse_jets g p hK hKO h
  let C1 := C0*((h+1).factorial:ℝ)^2/(1/2)*(1+max 1 (D/(1/2)))^(h+1)
  have hC1 : 0 ≤ C1 := by dsimp [C1]; positivity
  let L := ∑ j, ‖Module.finBasis ℝ (Euclidean d) j‖
  have hL : 0 ≤ L := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have he (i : CoordIndex (Euclidean d)) : ‖Module.finBasis ℝ (Euclidean d) i‖ ≤ L :=
    Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  let δ := (1-t)/16
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let J := 2^h*A*C1*L
  let C := J*(C1*L)*(h.factorial:ℝ)^2/δ*
    (2+2*max 1 ((Fintype.card (CoordIndex (Euclidean d)):ℝ)*J*(C1*L)/δ))^h
  refine ⟨max C 1,zero_lt_one.trans_le (le_max_right _ _),?_⟩
  intro w hw hw0 hwl hwu hwj hwG n hn y hy i j
  have hnR : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  let W := ‖roundPlanarChart a b p y‖^n
  have hrY : 0 < ‖roundPlanarChart a b p y‖ := hr.trans_le (hKr y hy)
  have hW : 0 < W := pow_pos hrY _
  let u := fun x => roundPower a b n x/w x
  have hu : ContMDiff 𝓘(ℝ,Euclidean d) 𝓘(ℝ,ℝ) ∞ u :=
    (roundPower_smooth a b n).div₀ (hw) (hw0)
  have huw : ContDiffOn ℝ ∞ (w ∘ (chartAt (Euclidean d) p).symm)
      (chartAt (Euclidean d) p).target := fun z hz => (contDiffAt_inChart (hw) p hz).contDiffWithinAt
  have hu0 : ContDiffOn ℝ ∞ (roundPower a b n ∘ (chartAt (Euclidean d) p).symm)
      (chartAt (Euclidean d) p).target :=
    fun z hz => (contDiffAt_inChart (roundPower_smooth a b n) p hz).contDiffWithinAt
  have huj : ∀ k ≤ h+1, ‖iteratedFDeriv ℝ k (u ∘ (chartAt (Euclidean d) p).symm) y‖ ≤
      C1*(n:ℝ)^k*W := by
    exact sharp_conjugate_jet_bound_on (chartAt (Euclidean d) p).open_target (hKO hy)
      hu0 huw (h+1) (by norm_num : (0:ℝ)<1/2) hW hnR hC0.le hD (hwl y hy)
      (fun k hk => hCj n y hy k hk) (fun k hk hkh => hwj k hk hkh y hy)
  have hR : 0 < Complex.normSq (roundPlanarChart a b p y) := by
    rw [Complex.normSq_eq_norm_sq]; positivity
  have hgL := roundPower_conjugate_gradient_lower g ((chartAt (Euclidean d) p).symm y)
    (hg y hy) a b n hn ha hb hab hR (hKt y hy) ht (w) (hw) (hw0)
    (hwl y hy) (hwu y hy) (hwG y hy)
  have heW : Complex.normSq (roundPlanarChart a b p y)^n=W^2 := by
    dsimp [W]
    rw [Complex.normSq_eq_norm_sq,←pow_mul,←pow_mul,Nat.mul_comm 2 n]
  have hgrad : δ*((n:ℝ)*W)^2 ≤ coordinateGradientPair g u u ((chartAt (Euclidean d) p).symm y) := by
    change δ*(n:ℝ)^2*Complex.normSq (roundPlanarChart a b p y)^n ≤ _ at hgL
    rw [heW] at hgL
    simpa only [mul_pow,mul_assoc] using hgL
  have hp := chartGradientProjection_jet_bound hu g p (hKO hy) h hδ hnR hW hC1
    (zero_le_one.trans hA) hL he (fun i j k hk => hAj i j k hk y hy) huj hgrad i j
  exact hp.trans (mul_le_mul_of_nonneg_right (le_max_left C 1) (pow_nonneg (Nat.cast_nonneg _) _))
end YauCounterexamples
end

end OAI
