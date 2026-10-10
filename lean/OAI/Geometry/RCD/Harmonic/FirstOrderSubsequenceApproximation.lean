import OAI.Geometry.RCD.Harmonic.FirstOrderEuclideanLimit
import OAI.Geometry.RCD.Metric.LocalIsometryDensityTransfer

namespace OAI

/-! # Actual pointed Euclidean approximations along first-order sequences -/

open Set Filter Metric MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
universe u
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.first_order_subsequence_approximation {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n) (hK : K≤0)
    (p : ℕ → X) (r ε : ℕ → ℝ)
    (hr : ∀ k, 0<r k) (hr0 : Tendsto r atTop (𝓝 0))
    (hcurv : ∀ k, -1≤K*(80*r k)^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hε0 : Tendsto ε atTop (𝓝 0))
    (U : ℕ → Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (v : ℕ → X → Euclidean n)
    (hsplit : ∀ k, FirstOrderSplittingOn (hausdorff n X) hX.quadratic
      (p k) (80*r k) (ε k) (U k) (v k))
    {τ : ℝ} (hτ : 0<τ) :
    ∃ a : ℕ → ℕ, StrictMono a ∧ ∀ᶠ k in atTop,
      IsPointedApproximation (p (a k)) 0 (r (a k)/1024) 2 τ
        (fun x => (r (a k)/1024)⁻¹ • (v (a k) x-v (a k) (p (a k)))) := by
  obtain ⟨a,ha,Y,dY,hproper,q,δ,V,F,_hδ,hδ0,hV,_hF,hFq,hvalues,hiso,himage⟩ :=
    hX.first_order_euclidean_limit hn hK p r ε hr hr0 hcurv hε hε1 hε0 U v hsplit
  let := dY
  let := hproper
  have hcurv5 (k : ℕ) : -1≤K*(16*(5*r (a k)))^2 := by
    simpa only [show 16*(5*r (a k))=80*r (a k) by ring] using hcurv (a k)
  have hsplit5 (k : ℕ) : FirstOrderSplittingOn (hausdorff n X) hX.quadratic
      (p (a k)) (16*(5*r (a k))) (ε (a k)) (U (a k)) (v (a k)) := by
    simpa only [show 16*(5*r (a k))=80*r (a k) by ring] using hsplit (a k)
  have hm := hX.first_order_uniform_distortion hn hK (p∘a) (fun k => 5*r (a k)) (ε∘a)
    (fun k => mul_pos (by norm_num) (hr (a k)))
    (by simpa only [mul_zero,Function.comp_apply] using (hr0.comp ha.tendsto_atTop).const_mul 5)
    hcurv5 (fun k => hε (a k)) (fun k => hε1 (a k)) (hε0.comp ha.tendsto_atTop)
    (U∘a) (v∘a) hsplit5 (show 0<τ/5120 by positivity)
  refine ⟨a,ha,?_⟩
  filter_upwards [hm,hvalues (τ/8192) (by positivity),
    hδ0.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/8192)),
    hδ0.eventually (gt_mem_nhds (show 0<τ/8192 by positivity))] with k hk hv hd hdt
  have hrk := hr (a k)
  let f : X → Euclidean n := fun x => (r (a k)/1024)⁻¹ • (v (a k) x-v (a k) (p (a k)))
  have hf (x : X) : f x=(1024:ℝ) • ((r (a k))⁻¹ • (v (a k) x-v (a k) (p (a k)))) := by
    dsimp [f]
    rw [smul_smul]
    congr 1
    field_simp
  refine ⟨?_,?_,?_⟩
  · simpa [f] using hτ.le
  · intro x y hx hy
    have hx' : dist x (p (a k))≤5*r (a k)/48 := by linarith
    have hy' : dist y (p (a k))≤5*r (a k)/48 := by linarith
    have hh := hk x y hx' hy'
    simp only [Function.comp_apply] at hh
    have he : dist (f x) (f y)=dist (v (a k) x) (v (a k) y)/(r (a k)/1024) := by
      dsimp [f]
      rw [dist_smul₀,Real.norm_of_nonneg (by positivity),dist_sub_right,div_eq_inv_mul]
      ring
    change |dist (f x) (f y)-dist x y/(r (a k)/1024)|≤τ
    rw [he]
    have he' : dist (v (a k) x) (v (a k) y)/(r (a k)/1024)-dist x y/(r (a k)/1024)=
        5120*(dist (v (a k) x) (v (a k) y)/(5*r (a k))-dist x y/(5*r (a k))) := by
      field_simp
      ring
    rw [he',abs_mul,abs_of_pos (by norm_num : (0:ℝ)<5120)]
    linarith
  · intro y hy
    obtain ⟨x,hx,hxy⟩ := local_isometry_density_transfer hrk hτ hd.le hdt.le le_rfl
      (V k) (fun x => (r (a k))⁻¹ • (v (a k) x-v (a k) (p (a k)))) F
      (hV k) hFq hiso himage hv y hy
    refine ⟨x,hx,?_⟩
    change dist (f x) y≤τ
    rw [hf]
    exact hxy

end RegularPointCoordinates

end

end OAI
