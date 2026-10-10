import OAI.Geometry.Perimeter.Regularity.EllipticCutoffEnergy
import OAI.Geometry.Perimeter.Regularity.EllipticUniformGradient
import OAI.Geometry.Perimeter.Regularity.EllipticC1Limit
import OAI.Geometry.Perimeter.Regularity.GeometricHolder

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

 def ellipticGradientConstant (n : ℕ) (K : ℝ) : ℝ :=
  4*K+Real.sqrt (2^(n+2)/volume.real (Metric.ball (0:Euc n) 1))

 theorem linear_uniform_gradient_explicit {θ δ K a B H R : ℝ}
    (hθ : 0<θ) (hθ1 : θ<1) (hK : 1 ≤ K)
    (hc : LinearContractionProperty n θ δ K)
    (ha : 0 ≤ a) (hB : 0 ≤ B) (hH : 0 ≤ H) (hR : 0<R)
    (hsmall : 32*K^2*a ≤ 1) (hforce : 16*K*B ≤ H)
    {A : Euc n → Euc n →L[ℝ] Euc n} (hA : Continuous A)
    {f : Euc n → ℝ} (hf : ContDiff ℝ 1 f) {F : Euc n → Euc n} (hF : Continuous F)
    {U : Set (Euc n)}
    (h : ∀ p∈U, WeakLinearEquation A f F (Metric.ball p R))
    (hnear : ∀ p∈U, ∀ x∈Metric.ball p R, ‖ContinuousLinearMap.id ℝ (Euc n)-A x‖ ≤ δ)
    (hosc : ∀ p∈U, ∀ j x, x∈Metric.ball p (θ^j*R) →
      ‖A p-A x‖ ≤ a*(1/2)^j ∧ ‖F x-F p‖ ≤ B*(1/2)^j)
    (hinit : ∀ p∈U, scaledGradientEnergy f p R 0 ≤ H^2) :
    (∀ p∈U, ‖gradient f p‖ ≤ 2*K*H) ∧
      ∀ j p, p∈U → ∀ p', p'∈U → dist p p' ≤ θ^j*R/2 →
        ‖gradient f p-gradient f p'‖ ≤ ellipticGradientConstant n K*H*(1/2)^j := by
  have hex (p : Euc n) : ∃ q : ℕ → Euc n, p∈U →
      (∀ j, ‖q j-gradient f p‖ ≤ 2*K*H*(1/2)^j) ∧
      (∀ j, scaledGradientEnergy f p (θ^j*R) (q j) ≤ H^2*((1/2)^j)^2) ∧
      ‖gradient f p‖ ≤ 2*K*H := by
    by_cases hp : p∈U
    · obtain ⟨q,hq⟩ := linear_pointwise_iteration hθ hθ1 hK hc ha hB hH hR hsmall hforce
        hA hf hF p (h p hp) (hnear p hp) (hosc p hp) (hinit p hp)
      exact ⟨q,fun _ ↦ hq⟩
    · exact ⟨fun _ ↦ 0,fun hh ↦ (hp hh).elim⟩
  choose q hq using hex
  have hV : 0<volume.real (Metric.ball (0:Euc n) 1) :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume 0 (by norm_num)).ne' measure_ball_lt_top.ne
  let L := Real.sqrt (2^(n+2)/volume.real (Metric.ball (0:Euc n) 1))
  have hL : 0 ≤ L := Real.sqrt_nonneg _
  have hLbig : 2^(n+2) ≤ volume.real (Metric.ball (0:Euc n) 1)*L^2 := by
    dsimp [L]
    rw [Real.sq_sqrt (by positivity),mul_div_cancel₀ _ hV.ne']
  exact ⟨fun p hp ↦ (hq p hp).2.2,gradient_modulus_from_slopes hθ hR hH hL hLbig hf
    (fun p hp ↦ (hq p hp).1) (fun p hp ↦ (hq p hp).2.1)⟩

 theorem linear_family_C1_limit {θ δ K a B r B₀ N : ℝ}
    (hθ : 0<θ) (hθ1 : θ<1) (hK : 1 ≤ K)
    (hc : LinearContractionProperty n θ δ K)
    (ha : 0 ≤ a) (hB : 0 ≤ B) (hr : 0<r) (hsmall : 32*K^2*a ≤ 1)
    {p : Euc n} {A : ℕ → Euc n → Euc n →L[ℝ] Euc n}
    {f : ℕ → Euc n → ℝ} {F : ℕ → Euc n → Euc n}
    (hA : ∀ i, Continuous (A i)) (hf : ∀ i, ContDiff ℝ 1 (f i)) (hF : ∀ i, Continuous (F i))
    (h : ∀ i, WeakLinearEquation (A i) (f i) (F i) (Metric.ball p (4*r)))
    (hnear : ∀ i x, x∈Metric.ball p (4*r) →
      ‖ContinuousLinearMap.id ℝ (Euc n)-A i x‖ ≤ min δ (1/2))
    (hosc : ∀ i x, x∈Metric.closedBall p r → ∀ j y, y∈Metric.ball x (θ^j*r) →
      ‖A i x-A i y‖ ≤ a*(1/2)^j ∧ ‖F i y-F i x‖ ≤ B*(1/2)^j)
    (hb : ∀ i x, |f i x| ≤ B₀) (hN : ∀ i x, ‖F i x‖ ≤ N)
    {g : Euc n → ℝ}
    (hlim : ∀ x∈Metric.ball p r, Tendsto (fun i ↦ f i x) atTop (𝓝 (g x))) :
    ContDiffOn ℝ 1 g (Metric.ball p r) ∧ GeometricHolderAt θ (gradient g) p := by
  let χ : ContDiffBump p := ⟨2*r,3*r,by positivity,by linarith⟩
  have hsχ : tsupport χ⊆Metric.ball p (4*r) := by
    rw [χ.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [χ]; linarith)
  let S := 256*(B₀^2*(∫ x, ‖gradient χ x‖^2)+N^2*(∫ x, (χ x)^2))
  have hS : 0 ≤ S := by
    dsimp [S]
    positivity
  have henergy (i : ℕ) : (∫ x, (χ x)^2*‖gradient (f i) x‖^2) ≤ S :=
    cutoff_energy_bound (hA i) (hf i) (hF i) (h i)
      (fun x hx ↦ (hnear i x hx).trans (min_le_right _ _)) χ.contDiff χ.hasCompactSupport hsχ (hb i) (hN i)
  let H := max (16*K*B) (Real.sqrt (r^(-(n:ℤ))*S))
  have hH : 0 ≤ H := (Real.sqrt_nonneg _).trans (le_max_right _ _)
  have hHe : r^(-(n:ℤ))*S ≤ H^2 := by
    have ht := sq_le_sq₀ (Real.sqrt_nonneg (r^(-(n:ℤ))*S)) hH |>.mpr (le_max_right _ _)
    rwa [Real.sq_sqrt (mul_nonneg (by positivity) hS)] at ht
  have hball (x : Euc n) (hx : x∈Metric.closedBall p r) : Metric.ball x r⊆Metric.ball p (2*r) := by
    intro y hy
    have hh := dist_triangle y x p
    rw [Metric.mem_closedBall] at hx
    rw [Metric.mem_ball] at hy ⊢
    linarith
  have huniform (i : ℕ) := linear_uniform_gradient_explicit hθ hθ1 hK hc ha hB hH hr hsmall
    (le_max_left _ _) (hA i) (hf i) (hF i)
    (fun x hx ↦ (h i).mono ((hball x hx).trans (Metric.ball_subset_ball (by linarith))))
    (fun x hx y hy ↦ (hnear i y ((hball x hx).trans (Metric.ball_subset_ball (by linarith)) hy)).trans (min_le_left _ _))
    (hosc i) (fun x hx ↦ (scaled_energy_le_cutoff (hf i) χ.contDiff χ.hasCompactSupport hr
      (fun y hy ↦ χ.one_of_mem_closedBall (Metric.ball_subset_closedBall (hball x hx hy)))).trans
      ((mul_le_mul_of_nonneg_left (henergy i) (by positivity)).trans hHe))
  obtain ⟨hg,hmod⟩ := C1_limit_of_geometric_gradient_estimates hf hθ (by positivity : 0<r/2)
    (fun i x hx ↦ (huniform i).1 x hx)
    (fun i j x hx y hy hxy ↦ (huniform i).2 j x hx y hy (by nlinarith)) hlim
  refine ⟨hg,r/2,ellipticGradientConstant n K*H,by positivity,?_,?_⟩
  · dsimp [ellipticGradientConstant]
    positivity
  · intro j x hx y hy hxy
    rw [dist_eq_norm]
    exact hmod j x (Metric.ball_subset_ball (by linarith) hx) y
      (Metric.ball_subset_ball (by linarith) hy) hxy

end RPISingularHarnack

end

end OAI
