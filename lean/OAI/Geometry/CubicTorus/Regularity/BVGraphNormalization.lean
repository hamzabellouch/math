import Mathlib
import OAI.Geometry.CubicTorus.Variation.BVColumnMismatchMeasure

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def graphNormalize (r e m : ℝ) (g : Plane → ℝ) (y : Plane) : ℝ :=
  (r*e)⁻¹ * (g (r • y)-r*m)

lemma graphNormalize_contDiff {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (r e m : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (graphNormalize r e m g) := by
  exact contDiff_const.mul ((hg.comp (by fun_prop)).sub contDiff_const)

lemma graphRescale_normalize {r e : ℝ} (hr : r ≠ 0) (he : e ≠ 0)
    (m : ℝ) (g : Plane → ℝ) : graphRescale r e m (graphNormalize r e m g) = g := by
  funext y
  simp only [graphRescale,graphNormalize,smul_smul,mul_inv_cancel₀ hr,one_smul]
  field_simp
  ring

lemma graphNormalize_lipschitz {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {r e : ℝ} (hr : 0 < r) (he : 0 < e) (m : ℝ) :
    LipschitzWith (⟨e⁻¹,inv_nonneg.mpr he.le⟩*K) (graphNormalize r e m g) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hh := hg.dist_le_mul (r • x) (r • y)
  rw [dist_smul₀,Real.norm_eq_abs,abs_of_pos hr,Real.dist_eq] at hh
  have ht := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (mul_nonneg hr.le he.le))
  have hdiff : graphNormalize r e m g x-graphNormalize r e m g y =
      (r*e)⁻¹*(g (r • x)-g (r • y)) := by unfold graphNormalize; ring
  rw [Real.dist_eq,hdiff,abs_mul,abs_of_pos (inv_pos.mpr (mul_pos hr he))]
  apply ht.trans_eq
  change (r*e)⁻¹*((K:ℝ)*(r*dist x y)) = (e⁻¹*(K:ℝ))*dist x y
  field_simp

lemma graphNormalize_energy {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {r e : ℝ} (hr : 0 < r) (he : 0 < e) (m b : ℝ) :
    r^2*e^2*(∫ y in Metric.ball (0 : Plane) b, ‖fderiv ℝ (graphNormalize r e m g) y‖^2) =
      ∫ y in Metric.ball (0 : Plane) (r*b), ‖fderiv ℝ g y‖^2 := by
  have hh := graphRescale_relative_energy (graphNormalize_contDiff hg r e m) hr e m b
    (0 : Plane →L[ℝ] ℝ)
  simpa only [graphRescale_normalize hr.ne' he.ne',smul_zero,sub_zero] using hh.symm

lemma graphNormalize_height {r e α : ℝ} (hr : 0 < r) (he : e ≠ 0)
    (m : ℝ) {g : Plane → ℝ} (hg : ∀ y, |g y| ≤ α*r) (y : Plane) :
    |m+e*graphNormalize r e m g y| ≤ α := by
  have heq : m+e*graphNormalize r e m g y = r⁻¹*g (r • y) := by
    unfold graphNormalize
    field_simp
    ring
  rw [heq,abs_mul,abs_of_pos (inv_pos.mpr hr)]
  apply (mul_le_mul_of_nonneg_left (hg _) (inv_nonneg.mpr hr.le)).trans_eq
  field_simp

lemma planeSquare_subset_closedBall {R : ℝ} (_hR : 0 ≤ R) :
    planeSquare R ⊆ Metric.closedBall 0 (‖planeProductCoordinates.symm.toContinuousLinearMap‖*R) := by
  intro x hx
  have hb : ‖planeProductCoordinates x‖ ≤ R := by
    rw [Prod.norm_def]
    exact max_le (abs_le.mpr hx.1) (abs_le.mpr hx.2)
  rw [Metric.mem_closedBall,dist_zero_right]
  have hh := planeProductCoordinates.symm.toContinuousLinearMap.le_opNorm (planeProductCoordinates x)
  simpa only [ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply] using
    hh.trans (mul_le_mul_of_nonneg_left hb (norm_nonneg _))

lemma ball_subset_planeSquare {R ρ : ℝ} (_hR : 0 ≤ R)
    (hρ : ‖planeProductCoordinates.toContinuousLinearMap‖*ρ ≤ R) :
    Metric.ball (0 : Plane) ρ ⊆ planeSquare R := by
  intro x hx
  have hh := planeProductCoordinates.toContinuousLinearMap.le_opNorm x
  have hn : ‖x‖ ≤ ρ := (by simpa only [Metric.mem_ball,dist_zero_right] using hx : ‖x‖ < ρ).le
  have hb := hh.trans ((mul_le_mul_of_nonneg_left hn (norm_nonneg _)).trans hρ)
  change ‖planeProductCoordinates x‖ ≤ R at hb
  rw [Prod.norm_def] at hb
  exact ⟨abs_le.mp (le_max_left _ _ |>.trans hb),abs_le.mp (le_max_right _ _ |>.trans hb)⟩

lemma planeSquare_mean_abs_le {f : Plane → ℝ} (hf : Continuous f)
    {R α : ℝ} (hR : 0 < R) (hα : ∀ y, |f y| ≤ α) :
    |(∫ y in planeSquare R, f y)/(2*R)^2| ≤ α := by
  have hi : IntegrableOn f (planeSquare R) := hf.continuousOn.integrableOn_compact (isCompact_planeSquare R)
  have hfin : (volume : Measure Plane) (planeSquare R) ≠ ⊤ := (isCompact_planeSquare R).measure_lt_top.ne
  have hb : |∫ y in planeSquare R, f y| ≤ α*(2*R)^2 := by
    apply abs_integral_le_integral_abs.trans
    calc
      _ ≤ ∫ _y in planeSquare R, α := integral_mono hi.norm (integrableOn_const hfin) hα
      _ = _ := by rw [setIntegral_const,planeSquare_volume R hR.le]; simp only [smul_eq_mul]; ring
  rw [abs_div,abs_of_pos (by positivity : 0 < (2*R)^2),div_le_iff₀ (by positivity)]
  exact hb

theorem smooth_graph_normalized_H1 {g : Plane → ℝ} {K : ℝ≥0}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgLip : LipschitzWith K g)
    {r e R b α D : ℝ} (hr : 0 < r) (he : 0 < e) (hR : 0 < R)
    (hs : planeSquare R ⊆ Metric.ball (0 : Plane) b)
    (hh : ∀ y, |g y| ≤ α*r)
    (henergy : (∫ y in Metric.ball (0 : Plane) (r*b), ‖fderiv ℝ g y‖^2) ≤ r^2*e^2*D) :
    ∃ m : ℝ, |m| ≤ α ∧
      (∫ y in planeSquare R, ‖fderiv ℝ (graphNormalize r e m g) y‖^2) ≤ D ∧
      (∫ y in planeSquare R, (graphNormalize r e m g y)^2) ≤
        16*R^2*‖planeProductCoordinates.symm.toContinuousLinearMap‖^2*D := by
  let g₀ := graphNormalize r 1 0 g
  have hL : LipschitzWith K g₀ := by
    have h := graphNormalize_lipschitz hgLip hr (by norm_num : (0:ℝ)<1) 0
    exact h.weaken (by change (1:ℝ)⁻¹*(K:ℝ) ≤ K; simp)
  have hc : Continuous g₀ := (graphNormalize_contDiff hg r 1 0).continuous
  have hgb : (∫ y in Metric.ball (0 : Plane) b, ‖fderiv ℝ g₀ y‖^2) ≤ D*e^2 := by
    have heq := graphNormalize_energy hg hr (by norm_num : (0:ℝ)<1) 0 b
    dsimp only [g₀] at ⊢
    simp only [one_pow,mul_one] at heq
    have htt := heq.le.trans henergy
    nlinarith [sq_pos_of_pos hr]
  have hgs : (∫ y in planeSquare R, ‖fderiv ℝ g₀ y‖^2) ≤ D*e^2 := by
    exact (setIntegral_mono_set (lipschitz_gradient_sq_integrable_ball hL b)
      (Eventually.of_forall fun y ↦ sq_nonneg _) hs.eventuallyLE).trans hgb
  let m := (∫ y in planeSquare R, g₀ y)/(2*R)^2
  refine ⟨m,?_,?_⟩
  · apply planeSquare_mean_abs_le hc hR
    intro y
    simpa only [zero_add,one_mul] using graphNormalize_height hr one_ne_zero 0 hh y
  · have heq : (fun y ↦ e⁻¹*(g₀ y-m)) = graphNormalize r e m g := by
      funext y
      dsimp only [g₀,graphNormalize]
      field_simp
      ring
    have hp := planar_normalized_H1 hL hR he hgs
    change (∫ y in planeSquare R, ‖fderiv ℝ (fun x ↦ e⁻¹*(g₀ x-m)) y‖^2) ≤ D ∧
      (∫ y in planeSquare R, (e⁻¹*(g₀ y-m))^2) ≤ _ at hp
    rw [← heq]
    exact hp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

theorem local_planar_H1_strong_harmonic_approximation {R : ℝ} (hR : 0 < R)
    {S : Set Plane} (hS : IsCompact S) (hball : Metric.ball (0 : Plane) (4 * R) ⊆ S)
    {ζ : Plane → ℝ} {Lζ : ℝ≥0} (hζ : ContDiff ℝ 1 ζ)
    (hζLip : LipschitzWith Lζ ζ) (hζs : tsupport ζ ⊆ S)
    (hζone : ∀ x ∈ Metric.ball (0 : Plane) (4 * R), ζ x = 1)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ x, |ζ x| ≤ A) (hb : ∀ x, ‖fderiv ℝ ζ x‖ ≤ B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : ℕ → Plane → ℝ) (L : ℕ → ℝ≥0),
        (∀ i, LipschitzWith (L i) (f i)) →
      ∀ M D : ℝ, 0 ≤ D →
        (∀ i, (∫ x in S, f i x ^ 2) ≤ M) →
        (∀ i, (∫ x in S, ‖fderiv ℝ (f i) x‖ ^ 2) ≤ D) →
        (∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          tsupport φ ⊆ Metric.ball 0 (4 * R) →
          Tendsto (fun i ↦ ∫ y, f i y * Δ φ y) atTop (𝓝 0)) →
      ∃ (ψ : ℕ → ℕ) (v : Plane → ℝ), StrictMono ψ ∧ ContDiff ℝ (⊤ : ℕ∞) v ∧
        Tendsto (fun i ↦ ∫ x in Metric.ball (0 : Plane) R, (f (ψ i) x-v x)^2) atTop (𝓝 0) ∧
        ∀ ρ : ℝ, 0 ≤ ρ →
          (∫ x in Metric.ball (0 : Plane) ρ, ‖fderiv ℝ v x-fderiv ℝ v 0‖^2) ≤ C*M*ρ^4 := by
  obtain ⟨C₀, hC₀, happ⟩ := planar_H1_strong_harmonic_approximation hR hS hball
  refine ⟨C₀ * (A ^ 2 + 1), by positivity, ?_⟩
  intro f L hf M D hD hM hgrad hw
  have hMnon : 0 ≤ M := (integral_nonneg (fun x ↦ sq_nonneg (f 0 x))).trans (hM 0)
  have hs : HasCompactSupport ζ := hS.of_isClosed_subset isClosed_closure hζs
  let u : ℕ → Plane → ℝ := fun i x ↦ ζ x * f i x
  have huLip (i : ℕ) := exists_lipschitz_cutoff_mul hζLip (hf i) hs
  choose K hK using huLip
  have henergy (i : ℕ) := lipschitz_cutoff_H1 (μ := volume) (hf i) hζ hs hS hζs hA hB ha hb
  have hglobalM (i : ℕ) : (∫ x, u i x ^ 2) ≤ A ^ 2 * M :=
    (henergy i).2.2.1.trans (mul_le_mul_of_nonneg_left (hM i) (sq_nonneg A))
  have hglobalD (i : ℕ) : (∫ x, ‖fderiv ℝ (u i) x‖ ^ 2) ≤
      2 * A ^ 2 * D + 2 * B ^ 2 * M := by
    exact (henergy i).2.2.2.trans (add_le_add
      (mul_le_mul_of_nonneg_left (hgrad i) (by positivity))
      (mul_le_mul_of_nonneg_left (hM i) (by positivity)))
  have hw' (φ : Plane → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφs : HasCompactSupport φ)
      (hφb : tsupport φ ⊆ Metric.ball 0 (4 * R)) :
      Tendsto (fun i ↦ ∫ y, u i y * Δ φ y) atTop (𝓝 0) := by
    have he (i : ℕ) : (fun y ↦ u i y * Δ φ y) = (fun y ↦ f i y * Δ φ y) := by
      funext y
      by_cases hy : y ∈ tsupport φ
      · simp only [u, hζone y (hφb hy), one_mul]
      · have hz : Δ φ y = 0 := image_eq_zero_of_notMem_tsupport
          (fun hh ↦ hy (laplacian_tsupport_subset hφ hh))
        simp only [hz, mul_zero]
    simpa only [he] using hw φ hφ hφs hφb
  obtain ⟨ψ, v, hψ, hv, he, hdec⟩ := happ u K hK (fun i ↦ (henergy i).1)
    (fun i ↦ (henergy i).2.1) (A ^ 2 * M) (2 * A ^ 2 * D + 2 * B ^ 2 * M)
    (by positivity) hglobalM hglobalD hw'
  refine ⟨ψ,v,hψ,hv,?_,?_⟩
  · have heq (i : ℕ) : (∫ x in Metric.ball (0 : Plane) R, (u (ψ i) x-v x)^2) =
        ∫ x in Metric.ball (0 : Plane) R, (f (ψ i) x-v x)^2 := by
      apply setIntegral_congr_fun measurableSet_ball
      intro x hx
      have hx' := (Metric.ball_subset_ball (by linarith : R ≤ 4*R)) hx
      simp only [u,hζone x hx',one_mul]
    simpa only [heq] using he
  · intro ρ hρ
    apply (hdec ρ hρ).trans
    have ht : A^2*M ≤ (A^2+1)*M := by nlinarith
    have ht' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht hC₀.le)
      (pow_nonneg hρ 4)
    nlinarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

lemma exists_planeSquare_cutoff {Q : ℝ} (hQ : 0 < Q) :
    ∃ R : ℝ, ∃ ζ : Plane → ℝ, ∃ L : ℝ≥0, 0 < R ∧
      Metric.ball (0 : Plane) (4*R) ⊆ planeSquare Q ∧
      ContDiff ℝ 1 ζ ∧ LipschitzWith L ζ ∧ tsupport ζ ⊆ planeSquare Q ∧
      (∀ x ∈ Metric.ball (0 : Plane) (4*R), ζ x = 1) ∧
      (∀ x, |ζ x| ≤ 1) ∧ (∀ x, ‖fderiv ℝ ζ x‖ ≤ (L:ℝ)) := by
  let ρ := Q/(‖planeProductCoordinates.toContinuousLinearMap‖+1)
  have hρ : 0 < ρ := div_pos hQ (by positivity)
  have hh : ‖planeProductCoordinates.toContinuousLinearMap‖*ρ ≤ Q := by
    dsimp [ρ]
    rw [← mul_div_assoc,div_le_iff₀ (by positivity : 0 < ‖planeProductCoordinates.toContinuousLinearMap‖+1)]
    nlinarith
  have hb := ball_subset_planeSquare hQ.le hh
  let b : ContDiffBump (0 : Plane) := ⟨ρ/4,ρ/2,by positivity,by linarith⟩
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport b.hasCompactSupport
    (b.contDiff : ContDiff ℝ (⊤ : ℕ∞) b) (by simp)
  refine ⟨ρ/16,b,L,by positivity,?_,(b.contDiff : ContDiff ℝ 1 b),hL,?_,?_,?_,?_⟩
  · apply (Metric.ball_subset_ball (by linarith : 4*(ρ/16) ≤ ρ)).trans hb
  · rw [b.tsupport_eq]
    apply (Metric.closedBall_subset_ball (by change ρ/2 < ρ; linarith)).trans hb
  · intro x hx
    apply b.one_of_mem_closedBall
    exact Metric.ball_subset_closedBall ((Metric.ball_subset_ball (by change 4*(ρ/16) ≤ ρ/4; linarith)) hx)
  · intro x
    rw [abs_of_nonneg (b.nonneg)]
    exact b.le_one
  · intro x
    exact norm_fderiv_le_of_lipschitz ℝ hL

theorem planeSquare_H1_strong_harmonic {Q : ℝ} (hQ : 0 < Q) :
    ∃ R C : ℝ, 0 < R ∧ 0 < C ∧ Metric.ball (0 : Plane) (4*R) ⊆ planeSquare Q ∧
      ∀ (f : ℕ → Plane → ℝ) (L : ℕ → ℝ≥0),
        (∀ i, LipschitzWith (L i) (f i)) →
      ∀ M D : ℝ, 0 ≤ D →
        (∀ i, (∫ x in planeSquare Q, f i x^2) ≤ M) →
        (∀ i, (∫ x in planeSquare Q, ‖fderiv ℝ (f i) x‖^2) ≤ D) →
        (∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          tsupport φ ⊆ Metric.ball 0 (4*R) →
          Tendsto (fun i ↦ ∫ y, f i y*Δ φ y) atTop (𝓝 0)) →
      ∃ (ψ : ℕ → ℕ) (v : Plane → ℝ), StrictMono ψ ∧ ContDiff ℝ (⊤ : ℕ∞) v ∧
        Tendsto (fun i ↦ ∫ x in Metric.ball (0 : Plane) R, (f (ψ i) x-v x)^2) atTop (𝓝 0) ∧
        ∀ ρ : ℝ, 0 ≤ ρ →
          (∫ x in Metric.ball (0 : Plane) ρ, ‖fderiv ℝ v x-fderiv ℝ v 0‖^2) ≤ C*M*ρ^4 := by
  obtain ⟨R,ζ,L,hR,hball,hζ,hL,hs,hone,ha,hb⟩ := exists_planeSquare_cutoff hQ
  obtain ⟨C,hC,happ⟩ := local_planar_H1_strong_harmonic_approximation hR (isCompact_planeSquare Q)
    hball hζ hL hs hone (by norm_num : (0:ℝ)≤1) L.coe_nonneg ha hb
  exact ⟨R,C,hR,hC,hball,happ⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

theorem weakCMC_normalized_graph_residual {U : Set Torus} (hU : IsOpen U)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure U μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H * directionalFlux U D.coordinate D.function)
    {a n : Cover} (hn : ‖n‖ = 1) {r ε e A C : ℝ}
    (hr : 0 < r) (hrsmall : r < 1 / 2) (hε : ε < 1 / 4) (he : 0 < e)
    (htrap : normalCap (quotientMap a) n r (ε * r) ⊆ (closure U)ᶜ ∧
      normalCap (quotientMap a) (-n) r (ε * r) ⊆ U)
    (hcell : Metric.closedBall a r ⊆ {x | ∀ i, 0 < x i ∧ x i < 1})
    (htilt : (∫ z in {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball a r},
      ‖(z.2 : Cover) - n‖ ^ 2 ∂(μ : Measure NormalBundle)) ≤ r ^ 2 * e ^ 2)
    (harea : (μ : Measure NormalBundle).real
      {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball a r} ≤ A * r ^ 2)
    {g : Plane → ℝ} (hg : Continuous g)
    (hcol : (∫ y in Metric.ball (0 : Plane) (r / 4),
      |g y - normalColumnHeight U (quotientMap a) n r y|) ≤ C * r ^ 3 * e ^ 2)
    {φ : Plane → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hs : tsupport φ ⊆ Metric.ball (0 : Plane) (1 / 4))
    {B D Q : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D) (hQ : 0 ≤ Q)
    (hb : ∀ y, |φ y| ≤ B) (hd : ∀ y, ‖fderiv ℝ φ y‖ ≤ D)
    (hq : ∀ y, |Δ φ y| ≤ Q) (m : ℝ) :
    |∫ y : Plane, ((r * e)⁻¹ * (g (r • y) - m)) * Δ φ y| ≤
      (D / 2 + C * Q) * e + |H| * B * A * (r / e) := by
  let φr : Plane → ℝ := fun y ↦ φ (r⁻¹ • y)
  have hφr : ContDiff ℝ (⊤ : ℕ∞) φr := hφ.comp (by fun_prop)
  have hsr : tsupport φr ⊆ Metric.ball (0 : Plane) (r / 4) := by
    simpa only [mul_one_div] using scaled_test_support hr hs
  have hdr (y : Plane) : ‖fderiv ℝ φr y‖ ≤ D / r := by
    rw [fderiv_comp_smul_eq ((hφ.differentiable (by simp)) _), norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    exact (mul_le_mul_of_nonneg_left (hd _) (inv_nonneg.mpr hr.le)).trans_eq (by ring)
  have hqr (y : Plane) : |Δ φr y| ≤ Q / r ^ 2 := by
    rw [laplacian_comp_smul hφ, abs_mul, abs_of_nonneg (sq_nonneg _)]
    exact (mul_le_mul_of_nonneg_left (hq _) (sq_nonneg r⁻¹)).trans_eq (by rw [inv_pow]; ring)
  have hres := weakCMC_graph_residual_bound hU hμ hH hn hr hrsmall hε htrap
    hφr hsr hcell hB (by positivity) (fun y ↦ hb _) hdr hqr hg
  have hbnd : |∫ y : Plane, g y * Δ φr y| ≤
      (D / 2 + C * Q) * r * e ^ 2 + |H| * B * A * r ^ 2 := by
    calc
      _ ≤ (D / r / 2) * (r ^ 2 * e ^ 2) +
          |H| * B * (A * r ^ 2) + (Q / r ^ 2) * (C * r ^ 3 * e ^ 2) :=
        hres.trans (add_le_add (add_le_add
          (mul_le_mul_of_nonneg_left htilt (by positivity))
          (mul_le_mul_of_nonneg_left harea (by positivity)))
          (mul_le_mul_of_nonneg_left hcol (by positivity)))
      _ = _ := by field_simp; ring
  have hc : HasCompactSupport φ := (isCompact_closedBall (0 : Plane) (1 / 4)).of_isClosed_subset
    isClosed_closure (hs.trans Metric.ball_subset_closedBall)
  have hcont : Continuous (fun y : Plane ↦ g (r • y)) := by fun_prop
  rw [centered_scale_laplacian_pairing hcont hφ hc,
    planar_scaled_laplacian_pairing hφ hr, abs_mul,
    abs_of_pos (inv_pos.mpr (mul_pos hr he))]
  have hh := mul_le_mul_of_nonneg_left hbnd (inv_nonneg.mpr (mul_nonneg hr.le he.le))
  apply hh.trans_eq
  field_simp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

lemma integral_polar_tilt_ball {μ : FiniteMeasure NormalBundle} {N : Torus → Cover}
    (hN : Measurable N)
    (hp : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (a n : Cover) (r : ℝ)
    (hc : Metric.ball a r ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) :
    (∫ x in Metric.ball (quotientMap a) r, ‖N x-n‖^2 ∂(spatialNormalMeasure μ : Measure Torus)) =
      ∫ z in {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball a r},
        ‖(z.2 : Cover)-n‖^2 ∂(μ : Measure NormalBundle) := by
  have hs : MeasurableSet {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball a r} :=
    Metric.isOpen_ball.measurableSet.preimage (by fun_prop)
  rw [← integral_indicator Metric.isOpen_ball.measurableSet,
    integral_spatialNormalMeasure μ (((hN.sub_const n).norm.pow_const 2).indicator
      Metric.isOpen_ball.measurableSet), ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [hp] with z hz
  have hm := compactCell_mem_quotient_ball_iff z.1 a r hc
  change (Metric.ball (quotientMap a) r).indicator (fun x ↦ ‖N x-n‖^2) (quotientMap z.1) = _
  by_cases hh : (z.1 : Cover) ∈ Metric.ball a r
  · rw [indicator_of_mem (hm.mpr hh),indicator_of_mem (show z ∈ {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball a r} from hh),hz]
  · rw [indicator_of_notMem (mt hm.mp hh),indicator_of_notMem (show z ∉ {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball a r} from hh)]

lemma polar_tilt_integrable {μ : FiniteMeasure NormalBundle} {N : Torus → Cover}
    (hN : Measurable N) (hu : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    (n : Cover) : Integrable (fun x ↦ ‖N x-n‖^2) (spatialNormalMeasure μ : Measure Torus) := by
  apply Integrable.of_bound ((hN.sub_const n).norm.pow_const 2).aestronglyMeasurable ((1+‖n‖)^2)
  filter_upwards [hu] with x hx
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (by simpa only [hx] using norm_sub_le (N x) n) 2

lemma cubeCenter_closedBall_interior {r : ℝ} (hr : r < 1/2) :
    Metric.closedBall cubeCenter r ⊆ {x | ∀ i, 0 < x i ∧ x i < 1} := by
  intro x hx i
  have hh := (PiLp.norm_apply_le (x-cubeCenter) i).trans
    (show ‖x-cubeCenter‖ ≤ r by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx)
  simp only [PiLp.sub_apply,cubeCenter,Real.norm_eq_abs] at hh
  have ha := abs_le.mp hh
  constructor <;> linarith

theorem weakCMC_spatial_normalized_residual {U : Set Torus} (hU : IsOpen U)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure U μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H*directionalFlux U D.coordinate D.function)
    {N : Torus → Cover} (hN : Measurable N)
    (hp : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hu : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    {n : Cover} (hn : ‖n‖ = 1) {r α e A C : ℝ}
    (hr : 0 < r) (hrs : r < 1/2) (hα : α < 1/4) (he : 0 < e)
    (htrap : normalCap (quotientMap cubeCenter) n r (α*r) ⊆ (closure U)ᶜ ∧
      normalCap (quotientMap cubeCenter) (-n) r (α*r) ⊆ U)
    (htilt : (∫ x in Metric.closedBall (quotientMap cubeCenter) (17*r), ‖N x-n‖^2
      ∂(spatialNormalMeasure μ : Measure Torus)) ≤ r^2*e^2)
    (ha : (spatialNormalMeasure μ : Measure Torus).real (Metric.ball (quotientMap cubeCenter) r) ≤ A*r^2)
    {g : Plane → ℝ} (hg : Continuous g)
    (hcol : (∫ y in Metric.ball (0 : Plane) (r/4),
      |g y-normalColumnHeight U (quotientMap cubeCenter) n r y|) ≤ C*r^3*e^2)
    {φ : Plane → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hs : tsupport φ ⊆ Metric.ball (0 : Plane) (1/4))
    {B D Q : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D) (hQ : 0 ≤ Q)
    (hb : ∀ y, |φ y| ≤ B) (hd : ∀ y, ‖fderiv ℝ φ y‖ ≤ D)
    (hq : ∀ y, |Δ φ y| ≤ Q) (m : ℝ) :
    |∫ y : Plane, graphNormalize r e m g y*Δ φ y| ≤
      (D/2+C*Q)*e+|H| * B*A*(r/e) := by
  have hc := cubeCenter_closedBall_interior hrs
  have hcb := Metric.ball_subset_closedBall.trans hc
  apply weakCMC_normalized_graph_residual hU hμ hH hn hr hrs hα he htrap hc
    (g := g) (m := r*m) ?_ ?_ hg hcol hφ hs hB hD hQ hb hd hq
  · rw [← integral_polar_tilt_ball hN hp cubeCenter n r hcb]
    apply (setIntegral_mono_set (polar_tilt_integrable hN hu n).integrableOn
      (Eventually.of_forall fun x ↦ sq_nonneg _) ?_).trans htilt
    exact (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))).eventuallyLE
  · change cellBallMass μ cubeCenter r ≤ A*r^2
    rwa [cellBallMass_eq_spatialNormalMeasure μ cubeCenter r hcb]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

lemma smooth_compact_test_bounds {φ : Plane → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) :
    ∃ B D Q : ℝ, 0 ≤ B ∧ 0 ≤ D ∧ 0 ≤ Q ∧
      (∀ y, |φ y| ≤ B) ∧ (∀ y, ‖fderiv ℝ φ y‖ ≤ D) ∧ (∀ y, |Δ φ y| ≤ Q) := by
  obtain ⟨B,hB⟩ := hc.exists_bound_of_continuous hφ.continuous
  obtain ⟨D,hD⟩ := (hc.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
    (hφ.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous
  have hl : HasCompactSupport (Δ φ) := hc.of_isClosed_subset isClosed_closure (laplacian_tsupport_subset hφ)
  obtain ⟨Q,hQ⟩ := hl.exists_bound_of_continuous (compact_laplacian_continuous hφ)
  exact ⟨max B 0,max D 0,max Q 0,le_max_right _ _,le_max_right _ _,le_max_right _ _,
    fun y ↦ (hB y).trans (le_max_left _ _),fun y ↦ (hD y).trans (le_max_left _ _),
    fun y ↦ (hQ y).trans (le_max_left _ _)⟩

theorem weakCMC_normalized_sequence_harmonic {U : Set Torus} (hU : IsOpen U)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure U μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H*directionalFlux U D.coordinate D.function)
    {N : Torus → Cover} (hN : Measurable N)
    (hp : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hu : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    (n : ℕ → Cover) (r α e m C : ℕ → ℝ) (g : ℕ → Plane → ℝ) (A : ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hr : ∀ i, 0 < r i) (hrs : ∀ i, r i < 1/2)
    (hα : ∀ i, α i < 1/4) (he : ∀ i, 0 < e i)
    (htrap : ∀ i, normalCap (quotientMap cubeCenter) (n i) (r i) (α i*r i) ⊆ (closure U)ᶜ ∧
      normalCap (quotientMap cubeCenter) (-(n i)) (r i) (α i*r i) ⊆ U)
    (htilt : ∀ i, (∫ x in Metric.closedBall (quotientMap cubeCenter) (17*r i), ‖N x-n i‖^2
      ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (r i)^2*(e i)^2)
    (ha : ∀ i, (spatialNormalMeasure μ : Measure Torus).real (Metric.ball (quotientMap cubeCenter) (r i)) ≤ A*(r i)^2)
    (hg : ∀ i, Continuous (g i))
    (hcol : ∀ i, (∫ y in Metric.ball (0 : Plane) (r i/4),
      |g i y-normalColumnHeight U (quotientMap cubeCenter) (n i) (r i) y|) ≤ C i*(r i)^3*(e i)^2)
    (helim : Tendsto e atTop (𝓝 0)) (hClim : Tendsto C atTop (𝓝 0))
    (hrel : Tendsto (fun i ↦ r i/(e i)^2) atTop (𝓝 0)) :
    ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Metric.ball (0 : Plane) (1/4) →
      Tendsto (fun i ↦ ∫ y, graphNormalize (r i) (e i) (m i) (g i) y*Δ φ y) atTop (𝓝 0) := by
  intro φ hφ hc hs
  obtain ⟨B,D,Q,hB,hD,hQ,hb,hd,hq⟩ := smooth_compact_test_bounds hφ hc
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  have hrE : Tendsto (fun i ↦ r i/e i) atTop (𝓝 0) := by
    have hfun : (fun i ↦ (r i/(e i)^2)*e i) = (fun i ↦ r i/e i) := by
      funext i
      field_simp [(he i).ne']
    simpa only [hfun,mul_zero] using hrel.mul helim
  have hl : Tendsto (fun i ↦ (D/2+C i*Q)*e i+|H| * B*A*(r i/e i)) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_add,add_zero] using
      ((tendsto_const_nhds.add (hClim.mul_const Q)).mul helim).add (hrE.const_mul (|H| * B*A))
  apply squeeze_zero' (Eventually.of_forall fun i ↦ abs_nonneg _) _ hl
  exact Eventually.of_forall fun i ↦ weakCMC_spatial_normalized_residual hU hμ hH hN hp hu
    (hn i) (hr i) (hrs i) (hα i) (he i) (htrap i) (htilt i) (ha i) (hg i) (hcol i)
      hφ hs hB hD hQ hb hd hq (m i)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
open Laplacian
namespace CubicTorus

lemma exists_small_planeSquare : ∃ Q : ℝ, 0 < Q ∧
    planeSquare Q ⊆ Metric.ball (0 : Plane) (1/8) := by
  let K := ‖planeProductCoordinates.symm.toContinuousLinearMap‖
  let Q := 1/(16*(K+1))
  have hK : 0 ≤ K := norm_nonneg _
  have hQ : 0 < Q := by dsimp [Q]; positivity
  refine ⟨Q,hQ,(planeSquare_subset_closedBall hQ.le).trans (Metric.closedBall_subset_ball ?_)⟩
  change K*Q < 1/8
  dsimp [Q]
  rw [← mul_div_assoc,div_lt_iff₀ (by positivity : 0 < 16*(K+1))]
  linarith

lemma strongL2_restrict_ball {f : ℕ → Plane → ℝ} {u : Plane → ℝ}
    (hf : ∀ i, Continuous (f i)) (hu : Continuous u) {R S : ℝ} (hRS : R ≤ S)
    (hlim : Tendsto (fun i ↦ ∫ y in Metric.ball (0 : Plane) S, (f i y-u y)^2) atTop (𝓝 0)) :
    Tendsto (fun i ↦ ∫ y in Metric.ball (0 : Plane) R, (f i y-u y)^2) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun i ↦ integral_nonneg fun y ↦ sq_nonneg _) _ hlim
  apply Eventually.of_forall
  intro i
  exact setIntegral_mono_set
    (((hf i |>.sub hu).pow 2).continuousOn.integrableOn_compact (isCompact_closedBall (0 : Plane) S) |>.mono_set
      Metric.ball_subset_closedBall) (Eventually.of_forall fun y ↦ sq_nonneg _)
    (Metric.ball_subset_ball hRS).eventuallyLE

lemma directionalFlux_congr_ae {E F : Set Torus} (h : E =ᵐ[torusVolume] F)
    (i : Fin 3) (g : Cover → ℝ) : directionalFlux E i g = directionalFlux F i g := by
  exact setIntegral_congr_set (liftSet_congr_ae h)

theorem isMinimizerAt_trapped_harmonic_graphs {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ r₀ Q R D M C : ℝ, 0 < r₀ ∧ 0 < Q ∧ 0 < R ∧ R ≤ 1/8 ∧
      0 ≤ D ∧ 0 ≤ M ∧ 0 < C ∧ Metric.ball (0 : Plane) R ⊆ planeSquare Q ∧
      ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ → ∀ H : ℝ,
        (∀ w : WallVariation, normalFirstVariation μ w = H*directionalFlux E w.coordinate w.function) →
      ∀ N : Torus → Cover, Measurable N →
        (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
        (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
      ∀ (n : ℕ → Cover) (r α e : ℕ → ℝ), (∀ i, ‖n i‖ = 1) →
        (∀ i, 0 < r i) → (∀ i, r i ≤ r₀) → (∀ i, 0 ≤ α i) → (∀ i, α i < 1/4) →
        (∀ i, 0 < e i) → (∀ i, e i ≤ 1/2) →
        Tendsto α atTop (𝓝 0) → Tendsto e atTop (𝓝 0) →
        Tendsto (fun i ↦ r i/(e i)^2) atTop (𝓝 0) →
        (∀ i, normalCap (quotientMap cubeCenter) (n i) (r i) (α i*r i) ⊆ (closure (openRepresentative E))ᶜ ∧
          normalCap (quotientMap cubeCenter) (-(n i)) (r i) (α i*r i) ⊆ openRepresentative E) →
        (∀ i, (∫ x in Metric.closedBall (quotientMap cubeCenter) (17*r i), ‖N x-n i‖^2
          ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (r i)^2*(e i)^2) →
      ∃ (m : ℕ → ℝ) (g : ℕ → Plane → ℝ) (ψ : ℕ → ℕ) (u : Plane → ℝ),
        StrictMono ψ ∧ ContDiff ℝ (⊤ : ℕ∞) u ∧
        (∀ i, ContDiff ℝ (⊤ : ℕ∞) (g i) ∧ LipschitzWith 1 (g i) ∧
          (∀ y, |g i y| ≤ α i*r i) ∧ |m i| ≤ α i ∧
          (∫ y in planeSquare Q, ‖fderiv ℝ (graphNormalize (r i) (e i) (m i) (g i)) y‖^2) ≤ D ∧
          (∫ y in planeSquare Q, (graphNormalize (r i) (e i) (m i) (g i) y)^2) ≤ M ∧
          (∀ s : ℝ, s ≤ r i/4 → torusVolume.real
            (((openRepresentative E) ∆ torusGraphRegion cubeCenter (n i) (g i)) ∩
              Metric.ball (quotientMap cubeCenter) s) ≤
              (r i)^3*(e i)^2*(D*α i+e i*(volume : Measure Plane).real (Metric.ball 0 (1/4))))) ∧
        Tendsto (fun i ↦ ∫ y in Metric.ball (0 : Plane) R,
          (graphNormalize (r (ψ i)) (e (ψ i)) (m (ψ i)) (g (ψ i)) y-u y)^2) atTop (𝓝 0) ∧
        ∀ ρ : ℝ, 0 ≤ ρ →
          (∫ y in Metric.ball (0 : Plane) ρ, ‖fderiv ℝ u y-fderiv ℝ u 0‖^2) ≤ C*M*ρ^4 := by
  obtain ⟨R₀,D,hR₀,hD,happ⟩ := isMinimizerAt_smooth_trapped_approximation hV hE hmin
  obtain ⟨R₁,A,hR₁,hA,harea⟩ := isMinimizerAt_perimeter_upper_density hV hE hmin
  obtain ⟨Q,hQ,hQs⟩ := exists_small_planeSquare
  obtain ⟨R,C,hR,hC,hRQ,hharm⟩ := planeSquare_H1_strong_harmonic hQ
  let M := 16*Q^2*‖planeProductCoordinates.symm.toContinuousLinearMap‖^2*D
  have hMs : 0 ≤ M := by dsimp [M]; positivity
  have hRR : min R (1/8) ≤ 4*R := (min_le_left _ _).trans (by linarith)
  refine ⟨min (min R₀ R₁) (1/4),Q,min R (1/8),D,M,C,by positivity,hQ,by positivity,
    min_le_right _ _,hD,hMs,hC,(Metric.ball_subset_ball hRR).trans hRQ,?_⟩
  intro μ hμ H hH N hN hp hu n r α e hn hr hrr hα0 hα he hes hαlim helim hrel htrap htilt
  have hr₀ (i) : r i ≤ R₀ := (hrr i).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hr₁ (i) : r i ≤ R₁ := (hrr i).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hrs (i) : r i < 1/2 := lt_of_le_of_lt ((hrr i).trans (min_le_right _ _)) (by norm_num)
  have ha (i) := harea μ hμ (quotientMap cubeCenter) (r i) (hr i) (hr₁ i)
  have hgraphs (i) := happ μ hμ N hN hp hu (n i) (hn i) (r i) (α i) (e i)
    (hr i) (hr₀ i) (hα0 i) (hα i) (he i) (hes i) (htrap i) (htilt i)
  choose g hg hL hh henergy herror using hgraphs
  have hmeans (i) := smooth_graph_normalized_H1 (hg i) (hL i) (hr i) (he i) hQ hQs (hh i)
    (by simpa only [mul_one_div] using henergy i)
  choose m hm hgrad hval using hmeans
  let f i := graphNormalize (r i) (e i) (m i) (g i)
  let L (i : ℕ) : ℝ≥0 := ⟨(e i)⁻¹,inv_nonneg.mpr (he i).le⟩*1
  have hfL (i) : LipschitzWith (L i) (f i) := graphNormalize_lipschitz (hL i) (hr i) (he i) (m i)
  have hUE := isMinimizerAt_openRepresentative_ae hV hE hmin
  have hμU := hμ.congr_ae hUE.symm
  have hHU (w : WallVariation) : normalFirstVariation μ w = H*directionalFlux (openRepresentative E) w.coordinate w.function := by
    rw [directionalFlux_congr_ae hUE]
    exact hH w
  let B i := D*α i+e i*(volume : Measure Plane).real (Metric.ball 0 (1/4))
  have hBlim : Tendsto B atTop (𝓝 0) := by
    simpa only [mul_zero,zero_mul,zero_add] using (hαlim.const_mul D).add (helim.mul_const ((volume : Measure Plane).real (Metric.ball 0 (1/4))))
  have hcol (i) : (∫ y in Metric.ball (0 : Plane) (r i/4),
      |g i y-normalColumnHeight (openRepresentative E) (quotientMap cubeCenter) (n i) (r i) y|) ≤
      B i*(r i)^3*(e i)^2 := by
    exact (herror i).1.trans_eq (by dsimp [B]; ring)
  have hw := weakCMC_normalized_sequence_harmonic (isOpen_openRepresentative E) hμU hHU hN hp hu
    n r α e m B g A hn hr hrs hα he htrap htilt ha (fun i ↦ (hg i).continuous)
    hcol helim hBlim hrel
  obtain ⟨ψ,u,hψ,huS,hconv,huE⟩ := hharm f L hfL M D hD hval hgrad
    (fun φ hφ hc hs ↦ hw φ hφ hc (hs.trans (hRQ.trans (hQs.trans (Metric.ball_subset_ball (by norm_num))))))
  refine ⟨m,g,ψ,u,hψ,huS,?_,?_,huE⟩
  · intro i
    exact ⟨hg i,hL i,hh i,hm i,hgrad i,hval i,(herror i).2⟩
  · exact strongL2_restrict_ball (fun i ↦ (graphNormalize_contDiff (hg (ψ i)) _ _ _).continuous)
      huS.continuous (min_le_left _ _) hconv

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma norm_sub_sq_le_two {X : Type*} [NormedAddCommGroup X] (a b : X) :
    ‖a-b‖^2 ≤ 2*‖a‖^2+2*‖b‖^2 := by
  have hh := norm_sub_le a b
  have hn := norm_nonneg (a-b)
  nlinarith [sq_nonneg (‖a‖-‖b‖)]

lemma graph_relative_energy_bound {f : Plane → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {Q R D : ℝ} (hs : Metric.ball (0 : Plane) R ⊆ planeSquare Q)
    (hD : (∫ y in planeSquare Q, ‖fderiv ℝ f y‖^2) ≤ D) (p : Plane →L[ℝ] ℝ) :
    (∫ y in Metric.ball (0 : Plane) R, ‖fderiv ℝ f y-p‖^2) ≤
      2*D+2*‖p‖^2*(volume : Measure Plane).real (Metric.ball 0 R) := by
  have hc := (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous
  have hi : IntegrableOn (fun y ↦ ‖fderiv ℝ f y‖^2) (planeSquare Q) :=
    (hc.norm.pow 2).continuousOn.integrableOn_compact (isCompact_planeSquare Q)
  have hrel := plane_fderiv_relative_integrable hf p R
  have hb : (∫ y in Metric.ball (0 : Plane) R, ‖fderiv ℝ f y‖^2) ≤ D :=
    (setIntegral_mono_set hi (Eventually.of_forall fun y ↦ sq_nonneg _) hs.eventuallyLE).trans hD
  have hfin : (volume : Measure Plane) (Metric.ball 0 R) ≠ ⊤ := measure_ball_lt_top.ne
  calc
    _ ≤ ∫ y in Metric.ball (0 : Plane) R, 2*‖fderiv ℝ f y‖^2+2*‖p‖^2 :=
      integral_mono hrel (((hi.mono_set hs).const_mul 2).add (integrableOn_const hfin))
        (fun y ↦ norm_sub_sq_le_two _ _)
    _ = 2*(∫ y in Metric.ball (0 : Plane) R, ‖fderiv ℝ f y‖^2)+
        2*‖p‖^2*(volume : Measure Plane).real (Metric.ball 0 R) := by
      rw [integral_add ((hi.mono_set hs).const_mul 2) (integrableOn_const hfin),integral_const_mul,
        setIntegral_const,smul_eq_mul]
      ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hb (by norm_num)) le_rfl

lemma sublevelVolume_ae_left {E F : Set Torus} (h : E =ᵐ[torusVolume] F)
    (q : Cover → ℝ) (t : ℝ) : sublevelVolume E q t = sublevelVolume F q t := by
  unfold sublevelVolume
  exact congrArg ENNReal.toReal (measure_congr (h.inter EventuallyEq.rfl))

lemma symmDiff_ae_left {E F G : Set Torus} (h : E =ᵐ[torusVolume] F) :
    E ∆ G =ᵐ[torusVolume] F ∆ G := h.symmDiff EventuallyEq.rfl

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

theorem isMinimizerAt_trapped_sequential_decay {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ r₀ R K : ℝ, 0 < r₀ ∧ 0 < R ∧ R ≤ 1/8 ∧ 0 ≤ K ∧
      ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ → ∀ H : ℝ,
        (∀ w : WallVariation, normalFirstVariation μ w = H*directionalFlux E w.coordinate w.function) →
      ∀ N : Torus → Cover, Measurable N →
        (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
        (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
      ∀ (n : ℕ → Cover) (r α e : ℕ → ℝ), (∀ i, ‖n i‖ = 1) →
        (∀ i, 0 < r i) → (∀ i, r i ≤ r₀) → (∀ i, 0 ≤ α i) → (∀ i, α i < 1/4) →
        (∀ i, 0 < e i) → (∀ i, e i ≤ 1/2) →
        Tendsto α atTop (𝓝 0) → Tendsto e atTop (𝓝 0) →
        Tendsto (fun i ↦ r i/(e i)^2) atTop (𝓝 0) →
        (∀ i, normalCap (quotientMap cubeCenter) (n i) (r i) (α i*r i) ⊆ (closure (openRepresentative E))ᶜ ∧
          normalCap (quotientMap cubeCenter) (-(n i)) (r i) (α i*r i) ⊆ openRepresentative E) →
        (∀ i, (∫ x in Metric.closedBall (quotientMap cubeCenter) (17*r i), ‖N x-n i‖^2
          ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (r i)^2*(e i)^2) →
      ∀ θ ε : ℝ, 0 < θ → 2*θ ≤ R → 0 < ε →
      ∃ (ψ : ℕ → ℕ) (p : Plane →L[ℝ] ℝ), StrictMono ψ ∧ ∀ᶠ i in atTop,
        bundleOrientedExcess μ (graphSlopeNormal (n (ψ i))
          (e (ψ i) • (InnerProductSpace.toDual ℝ Plane).symm p)) (r (ψ i)*θ) ≤
          (r (ψ i))^2*(e (ψ i))^2*(K*θ^4+ε) := by
  obtain ⟨r₀,Q,R,D,M,C,hr₀,hQ,hR,hRs,hD,hM,hC,hRQ,hg⟩ :=
    isMinimizerAt_trapped_harmonic_graphs hV hE hmin
  refine ⟨min r₀ (1/4),R,32*C*M,by positivity,hR,hRs,by positivity,?_⟩
  intro μ hμ H hH N hN hp hu n r α e hn hr hrr hα0 hα he hes hαlim helim hrel htrap htilt θ ε hθ hθR hε
  obtain ⟨m,g,ψ,u,hψ,huS,hdata,hconv,huE⟩ :=
    hg μ hμ H hH N hN hp hu n r α e hn hr (fun i ↦ (hrr i).trans (min_le_left _ _)) hα0 hα he hes hαlim helim hrel htrap htilt
  let f i := graphNormalize (r i) (e i) (m i) (g i)
  have hf (i) : ContDiff ℝ (⊤ : ℕ∞) (f i) := graphNormalize_contDiff (hdata i).1 _ _ _
  let p := fderiv ℝ u 0
  let A := 2*D+2*‖p‖^2*(volume : Measure Plane).real (Metric.ball 0 (2*θ))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have henergy (i) : (∫ y in Metric.ball (0 : Plane) (2*θ), ‖fderiv ℝ (f i) y-p‖^2) ≤ A :=
    graph_relative_energy_bound (hf i) ((Metric.ball_subset_ball hθR).trans hRQ) (hdata i).2.2.2.2.1 p
  have hmlim : Tendsto m atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hαlim
    exact Eventually.of_forall fun i ↦ (hdata i).2.2.2.1
  have hrlim : Tendsto r atTop (𝓝 0) := by
    have hh := hrel.mul (helim.pow 2)
    simpa only [div_mul_cancel₀ _ (pow_ne_zero 2 (he _).ne'), zero_pow (by norm_num : 2 ≠ 0),mul_zero] using hh
  let B i := D*α i+e i*(volume : Measure Plane).real (Metric.ball 0 (1/4))+e i
  have hBlim : Tendsto B atTop (𝓝 0) := by
    simpa only [mul_zero,zero_mul,zero_add] using
      ((hαlim.const_mul D).add (helim.mul_const ((volume : Measure Plane).real (Metric.ball 0 (1/4))))).add helim
  have hUE := isMinimizerAt_openRepresentative_ae hV hE hmin
  have hμU := hμ.congr_ae hUE.symm
  have hminU := (isMinimizerAt_congr_ae hUE).mpr hmin
  have hmismatch (i) : sublevelVolume
      ((openRepresentative E) ∆ torusGraphRegion cubeCenter (n i) (graphRescale (r i) (e i) (m i) (f i)))
      radialSquared ((r i*(2*θ))^2) < (r i)^3*(e i)^2*B i := by
    rw [show graphRescale (r i) (e i) (m i) (f i) = g i from graphRescale_normalize (hr i).ne' (he i).ne' _ _]
    have hsmall : r i*(2*θ) ≤ 1/4 := by
      have hri := (hrr i).trans (min_le_right _ _)
      nlinarith [mul_le_mul_of_nonneg_left (hθR.trans hRs) (hr i).le]
    unfold sublevelVolume
    rw [sublevelRegion_radialSquared (mul_nonneg (hr i).le (by positivity)) hsmall,cubeBall_eq_metricBall]
    apply ((hdata i).2.2.2.2.2.2 _ ?_).trans_lt
    · dsimp [B]
      nlinarith [mul_pos (pow_pos (hr i) 3) (pow_pos (he i) 3)]
    · calc
        _ ≤ r i*(1/4) := mul_le_mul_of_nonneg_left ((hθR.trans hRs).trans (by norm_num)) (hr i).le
        _ = _ := by ring
  have hconv' := strongL2_restrict_ball (fun i ↦ (hf (ψ i)).continuous) huS.continuous hθR hconv
  obtain ⟨χ,hχ,hdec⟩ := isMinimizerAt_sequential_oriented_decay hV
    (isOpen_openRepresentative E).measurableSet hminU hμU
    (r ∘ ψ) (e ∘ ψ) (m ∘ ψ) (α ∘ ψ) (B ∘ ψ) (n ∘ ψ) (f ∘ ψ)
    (fun i ↦ hr (ψ i)) (fun i ↦ he (ψ i)) (fun i ↦ hn (ψ i)) (fun i ↦ hf (ψ i))
    (hrlim.comp hψ.tendsto_atTop) (helim.comp hψ.tendsto_atTop)
    (hmlim.comp hψ.tendsto_atTop) (hαlim.comp hψ.tendsto_atTop) (hBlim.comp hψ.tendsto_atTop)
    (hrel.comp hψ.tendsto_atTop) hθ huS p hA (fun i ↦ henergy (ψ i)) (huE (2*θ) (by positivity)) hconv'
    (fun i y _ ↦ graphNormalize_height (hr (ψ i)) (he (ψ i)).ne' _ ((hdata (ψ i)).2.2.1) y)
    (fun i ↦ hmismatch (ψ i)) hε
  refine ⟨ψ ∘ χ,p,hψ.comp hχ,?_⟩
  have heq : 2*(C*M*(2*θ)^4)+ε = 32*C*M*θ^4+ε := by ring
  simpa only [Function.comp_def,heq] using hdec

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma diagonal_strictMono {P : ℕ → ℕ → Prop} (hP : ∀ i, ∀ᶠ j in atTop, P i j) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ i, P i (ψ i) := by
  have hh (i) : ∃ N : ℕ, ∀ j ≥ N, P i j := eventually_atTop.mp (hP i)
  choose N hN using hh
  let ψ : ℕ → ℕ := Nat.rec (N 0) (fun i k ↦ max (N (i+1)) (k+1))
  have hψ : StrictMono ψ := strictMono_nat_of_lt_succ (fun i ↦ by
    change ψ i < max (N (i+1)) (ψ i+1)
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _))
  refine ⟨ψ,hψ,fun i ↦ hN i _ ?_⟩
  cases i with
  | zero => exact le_rfl
  | succ i => exact le_max_left _ _

lemma oscillation_le_scaled_tilt {μ : FiniteMeasure NormalBundle} {N : Torus → Cover}
    (hN : Measurable N) (hn : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    {n : Cover} (hnorm : ‖n‖ = 1) (c : Torus) {r e A : ℝ} (hr : 0 < r) (he : 0 ≤ e) (hA : 0 ≤ A)
    (hm : (spatialNormalMeasure μ : Measure Torus).real (Metric.ball c (16*r)) ≤ A*(16*r)^2)
    (ht : (∫ x in Metric.closedBall c (17*r), ‖N x-n‖^2 ∂(spatialNormalMeasure μ : Measure Torus)) ≤ r^2*e^2) :
    normalOscillation (spatialNormalMeasure μ) N c n (8*r) ≤ (A+1)*e := by
  have hmass : (spatialNormalMeasure μ : Measure Torus).real (Metric.closedBall c (8*r)) ≤ (4*A)*(8*r)^2 := by
    calc
      _ ≤ (spatialNormalMeasure μ : Measure Torus).real (Metric.ball c (16*r)) :=
        measureReal_mono (Metric.closedBall_subset_ball (by linarith))
      _ ≤ A*(16*r)^2 := hm
      _ = _ := by ring
  have hexc : normalExcess (spatialNormalMeasure μ) N c n (8*r) ≤ e^2/64 := by
    unfold normalExcess
    apply (div_le_iff₀ (by positivity : 0 < (8*r)^2)).mpr
    have hj := (setIntegral_mono_set (polar_tilt_integrable hN hn n).integrableOn
      (Eventually.of_forall fun x ↦ sq_nonneg ‖N x-n‖)
      (Metric.closedBall_subset_closedBall (by linarith : 8*r ≤ 17*r)).eventuallyLE).trans ht
    convert hj using 1
    · rfl
    · ring
  have hh := (normalOscillation_sq_le_excess (spatialNormalMeasure μ) hN hn hnorm c
    (by positivity : 0 < 8*r) hmass).trans (mul_le_mul_of_nonneg_left hexc (by positivity : 0 ≤ 4*A))
  have hrhs : 0 ≤ (A+1)*e := by positivity
  have hpoly : 4*A*(e^2/64) ≤ ((A+1)*e)^2 := by
    nlinarith [mul_nonneg (sq_nonneg (A+1)) (sq_nonneg e),mul_nonneg (sq_nonneg A) (sq_nonneg e),mul_nonneg hA (sq_nonneg e)]
  nlinarith

theorem isMinimizerAt_trapping_subsequence {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ →
      ∀ N : Torus → Cover, Measurable N →
      (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
      (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
      ∀ c ∈ frontier (openRepresentative E), ∀ (n : ℕ → Cover) (r e : ℕ → ℝ),
      (∀ i, ‖n i‖ = 1) → (∀ i, 0 < r i) → (∀ i, r i ≤ r₀) →
      (∀ i, 0 ≤ e i) → Tendsto e atTop (𝓝 0) →
      (∀ i, (∫ x in Metric.closedBall c (17*r i), ‖N x-n i‖^2
        ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (r i)^2*(e i)^2) →
      ∃ (ψ : ℕ → ℕ) (α : ℕ → ℝ), StrictMono ψ ∧ Tendsto α atTop (𝓝 0) ∧
        (∀ i, 0 < α i ∧ α i < 1/4) ∧
        ∀ i, normalCap c (n (ψ i)) (r (ψ i)) (α i*r (ψ i)) ⊆ (closure (openRepresentative E))ᶜ ∧
          normalCap c (-(n (ψ i))) (r (ψ i)) (α i*r (ψ i)) ⊆ openRepresentative E := by
  obtain ⟨R,δ,hR,hδ,htrap⟩ := isMinimizerAt_quantitative_trapping hV hE hmin
  obtain ⟨S,A,hS,hA,harea⟩ := isMinimizerAt_perimeter_upper_density hV hE hmin
  refine ⟨min R (S/16),by positivity,?_⟩
  intro μ hμ N hN hp hu c hc n r e hn hr hrr he helim ht
  let o i := normalOscillation (spatialNormalMeasure μ) N c (n i) (8*r i)
  have hob (i) : o i ≤ (A+1)*e i :=
    oscillation_le_scaled_tilt hN hu (hn i) c (hr i) (he i) hA.le
      (harea μ hμ c (16*r i) (by have hh := hr i; positivity) (by have hh := (hrr i).trans (min_le_right _ _); linarith)) (ht i)
  have holim : Tendsto o atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun i ↦ div_nonneg (integral_nonneg fun x ↦ norm_nonneg _) (sq_nonneg _))
      (Eventually.of_forall hob)
    simpa only [mul_zero] using helim.const_mul (A+1)
  let α (i : ℕ) : ℝ := 1/((i:ℝ)+8)
  have hα (i) : 0 < α i ∧ α i < 1/4 := by
    have hi : 0 ≤ (i:ℝ) := Nat.cast_nonneg i
    dsimp [α]
    constructor
    · positivity
    · rw [div_lt_iff₀ (by positivity : 0 < (i:ℝ)+8)]
      linarith
  have hαlim : Tendsto α atTop (𝓝 0) := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using
      ((tendsto_add_atTop_iff_nat 8).2 (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hevent (i) : ∀ᶠ j in atTop, 131072*o j < δ^2*(α i/4)^6 :=
    (show Tendsto (fun j ↦ 131072*o j) atTop (𝓝 0) from by simpa only [mul_zero] using holim.const_mul 131072).eventually
      (gt_mem_nhds (by have hh := (hα i).1; positivity))
  obtain ⟨ψ,hψ,hsmall⟩ := diagonal_strictMono hevent
  refine ⟨ψ,α,hψ,hαlim,hα,fun i ↦ ?_⟩
  exact htrap μ hμ N hN hp hu c hc (n (ψ i)) (hn _) (r (ψ i)) (α i)
    (hr _) ((hrr _).trans (min_le_left _ _)) (hα i).1 (hα i).2.le (hsmall i)

end CubicTorus

end
end

end

end OAI
