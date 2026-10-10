import Mathlib
import OAI.Analysis.SymmetricDomains.BishopPositiveInterior
import OAI.Analysis.SymmetricDomains.ScaledDiscC1Limit
import OAI.Analysis.SymmetricDomains.ScaledDiscDeltaC1
import OAI.Analysis.SymmetricDomains.ChoosePositiveC1Regularization
import OAI.Analysis.SymmetricDomains.NoncollapseC1Scaling

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
namespace Release061.Wiener
open scoped Topology
open Set Filter Metric

lemma limitModel_contDiffAt {k : ℕ} {Y : RealDiscParams k → BoundarySpace k}
    (κ : realAlgebra) (hY : ContDiffAt ℝ 1 Y 0) :
    ContDiffAt ℝ 1 (limitModel κ Y) 0 := by
  have hN := (normalSlice_contDiffAt κ hY).comp (f := fun q : RealDiscParams k => (0,q.2)) 0
    (show ContDiffAt ℝ 1 (fun q : RealDiscParams k => (0,q.2)) 0 by fun_prop)
  apply contDiffAt_pi.mpr
  intro i
  exact (Complex.ofRealCLM.contDiff.contDiffAt.comp 0 (by fun_prop)).add
    (contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp 0 (contDiffAt_pi.mp hN i)))

lemma scaledDisc_regularized_differentiable {k : ℕ}
    {f : (Fin (k+1) → ℝ) → Fin k → ℝ} {ε : ℝ}
    (D : LocalBishopData k f ε) (α t δ : ℝ) (q : RealDiscParams k)
    (hp : (t • q.1,q.2,α,δ) ∈ ball 0 D.radius) :
    DifferentiableAt ℝ (scaledDisc (regularizedSlice D.Y α δ) t) q := by
  have hjoint := scaledDisc_regularized_joint_smooth D α t (q := (δ,q)) hp
  exact (hjoint.comp q (show ContDiffAt ℝ 1 (fun x : RealDiscParams k => (δ,x)) q
    by fun_prop)).differentiableAt (by norm_num)

lemma scaledDisc_regularized_interior {k : ℕ}
    {f : (Fin (k+1) → ℝ) → Fin k → ℝ} {ε : ℝ}
    (D : LocalBishopData k f ε) {Ω : Set (Fin k → ℂ)}
    {α d r e₀ : ℝ} (hα : |α| < D.radius) (hd : 0 < d) (hdr : d < D.radius)
    (hrD : r < D.radius) (hre : r < e₀)
    (hinterior : ∀ b : Fin k → ℝ, ‖b‖ < D.radius →
      ∀ e : Fin k → ℝ, ‖e‖ < e₀ → ∀ δ ∈ Ioc 0 d, ∀ z : ClosedDisc,
        (fun i => bishopDisc D.Y (b,e,α,δ) i z) ∈ Ω)
    (t : ℝ) (ht : t ∈ Ioo 0 1) : ∀ᶠ δ in 𝓝[Ioi 0] 0,
      ∀ q ∈ closedBall (0 : RealDiscParams k) r,
        t • scaledDisc (regularizedSlice D.Y α δ) t q ∈ Ω ∧
          DifferentiableAt ℝ (scaledDisc (regularizedSlice D.Y α δ) t) q := by
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hd).filter_mono nhdsWithin_le_nhds] with δ hδ hδd
  intro q hq
  have hbn : ‖t • q.1‖ ≤ r := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) ht.2.le).trans
      ((norm_fst_le q).trans (mem_closedBall_zero_iff.mp hq))
  have hen : ‖q.2‖ ≤ r := (norm_snd_le q).trans (mem_closedBall_zero_iff.mp hq)
  have hp : (t • q.1,q.2,α,δ) ∈ ball 0 D.radius :=
    bishopParams_mem_ball (hbn.trans_lt hrD) (hen.trans_lt hrD) hα
      (by rw [abs_of_pos hδ]; exact hδd.trans hdr)
  constructor
  · dsimp only [scaledDisc]
    rw [smul_smul,mul_inv_cancel₀ ht.1.ne',one_smul]
    exact hinterior _ (hbn.trans_lt hrD) _ (hen.trans_lt hre) δ ⟨hδ,hδd.le⟩ (radialPoint t)
  · exact scaledDisc_regularized_differentiable D α t δ q hp

lemma limitModel_invertible_derivative {k : ℕ} {Y : RealDiscParams k → BoundarySpace k}
    (κ : realAlgebra) (hY : ContDiffAt ℝ 1 Y 0)
    (hunit : IsUnit (fderiv ℝ (fun e : Fin k → ℝ => normalSlice κ Y (0,e)) 0)) :
    ∃ J : RealDiscParams k ≃L[ℝ] (Fin k → ℂ),
      fderiv ℝ (limitModel κ Y) 0 = (J : RealDiscParams k →L[ℝ] (Fin k → ℂ)) := by
  let N : (Fin k → ℝ) → Fin k → ℝ := fun e => normalSlice κ Y (0,e)
  have hN : ContDiffAt ℝ 1 N 0 := (normalSlice_contDiffAt κ hY).comp 0 (by fun_prop)
  let J := ContinuousLinearEquiv.ofUnit hunit.unit
  have hJ : (J : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ)) = fderiv ℝ N 0 := hunit.unit_spec
  have hND : HasFDerivAt N (J : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ)) 0 := by
    rw [hJ]
    exact (hN.differentiableAt (by norm_num)).hasFDerivAt
  let Jfull := ((ContinuousLinearEquiv.refl ℝ (Fin k → ℝ)).prodCongr J).trans
    (Release061.realComplexBlock k)
  exact ⟨Jfull,(Release061.hasFDerivAt_realComplexBlock J hND).fderiv⟩

theorem bishop_transverse_noncollapse {k : ℕ} [NeZero k]
    {f : (Fin (k+1) → ℝ) → Fin k → ℝ} {ε : ℝ}
    (D : LocalBishopData k f ε) {Ω : Set (Fin k → ℂ)}
    (hΩ : IsOpen Ω) (hCP : DiscContinuityWithin k Ω ε)
    {α d u₀ L : ℝ} (hα : 0 < α) (hαr : α < D.radius)
    (hd : 0 < d) (hdr : d < D.radius) (hL : 1 ≤ L) (hu : α*L+d < u₀)
    (hG : ContinuousOn (graphPoint f) (closedBall 0 ε ×ˢ Icc α (α+d)))
    (hgraph : ∀ x ∈ closedBall 0 ε, ∀ u ∈ Ioo 0 u₀, graphPoint f (x,u) ∈ Ω)
    (hlam : ∀ θ, realEvaluation θ D.lam ≤ L)
    (htrans : IsUnit (fderiv ℝ (fun e : Fin k → ℝ => bishopNormal D.kappa D.Y (0,e,α,0)) 0)) :
    ∃ c C t₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < t₀ ∧ ∀ t, 0 < t → t < t₀ →
      ∃ a : Fin k → ℂ, ‖a‖ ≤ C*t ∧ ball a (c*t) ⊆ Ω := by
  have hαabs : |α| < D.radius := by rwa [abs_of_pos hα]
  have hp0 : ((0,0,α,0) : BishopParams k) ∈ ball 0 D.radius :=
    bishopParams_mem_ball (b := 0) (e := 0) (s := α) (δ := 0)
      (by simpa using D.radius_pos) (by simpa using D.radius_pos)
      hαabs (by simpa using D.radius_pos)
  let Y := regularizedSlice D.Y α 0
  have hY : ContDiffAt ℝ 1 Y 0 := regularizedSlice_smooth D hp0
  have hloc : ∀ᶠ q in 𝓝 (0 : RealDiscParams k), ∀ θ,
      (1/2 : ℝ) < dist (circleCos θ) (-1 : ℝ) → ∀ i, realEvaluation θ (Y q i) = 0 := by
    have hP : ContinuousAt (fun q : RealDiscParams k => (q.1,q.2,α,(0 : ℝ))) 0 := by fun_prop
    filter_upwards [hP.eventually (isOpen_ball.mem_nhds hp0)] with q hq
    exact D.localized _ hq rfl
  obtain ⟨r₁,hr₁,hv,hdv,_⟩ := scaledDisc_C1_limit D.cut_division hY hloc
  obtain ⟨e₀,he₀,hinterior⟩ := bishop_positive_interior D hΩ hCP hα hαr hdr hL hu hG hgraph hlam
  let r := min r₁ (min D.radius e₀)/2
  have hr : 0 < r := half_pos (lt_min hr₁ (lt_min D.radius_pos he₀))
  have hrr₁ : r ≤ r₁ := by dsimp [r]; linarith [min_le_left r₁ (min D.radius e₀)]
  have hrD : r < D.radius := by
    have hmin := min_le_right r₁ (min D.radius e₀)
    have hD := min_le_left D.radius e₀
    dsimp [r]; linarith
  have hre : r < e₀ := by
    have hmin := min_le_right r₁ (min D.radius e₀)
    have he := min_le_right D.radius e₀
    dsimp [r]; linarith
  have hKr : closedBall (0 : RealDiscParams k) r ⊆ closedBall 0 r₁ :=
    closedBall_subset_closedBall hrr₁
  let R : ℝ → ℝ → RealDiscParams k → Fin k → ℂ :=
    fun t δ => scaledDisc (regularizedSlice D.Y α δ) t
  have hδC1 (t : ℝ) (ht : t ∈ Ioo 0 1) :=
    scaledDisc_delta_C1_limit D hrD hαabs ht.1.le ht.2.le
  have hδi := scaledDisc_regularized_interior D hαabs hd hdr hrD hre hinterior
  obtain ⟨δ,hreg,hval,hder⟩ := Release061.choose_positive_C1_regularization (R := R) (ψ := limitModel D.kappa Y)
    (show (0 : ℝ) < 1 by norm_num) (hv.mono hKr) (hdv.mono hKr)
    (fun t ht u hu => ((hδC1 t ht).1 u hu).filter_mono nhdsWithin_le_nhds)
    (fun t ht u hu => ((hδC1 t ht).2 u hu).filter_mono nhdsWithin_le_nhds) hδi
  obtain ⟨Jfull,hfull⟩ := limitModel_invertible_derivative D.kappa hY htrans
  apply Release061.noncollapse_of_C1_scaling hr Jfull hfull
    ((limitModel_contDiffAt D.kappa hY).continuousAt_fderiv (by norm_num)) hder
    (hval.tendsto_at (mem_closedBall_self hr.le))
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds] with t ht ht1 q hq
    exact ((hreg t ⟨ht,ht1⟩).2.2 q hq).2
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds] with t ht ht1 q hq
    exact ((hreg t ⟨ht,ht1⟩).2.2 q hq).1

end Release061.Wiener

end

end OAI
