import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.ContDiffSmoothFiniteWave

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Matrix MvPolynomial
open scoped Topology ContDiff Matrix.Norms.Elementwise
section
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {X : Type*}
theorem generated_cutoff_wave_derivative_estimate [TopologicalSpace X]
    (g : X → σ → σ → (σ → ℝ) → ℂ) (b : X → σ → (σ → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j)) (hb : ∀ p i, ContDiff ℝ ∞ (b p i))
    (hg0 : ∀ p i j, g p i j 0 = if i = j then 1 else 0)
    (hdg0 : ∀ p i j, fderiv ℝ (g p i j) 0 = 0)
    (hgc : ∀ i j k, Continuous (fun q : X × (σ → ℝ) => iteratedFDeriv ℝ k (g q.1 i j) q.2))
    (hbc : ∀ i k, Continuous (fun q : X × (σ → ℝ) => iteratedFDeriv ℝ k (b q.1 i) q.2))
    (s : X → ℂ) (hs : Continuous s) (z : X → σ → ℂ) (hz : ∀ i, Continuous (fun p => z p i))
    (hz₀ : ∀ p, z p ≠ 0) (Q : X → σ → σ → ℂ)
    (hQ : ∀ i j, Continuous (fun p => Q p i j)) (hsym : ∀ p i j, Q p i j = Q p j i)
    (hnull : ∀ p, ∑ i, z p i*z p i = -1) (hQz : ∀ p k, ∑ i, z p i*Q p k i = 0)
    (ζ : (σ → ℝ) → ℂ) (hζ : ContDiff ℝ ∞ ζ) (_hζ₀ : ζ =ᶠ[𝓝 0] fun _ => 1)
    (m D : ℕ) (r c : ℝ) (_hr : r ≤ 1) (hc : 0 < c)
    {P : Set X} (hP : IsCompact P) :
    let K := 2*D+3*m+6
    let J := D+m+1
    let S := fun p => smoothPhasePolynomial (g p) (s p) (z p) (Q p) (K+J+1)
    let V := fun p => uniformSmoothWaveAmplitudes (g p) (b p) (S p) (z p) K J
    ∃ C > 0, ∀ p ∈ P, ∀ n : ℝ, 1 ≤ n → ∀ x ∈ Metric.ball (0 : σ → ℝ) r,
      ∀ φ : ℝ, n*((realPolyEval (S p) x).re-φ) ≤ Real.sqrt n*‖x‖-c*n*‖x‖^2 →
      ∀ k ≤ m, ‖iteratedFDeriv ℝ k
        (smoothFiniteWave (realPolyEval (S p)) (fun j x => ζ x * realPolyEval (V p j) x) J n) x‖ ≤
        C*n^k*Real.exp (n*φ) := by
  dsimp only
  let K := 2*D+3*m+6
  let J := D+m+1
  let S := fun p => smoothPhasePolynomial (g p) (s p) (z p) (Q p) (K+J+1)
  let V := fun p => uniformSmoothWaveAmplitudes (g p) (b p) (S p) (z p) K J
  have hu := generated_wave_uniform_jets g b hg hb hg0 hdg0 hgc hbc s hs z hz hz₀ Q hQ
    hsym hnull hQz K J (by dsimp [K]; omega) hP (isCompact_closedBall (0 : σ → ℝ) r)
  have hζB := uniformJetBounds_of_continuous_jets (fun _ : X => ζ)
    (fun k => (hζ.continuous_iteratedFDeriv (le_of_lt (WithTop.coe_lt_coe.mpr
      (ENat.natCast_lt_top k)))).comp continuous_snd) hP (isCompact_closedBall (0 : σ → ℝ) r)
  exact smooth_finite_wave_uniform_derivatives (fun p => realPolyEval (S p))
    (fun p j x => ζ x*realPolyEval (V p j) x)
    (fun p => contDiff_realPolyEval _) (fun p j => hζ.mul (contDiff_realPolyEval _)) m J
    (hu.1.mono subset_rfl Metric.ball_subset_closedBall)
    (fun j => (hζB.mul (fun _ => hζ) (fun _ => contDiff_realPolyEval _) (hu.2.2.2.2 j)).mono
      subset_rfl Metric.ball_subset_closedBall) c hc
end
theorem admissible_cutoff_wave_derivatives {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (g : X → Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (b : X → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j)) (hb : ∀ p i, ContDiff ℝ ∞ (b p i))
    (hg0 : ∀ p i j, g p i j 0 = if i = j then 1 else 0)
    (hdg0 : ∀ p i j, fderiv ℝ (g p i j) 0 = 0)
    (hgc : ∀ i j k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (g q.1 i j) q.2))
    (hbc : ∀ i k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (b q.1 i) q.2))
    (φ : X → PhaseSpace → ℝ) (hφ : ∀ p, ContDiff ℝ ∞ (φ p))
    (hφ0 : Continuous (fun p => φ p 0))
    (hφ2 : Continuous (fun q : X × PhaseSpace => iteratedFDeriv ℝ 2 (φ q.1) q.2))
    (B C : ℝ) {κ : ℝ} (hκ : 0 < κ) (m D : ℕ) :
    ∃ r > 0, ∀ ζ : (Fin 3 → ℝ) → ℂ, ContDiff ℝ ∞ ζ → (ζ =ᶠ[𝓝 0] fun _ => 1) →
      ∃ A > 0, ∀ p z Q, ‖z‖ ≤ B → (∑ i, z i*z i = -1) →
        PhaseMatrixValid (actualHessianForm (φ p)) z κ C Q →
        ∀ n : ℝ, 1 ≤ n → ‖phaseRealVector z-gradient (φ p) 0‖ ≤ (Real.sqrt n)⁻¹ →
        ∀ x ∈ Metric.ball (0 : Fin 3 → ℝ) r, ∀ k ≤ m,
          ‖iteratedFDeriv ℝ k
            (canonicalCutoffWave (g p) (b p) (φ p 0 : ℂ) z Q ζ m D n) x‖ ≤
            A*n^k*Real.exp (n*φ p (WithLp.toLp 2 x)) := by
  let K := 2*D+3*m+6
  let J := D+m+1
  have hgj : ∀ i j k, k < K+J+1 → Continuous (fun p => iteratedFDeriv ℝ k (g p i j) 0) := by
    intro i j k _
    exact (hgc i j k).comp (continuous_id.prodMk continuous_const)
  obtain ⟨R,hR,hga⟩ := all_admissible_generated_gaussian g hg hg0 hdg0 φ hφ hφ0 hφ2
    (K+J+1) (by dsimp [K,J]; omega) hgj B C hκ
  let T := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap
  let a : ℝ := max ‖T‖ 1
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let r := min 1 (R/a)
  have hr : 0 < r := lt_min zero_lt_one (div_pos hR ha)
  refine ⟨r,hr,?_⟩
  intro ζ hζ hζ0
  let H := fun p => actualHessianForm (φ p)
  let W := boundedPhaseSet H B κ C
  have hW : IsCompact W := boundedPhaseSet_isCompact H (continuous_actualHessianForm φ hφ2) B κ C
  let : CompactSpace W := isCompact_iff_compactSpace.mp hW
  let phaseProj : W → X := fun p => p.val.1.1
  let z : W → Fin 3 → ℂ := fun p => p.val.1.2
  let Q : W → ComplexPhaseMatrix := fun p => p.val.2
  have hphaseProj : Continuous phaseProj := (continuous_fst.comp continuous_fst).comp continuous_subtype_val
  have hz : Continuous z := (continuous_snd.comp continuous_fst).comp continuous_subtype_val
  have hQ : Continuous Q := continuous_snd.comp continuous_subtype_val
  have hn (p : W) : ∑ i, z p i*z p i = -1 := p.property.2.1
  have hv (p : W) : PhaseMatrixValid (H (phaseProj p)) (z p) κ C (Q p) := p.property.2.2
  have hgc' : ∀ i j k, Continuous (fun q : W × (Fin 3 → ℝ) =>
      iteratedFDeriv ℝ k (g (phaseProj q.1) i j) q.2) := by
    intro i j k
    exact (hgc i j k).comp ((hphaseProj.comp continuous_fst).prodMk continuous_snd)
  have hbc' : ∀ i k, Continuous (fun q : W × (Fin 3 → ℝ) =>
      iteratedFDeriv ℝ k (b (phaseProj q.1) i) q.2) := by
    intro i k
    exact (hbc i k).comp ((hphaseProj.comp continuous_fst).prodMk continuous_snd)
  obtain ⟨A,hA,hres⟩ := generated_cutoff_wave_derivative_estimate
    (fun p : W => g (phaseProj p)) (fun p => b (phaseProj p)) (fun p => hg (phaseProj p)) (fun p => hb (phaseProj p))
    (fun p => hg0 (phaseProj p)) (fun p => hdg0 (phaseProj p)) hgc' hbc'
    (fun p => (φ (phaseProj p) 0 : ℂ)) (Complex.continuous_ofReal.comp (hφ0.comp hphaseProj))
    z (fun i => (continuous_apply i).comp hz) (fun p => phase_vector_ne_zero _ (hn p))
    Q (fun i j => (continuous_apply j).comp ((continuous_apply i).comp hQ))
    (fun p i j => congrFun (congrFun (hv p).1 j) i) hn
    (fun p k => phase_matrix_annihilation _ _ (hv p).2.1 k)
    ζ hζ hζ0 m D r (κ/2) (min_le_left _ _) (half_pos hκ) isCompact_univ
  refine ⟨A*Real.exp ((a-1)^2/(2*κ)),mul_pos hA (Real.exp_pos _),?_⟩
  intro p z0 Q0 hz0 hn0 hQ0 n hn1 hlin x hx k hk
  let w : W := ⟨((p,z0),Q0),hz0,hn0,hQ0⟩
  have hnpos : 0 < n := lt_of_lt_of_le zero_lt_one hn1
  have hspos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  have hxnorm : ‖x‖ < r := by simpa only [Metric.mem_ball,dist_zero_right] using hx
  have hTx : ‖T x‖ ≤ a*‖x‖ := (T.le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg x))
  have hxR : (WithLp.toLp 2 x : PhaseSpace) ∈ Metric.ball 0 R := by
    change ‖T x-0‖ < R
    rw [sub_zero]
    apply lt_of_le_of_lt hTx
    apply (mul_lt_mul_of_pos_left (hxnorm.trans_le (min_le_right _ _)) ha).trans_le
    exact le_of_eq (mul_div_cancel₀ R ha.ne')
  have hp := hga p z0 Q0 hz0 hn0 hQ0 (WithLp.toLp 2 x) hxR
  have hbound : n*((realPolyEval (smoothPhasePolynomial (g p) (φ p 0 : ℂ) z0 Q0 (K+J+1)) x).re-
      φ p (WithLp.toLp 2 x)) ≤ a*Real.sqrt n*‖x‖-κ*n*‖x‖^2 := by
    have hsq := Real.sq_sqrt hnpos.le
    have hnl : n*‖phaseRealVector z0-gradient (φ p) 0‖ ≤ Real.sqrt n := by
      calc
        _ ≤ n*(Real.sqrt n)⁻¹ := mul_le_mul_of_nonneg_left hlin hnpos.le
        _ = Real.sqrt n := by field_simp; nlinarith
    have hpl := mul_le_mul_of_nonneg_right hnl (norm_nonneg (T x))
    have hmax := mul_le_mul_of_nonneg_left hTx hspos.le
    have hnorm : ‖x‖ ≤ ‖T x‖ := norm_pi_le_euclidean x
    have hquad : ‖x‖^2 ≤ ‖T x‖^2 := by nlinarith [norm_nonneg x,norm_nonneg (T x)]
    have hm := mul_le_mul_of_nonneg_left hquad (mul_nonneg hκ.le hnpos.le)
    have hp' := mul_le_mul_of_nonneg_left hp hnpos.le
    change n*((realPolyEval _ x).re-φ p (WithLp.toLp 2 x)) ≤
      n*(‖phaseRealVector z0-gradient (φ p) 0‖*‖T x‖-κ*‖T x‖^2) at hp'
    nlinarith
  have hbnd := gaussian_phase_coordinate_shift hnpos hκ hbound
  have hh := hres w (mem_univ w) n hn1 x hx
    (φ p (WithLp.toLp 2 x)+(a-1)^2/(2*κ)/n) hbnd k hk
  change ‖iteratedFDeriv ℝ k
    (canonicalCutoffWave (g p) (b p) (φ p 0 : ℂ) z0 Q0 ζ m D n) x‖ ≤ _ at hh
  rw [gaussian_phase_shift_exp hnpos.ne'] at hh
  convert hh using 1; ring

end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise

def normalWaveProfile (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (q : NormalWaveParameter) (x : NormalWaveSpace) : ℝ :=
  φ (normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2) x)

lemma contDiff_normalWaveProfile (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {φ : NormalWaveSpace → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (fun w : NormalWaveParameter × PhaseSpace => normalWaveProfile g φ w.1 w.2) :=
  normal_profile_family_smooth g φ hφ

lemma continuous_normalWaveProfile_iteratedFDeriv
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {φ : NormalWaveSpace → ℝ} (hφ : ContDiff ℝ ∞ φ) (K : Set NormalWaveSpace) (k : ℕ) :
    Continuous (fun w : (metricFrameSet g K) × PhaseSpace =>
      iteratedFDeriv ℝ k (normalWaveProfile g φ w.1.val) w.2) := by
  have h : Continuous (fun w : NormalWaveParameter × PhaseSpace =>
      iteratedFDeriv ℝ k (normalWaveProfile g φ w.1) w.2) :=
    continuous_parameter_iteratedFDeriv
      (fun w : NormalWaveParameter × PhaseSpace => normalWaveProfile g φ w.1 w.2)
      (contDiff_normalWaveProfile g hφ) k
  exact h.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

def normalFamilyWave (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ)
    (A : NormalWaveParameter × (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℂ)
    (b : NormalWaveParameter × (Fin 3 → ℝ) → Fin 3 → ℂ)
    (q : NormalWaveParameter) (z : Fin 3 → ℂ) (Q : ComplexPhaseMatrix)
    (ζ : (Fin 3 → ℝ) → ℂ) (m D : ℕ) (n : ℝ) : (Fin 3 → ℝ) → ℂ :=
  canonicalCutoffWave (fun i j x => A (q,x) i j) (fun j x => b (q,x) j)
    (normalWaveProfile g φ q 0 : ℂ) z Q ζ m D n

theorem normal_family_wave_estimates (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (hφ : ContDiff ℝ ∞ φ)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    (A : NormalWaveParameter × (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℂ)
    (b : NormalWaveParameter × (Fin 3 → ℝ) → Fin 3 → ℂ)
    (hA : ContDiff ℝ ∞ A) (hb : ContDiff ℝ ∞ b)
    (hA0 : ∀ q ∈ metricFrameSet g K, ∀ i j, A (q,0) i j = if i = j then 1 else 0)
    (hAd : ∀ q ∈ metricFrameSet g K, ∀ i j, fderiv ℝ (fun x => A (q,x) i j) 0 = 0)
    (B C : ℝ) {κ : ℝ} (hκ : 0 < κ) (m D : ℕ) :
    ∃ r : ℝ, 0 < r ∧ ∀ ζ : (Fin 3 → ℝ) → ℂ, ContDiff ℝ ∞ ζ → (ζ =ᶠ[𝓝 0] fun _ => 1) →
      ∃ T : ℝ, 0 < T ∧ ∀ q ∈ metricFrameSet g K, ∀ (z : Fin 3 → ℂ) (Q : ComplexPhaseMatrix), ‖z‖ ≤ B → (∑ i, z i*z i = -1) →
        PhaseMatrixValid (actualHessianForm (normalWaveProfile g φ q)) z κ C Q →
        ∀ n : ℝ, 1 ≤ n →
        ‖phaseRealVector z-gradient (normalWaveProfile g φ q) 0‖ ≤ (Real.sqrt n)⁻¹ →
        ∀ x ∈ Metric.ball (0 : Fin 3 → ℝ) r, ∀ k ≤ m,
          ‖iteratedFDeriv ℝ k (normalFamilyWave g φ A b q z Q ζ m D n) x‖ ≤
              T*n^k*Real.exp (n*normalWaveProfile g φ q (normalWaveEquiv x)) ∧
          ‖iteratedFDeriv ℝ k (fun y =>
            waveCoordinateOperator (fun i => Pi.single i 1)
              (fun i j y => A (q,y) i j) (fun j y => b (q,y) j)
              (normalFamilyWave g φ A b q z Q ζ m D n) y +
            (n : ℂ)*((n : ℂ)+2)*normalFamilyWave g φ A b q z Q ζ m D n y) x‖ ≤
              T*(n^(D+1))⁻¹*Real.exp (n*normalWaveProfile g φ q (normalWaveEquiv x)) := by
  let X := metricFrameSet g K
  let : CompactSpace X := isCompact_iff_compactSpace.mp (metricFrameSet_isCompact g hK)
  let G : X → Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ := fun q i j x => A (q.val,x) i j
  let β : X → Fin 3 → (Fin 3 → ℝ) → ℂ := fun q j x => b (q.val,x) j
  let Φ : X → PhaseSpace → ℝ := fun q => normalWaveProfile g φ q.val
  have hG (q : X) (i j : Fin 3) : ContDiff ℝ ∞ (G q i j) :=
    (contDiff_pi.mp (contDiff_pi.mp hA i) j).comp (contDiff_const.prodMk contDiff_id)
  have hβ (q : X) (j : Fin 3) : ContDiff ℝ ∞ (β q j) :=
    (contDiff_pi.mp hb j).comp (contDiff_const.prodMk contDiff_id)
  have hG0 (q : X) (i j : Fin 3) : G q i j 0 = if i = j then 1 else 0 := hA0 q.val q.property i j
  have hGd (q : X) (i j : Fin 3) : fderiv ℝ (G q i j) 0 = 0 := hAd q.val q.property i j
  have hGc (i j : Fin 3) (k : ℕ) : Continuous (fun w : X × (Fin 3 → ℝ) =>
      iteratedFDeriv ℝ k (G w.1 i j) w.2) := by
    exact (continuous_parameter_iteratedFDeriv (fun w => A w i j)
      (contDiff_pi.mp (contDiff_pi.mp hA i) j) k).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hβc (j : Fin 3) (k : ℕ) : Continuous (fun w : X × (Fin 3 → ℝ) =>
      iteratedFDeriv ℝ k (β w.1 j) w.2) := by
    exact (continuous_parameter_iteratedFDeriv (fun w => b w j)
      (contDiff_pi.mp hb j) k).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hΦ (q : X) : ContDiff ℝ ∞ (Φ q) :=
    (contDiff_normalWaveProfile g hφ).comp (contDiff_const.prodMk contDiff_id)
  have hΦ0 : Continuous (fun q : X => Φ q 0) :=
    (contDiff_normalWaveProfile g hφ).continuous.comp
      (continuous_subtype_val.prodMk continuous_const)
  have hΦ2 : Continuous (fun w : X × PhaseSpace => iteratedFDeriv ℝ 2 (Φ w.1) w.2) :=
    continuous_normalWaveProfile_iteratedFDeriv g hφ K 2
  obtain ⟨r1,hr1,he1⟩ := admissible_cutoff_wave_derivatives G β hG hβ hG0 hGd hGc hβc
    Φ hΦ hΦ0 hΦ2 B C hκ m D
  obtain ⟨r2,hr2,he2⟩ := admissible_cutoff_wave_residual G β hG hβ hG0 hGd hGc hβc
    Φ hΦ hΦ0 hΦ2 B C hκ m D
  refine ⟨min r1 r2,lt_min hr1 hr2,?_⟩
  intro ζ hζ hζ0
  obtain ⟨T1,hT1,hb1⟩ := he1 ζ hζ hζ0
  obtain ⟨T2,hT2,hb2⟩ := he2 ζ hζ hζ0
  refine ⟨max T1 T2,lt_of_lt_of_le hT1 (le_max_left _ _),?_⟩
  intro q hq z Q hz hn hQ n hn1 hlin x hx k hk
  have hx1 := Metric.ball_subset_ball (min_le_left r1 r2) hx
  have hx2 := Metric.ball_subset_ball (min_le_right r1 r2) hx
  refine ⟨(hb1 ⟨q,hq⟩ z Q hz hn hQ n hn1 hlin x hx1 k hk).trans ?_,
    (hb2 ⟨q,hq⟩ z Q hz hn hQ n hn1 hlin x hx2 k hk).trans ?_⟩
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left T1 T2) (pow_nonneg (le_trans zero_le_one hn1) _))
      (Real.exp_pos _).le
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right T1 T2)
        (inv_nonneg.mpr (pow_nonneg (le_trans zero_le_one hn1) _))) (Real.exp_pos _).le
end

open Set Filter Matrix
open scoped Topology ContDiff
theorem admissible_cutoff_wave_localized_derivatives {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (g : X → Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (b : X → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j)) (hb : ∀ p i, ContDiff ℝ ∞ (b p i))
    (hg0 : ∀ p i j, g p i j 0 = if i = j then 1 else 0)
    (hdg0 : ∀ p i j, fderiv ℝ (g p i j) 0 = 0)
    (hgc : ∀ i j k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (g q.1 i j) q.2))
    (hbc : ∀ i k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (b q.1 i) q.2))
    (φ : X → PhaseSpace → ℝ) (hφ : ∀ p, ContDiff ℝ ∞ (φ p))
    (hφ0 : Continuous (fun p => φ p 0))
    (hφ2 : Continuous (fun q : X × PhaseSpace => iteratedFDeriv ℝ 2 (φ q.1) q.2))
    (B C : ℝ) {κ : ℝ} (hκ : 0 < κ) (m D : ℕ) :
    ∃ r > 0, ∀ ζ : (Fin 3 → ℝ) → ℂ, ContDiff ℝ ∞ ζ → (ζ =ᶠ[𝓝 0] fun _ => 1) →
      ∃ A > 0, ∀ p z Q, ‖z‖ ≤ B → (∑ i, z i*z i = -1) →
        PhaseMatrixValid (actualHessianForm (φ p)) z κ C Q →
        ∀ n : ℝ, 1 ≤ n → ‖phaseRealVector z-gradient (φ p) 0‖ ≤ (Real.sqrt n)⁻¹ →
        ∀ x ∈ Metric.ball (0 : Fin 3 → ℝ) r, ∀ k ≤ m,
          ‖iteratedFDeriv ℝ k
            (canonicalCutoffWave (g p) (b p) (φ p 0 : ℂ) z Q ζ m D n) x‖ ≤
            A*n^k*Real.exp (n*φ p (WithLp.toLp 2 x))*Real.exp (-(κ/2)*n*‖x‖^2) := by
  let K := 2*D+3*m+6
  let J := D+m+1
  have hgj : ∀ i j k, k < K+J+1 → Continuous (fun p => iteratedFDeriv ℝ k (g p i j) 0) := by
    intro i j k _
    exact (hgc i j k).comp (continuous_id.prodMk continuous_const)
  obtain ⟨R,hR,hga⟩ := all_admissible_generated_gaussian g hg hg0 hdg0 φ hφ hφ0 hφ2
    (K+J+1) (by dsimp [K,J]; omega) hgj B C hκ
  let T := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap
  let a : ℝ := max ‖T‖ 1
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let r := min 1 (R/a)
  have hr : 0 < r := lt_min zero_lt_one (div_pos hR ha)
  refine ⟨r,hr,?_⟩
  intro ζ hζ hζ0
  let H := fun p => actualHessianForm (φ p)
  let W := boundedPhaseSet H B κ C
  have hW : IsCompact W := boundedPhaseSet_isCompact H (continuous_actualHessianForm φ hφ2) B κ C
  let : CompactSpace W := isCompact_iff_compactSpace.mp hW
  let phaseProj : W → X := fun p => p.val.1.1
  let z : W → Fin 3 → ℂ := fun p => p.val.1.2
  let Q : W → ComplexPhaseMatrix := fun p => p.val.2
  have hphaseProj : Continuous phaseProj := (continuous_fst.comp continuous_fst).comp continuous_subtype_val
  have hz : Continuous z := (continuous_snd.comp continuous_fst).comp continuous_subtype_val
  have hQ : Continuous Q := continuous_snd.comp continuous_subtype_val
  have hn (p : W) : ∑ i, z p i*z p i = -1 := p.property.2.1
  have hv (p : W) : PhaseMatrixValid (H (phaseProj p)) (z p) κ C (Q p) := p.property.2.2
  have hgc' : ∀ i j k, Continuous (fun q : W × (Fin 3 → ℝ) =>
      iteratedFDeriv ℝ k (g (phaseProj q.1) i j) q.2) := by
    intro i j k
    exact (hgc i j k).comp ((hphaseProj.comp continuous_fst).prodMk continuous_snd)
  have hbc' : ∀ i k, Continuous (fun q : W × (Fin 3 → ℝ) =>
      iteratedFDeriv ℝ k (b (phaseProj q.1) i) q.2) := by
    intro i k
    exact (hbc i k).comp ((hphaseProj.comp continuous_fst).prodMk continuous_snd)
  obtain ⟨A,hA,hres⟩ := generated_cutoff_wave_derivative_estimate
    (fun p : W => g (phaseProj p)) (fun p => b (phaseProj p)) (fun p => hg (phaseProj p)) (fun p => hb (phaseProj p))
    (fun p => hg0 (phaseProj p)) (fun p => hdg0 (phaseProj p)) hgc' hbc'
    (fun p => (φ (phaseProj p) 0 : ℂ)) (Complex.continuous_ofReal.comp (hφ0.comp hphaseProj))
    z (fun i => (continuous_apply i).comp hz) (fun p => phase_vector_ne_zero _ (hn p))
    Q (fun i j => (continuous_apply j).comp ((continuous_apply i).comp hQ))
    (fun p i j => congrFun (congrFun (hv p).1 j) i) hn
    (fun p k => phase_matrix_annihilation _ _ (hv p).2.1 k)
    ζ hζ hζ0 m D r (κ/2/2) (min_le_left _ _) (half_pos (half_pos hκ)) isCompact_univ
  refine ⟨A*Real.exp ((a-1)^2/(2*(κ/2))),mul_pos hA (Real.exp_pos _),?_⟩
  intro p z0 Q0 hz0 hn0 hQ0 n hn1 hlin x hx k hk
  let w : W := ⟨((p,z0),Q0),hz0,hn0,hQ0⟩
  have hnpos : 0 < n := lt_of_lt_of_le zero_lt_one hn1
  have hspos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  have hxnorm : ‖x‖ < r := by simpa only [Metric.mem_ball,dist_zero_right] using hx
  have hTx : ‖T x‖ ≤ a*‖x‖ := (T.le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg x))
  have hxR : (WithLp.toLp 2 x : PhaseSpace) ∈ Metric.ball 0 R := by
    change ‖T x-0‖ < R
    rw [sub_zero]
    apply lt_of_le_of_lt hTx
    apply (mul_lt_mul_of_pos_left (hxnorm.trans_le (min_le_right _ _)) ha).trans_le
    exact le_of_eq (mul_div_cancel₀ R ha.ne')
  have hp := hga p z0 Q0 hz0 hn0 hQ0 (WithLp.toLp 2 x) hxR
  have hbound : n*((realPolyEval (smoothPhasePolynomial (g p) (φ p 0 : ℂ) z0 Q0 (K+J+1)) x).re-
      φ p (WithLp.toLp 2 x)) ≤ a*Real.sqrt n*‖x‖-κ*n*‖x‖^2 := by
    have hsq := Real.sq_sqrt hnpos.le
    have hnl : n*‖phaseRealVector z0-gradient (φ p) 0‖ ≤ Real.sqrt n := by
      calc
        _ ≤ n*(Real.sqrt n)⁻¹ := mul_le_mul_of_nonneg_left hlin hnpos.le
        _ = Real.sqrt n := by field_simp; nlinarith
    have hpl := mul_le_mul_of_nonneg_right hnl (norm_nonneg (T x))
    have hmax := mul_le_mul_of_nonneg_left hTx hspos.le
    have hnorm : ‖x‖ ≤ ‖T x‖ := norm_pi_le_euclidean x
    have hquad : ‖x‖^2 ≤ ‖T x‖^2 := by nlinarith [norm_nonneg x,norm_nonneg (T x)]
    have hm := mul_le_mul_of_nonneg_left hquad (mul_nonneg hκ.le hnpos.le)
    have hp' := mul_le_mul_of_nonneg_left hp hnpos.le
    change n*((realPolyEval _ x).re-φ p (WithLp.toLp 2 x)) ≤
      n*(‖phaseRealVector z0-gradient (φ p) 0‖*‖T x‖-κ*‖T x‖^2) at hp'
    nlinarith
  have hbound' : n*((realPolyEval (smoothPhasePolynomial (g p) (φ p 0 : ℂ) z0 Q0 (K+J+1)) x).re-
      (φ p (WithLp.toLp 2 x)-(κ/2)*‖x‖^2)) ≤ a*Real.sqrt n*‖x‖-(κ/2)*n*‖x‖^2 := by
    nlinarith
  have hbnd := gaussian_phase_coordinate_shift hnpos (half_pos hκ) hbound'
  have hh := hres w (mem_univ w) n hn1 x hx
    (φ p (WithLp.toLp 2 x)-(κ/2)*‖x‖^2+(a-1)^2/(2*(κ/2))/n) hbnd k hk
  change ‖iteratedFDeriv ℝ k
    (canonicalCutoffWave (g p) (b p) (φ p 0 : ℂ) z0 Q0 ζ m D n) x‖ ≤ _ at hh
  rw [gaussian_phase_shift_exp hnpos.ne'] at hh
  rw [show n*(φ p (WithLp.toLp 2 x)-(κ/2)*‖x‖^2) =
    n*φ p (WithLp.toLp 2 x)+(-(κ/2)*n*‖x‖^2) by ring,Real.exp_add] at hh
  convert hh using 1; ring


end YauCounterexamples
end

end OAI
