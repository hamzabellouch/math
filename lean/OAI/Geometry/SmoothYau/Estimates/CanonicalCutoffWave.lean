import Mathlib
import OAI.Geometry.SmoothYau.Geometry.ActualHessianForm
import OAI.Geometry.SmoothYau.Geometry.GaussianLinearDistortion
import OAI.Geometry.SmoothYau.Smoothness.SmoothFiniteWaveSum

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
open Set Filter MvPolynomial
open scoped Topology ContDiff
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {X : Type*}

theorem generated_cutoff_wave_residual_estimate [TopologicalSpace X]
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
    (ζ : (σ → ℝ) → ℂ) (hζ : ContDiff ℝ ∞ ζ) (hζ₀ : ζ =ᶠ[𝓝 0] fun _ => 1)
    (m D : ℕ) (r c : ℝ) (hr : r ≤ 1) (hc : 0 < c)
    {P : Set X} (hP : IsCompact P) :
    let K := 2*D+3*m+6
    let J := D+m+1
    let S := fun p => smoothPhasePolynomial (g p) (s p) (z p) (Q p) (K+J+1)
    let V := fun p => uniformSmoothWaveAmplitudes (g p) (b p) (S p) (z p) K J
    ∃ C > 0, ∀ p ∈ P, ∀ n : ℝ, 1 ≤ n → ∀ x ∈ Metric.ball (0 : σ → ℝ) r,
      ∀ φ : ℝ, n*((realPolyEval (S p) x).re-φ) ≤ Real.sqrt n*‖x‖-c*n*‖x‖^2 →
      ∀ k ≤ m, ‖iteratedFDeriv ℝ k (fun y =>
        waveCoordinateOperator (fun i => Pi.single i 1) (g p) (b p) (smoothFiniteWave (realPolyEval (S p)) (fun j x => ζ x * realPolyEval (V p j) x) J n) y +
         (n : ℂ)*((n : ℂ)+2)*smoothFiniteWave (realPolyEval (S p)) (fun j x => ζ x * realPolyEval (V p j) x) J n y) x‖ ≤
        C*(n^(D+1))⁻¹*Real.exp (n*φ) := by
  dsimp only
  let K := 2*D+3*m+6
  let J := D+m+1
  let S := fun p => smoothPhasePolynomial (g p) (s p) (z p) (Q p) (K+J+1)
  let V := fun p => uniformSmoothWaveAmplitudes (g p) (b p) (S p) (z p) K J
  have hu := generated_wave_uniform_jets g b hg hb hg0 hdg0 hgc hbc s hs z hz hz₀ Q hQ
    hsym hnull hQz K J (by dsimp [K]; omega) hP (isCompact_closedBall (0 : σ → ℝ) r)
  have hgB (i j) := (uniformJetBounds_of_continuous_jets (fun p => g p i j) (hgc i j) hP
    (isCompact_closedBall (0 : σ → ℝ) r)).mono subset_rfl Metric.ball_subset_closedBall
  have hbB (i) := (uniformJetBounds_of_continuous_jets (fun p => b p i) (hbc i) hP
    (isCompact_closedBall (0 : σ → ℝ) r)).mono subset_rfl Metric.ball_subset_closedBall
  apply cutoff_polynomial_wave_residual_bound g b hg hb S V ζ hζ hζ₀ m D J le_rfl r c hr hc P
    hgB hbB (hu.1.mono subset_rfl Metric.ball_subset_closedBall)
    (fun j => (hu.2.2.2.2 j).mono subset_rfl Metric.ball_subset_closedBall)
  · intro p hp j
    exact (generated_wave_remainders_vanish (g p) (b p) (hg p) (hb p) (hg0 p) (hdg0 p)
      (s p) (z p) (Q p) (hz₀ p) (hsym p) (hnull p) (hQz p) K J (by dsimp [K]; omega)).1 j
  · intro p hp j hj
    exact (generated_wave_remainders_vanish (g p) (b p) (hg p) (hb p) (hg0 p) (hdg0 p)
      (s p) (z p) (Q p) (hz₀ p) (hsym p) (hnull p) (hQz p) K J (by dsimp [K]; omega)).2 j hj

end

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
open Set Filter Matrix MvPolynomial
open scoped Topology ContDiff Matrix.Norms.Elementwise

def canonicalCutoffWave (g : Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (b : Fin 3 → (Fin 3 → ℝ) → ℂ) (s : ℂ) (z : Fin 3 → ℂ)
    (Q : ComplexPhaseMatrix) (ζ : (Fin 3 → ℝ) → ℂ) (m D : ℕ) (n : ℝ) :
    (Fin 3 → ℝ) → ℂ :=
  let K := 2*D+3*m+6
  let J := D+m+1
  let S := smoothPhasePolynomial g s z Q (K+J+1)
  let V := uniformSmoothWaveAmplitudes g b S z K J
  smoothFiniteWave (realPolyEval S) (fun j x => ζ x * realPolyEval (V j) x) J n

lemma norm_pi_le_euclidean (x : Fin 3 → ℝ) : ‖x‖ ≤ ‖(WithLp.toLp 2 x : PhaseSpace)‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    (fun i => PiLp.norm_apply_le (WithLp.toLp 2 x : PhaseSpace) i)

theorem admissible_cutoff_wave_residual {X : Type*} [TopologicalSpace X] [CompactSpace X]
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
          ‖iteratedFDeriv ℝ k (fun y =>
            waveCoordinateOperator (fun i => Pi.single i 1) (g p) (b p)
              (canonicalCutoffWave (g p) (b p) (φ p 0 : ℂ) z Q ζ m D n) y +
            (n : ℂ)*((n : ℂ)+2)*canonicalCutoffWave (g p) (b p) (φ p 0 : ℂ) z Q ζ m D n y) x‖ ≤
            A*(n^(D+1))⁻¹*Real.exp (n*φ p (WithLp.toLp 2 x)) := by
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
  let partition : W → X := fun p => p.val.1.1
  let z : W → Fin 3 → ℂ := fun p => p.val.1.2
  let Q : W → ComplexPhaseMatrix := fun p => p.val.2
  have hπ : Continuous partition := (continuous_fst.comp continuous_fst).comp continuous_subtype_val
  have hz : Continuous z := (continuous_snd.comp continuous_fst).comp continuous_subtype_val
  have hQ : Continuous Q := continuous_snd.comp continuous_subtype_val
  have hn (p : W) : ∑ i, z p i*z p i = -1 := p.property.2.1
  have hv (p : W) : PhaseMatrixValid (H (partition p)) (z p) κ C (Q p) := p.property.2.2
  have hgc' : ∀ i j k, Continuous (fun q : W × (Fin 3 → ℝ) =>
      iteratedFDeriv ℝ k (g (partition q.1) i j) q.2) := by
    intro i j k
    exact (hgc i j k).comp ((hπ.comp continuous_fst).prodMk continuous_snd)
  have hbc' : ∀ i k, Continuous (fun q : W × (Fin 3 → ℝ) =>
      iteratedFDeriv ℝ k (b (partition q.1) i) q.2) := by
    intro i k
    exact (hbc i k).comp ((hπ.comp continuous_fst).prodMk continuous_snd)
  obtain ⟨A,hA,hres⟩ := generated_cutoff_wave_residual_estimate
    (fun p : W => g (partition p)) (fun p => b (partition p)) (fun p => hg (partition p)) (fun p => hb (partition p))
    (fun p => hg0 (partition p)) (fun p => hdg0 (partition p)) hgc' hbc'
    (fun p => (φ (partition p) 0 : ℂ)) (Complex.continuous_ofReal.comp (hφ0.comp hπ))
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
  change ‖iteratedFDeriv ℝ k (fun y =>
    waveCoordinateOperator _ (g p) (b p) (canonicalCutoffWave (g p) (b p) (φ p 0 : ℂ) z0 Q0 ζ m D n) y +
    (n : ℂ)*((n : ℂ)+2)*canonicalCutoffWave (g p) (b p) (φ p 0 : ℂ) z0 Q0 ζ m D n y) x‖ ≤ _ at hh
  rw [gaussian_phase_shift_exp hnpos.ne'] at hh
  convert hh using 1
  ring


end YauCounterexamples
end

end OAI
