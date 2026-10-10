import Mathlib
import OAI.Geometry.SmoothYau.Estimates.GeneratedPhaseGaussian
import OAI.Geometry.SmoothYau.Limits.ClosedPhaseMatrixValid

namespace OAI

noncomputable section
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
open Set Filter Matrix MvPolynomial
open scoped Topology ContDiff Matrix Matrix.Norms.Elementwise
namespace YauCounterexamples

def actualHessianForm (f : PhaseSpace → ℝ) : RealForm PhaseSpace where
  toFun v := (fderiv ℝ (fderiv ℝ f) 0 v).toLinearMap
  map_add' v w := by ext y; simp
  map_smul' c v := by ext y; simp

@[simp] lemma actualHessianForm_apply (f : PhaseSpace → ℝ) (v w : PhaseSpace) :
    actualHessianForm f v w = fderiv ℝ (fderiv ℝ f) 0 v w := rfl

def phaseRealVector (z : Fin 3 → ℂ) : PhaseSpace := WithLp.toLp 2 (fun i => (z i).re)

lemma real_phase_linear_general (z : Fin 3 → ℂ) (v : PhaseSpace) :
    (∑ i, (v i : ℂ)*z i).re = inner ℝ v (phaseRealVector z) := by
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Pi.star_apply, star_trivial, phaseRealVector, mul_comm]

lemma phase_linear_gradient_bound (f : PhaseSpace → ℝ) (z : Fin 3 → ℂ)
    (v : PhaseSpace) :
    (∑ i, (v i : ℂ)*z i).re - fderiv ℝ f 0 v ≤
      ‖phaseRealVector z - gradient f 0‖ * ‖v‖ := by
  rw [real_phase_linear_general, ←inner_gradient_left, real_inner_comm v (gradient f 0),
    ←inner_sub_right]
  simpa only [mul_comm] using real_inner_le_norm v (phaseRealVector z-gradient f 0)

lemma continuous_actualHessianForm {X : Type*} [TopologicalSpace X]
    (φ : X → PhaseSpace → ℝ)
    (hφ2 : Continuous (fun q : X × PhaseSpace => iteratedFDeriv ℝ 2 (φ q.1) q.2)) :
    Continuous (fun p => phaseFormMatrix (actualHessianForm (φ p))) := by
  have hH := (continuous_hessian_of_iterated φ hφ2).comp
    (continuous_id.prodMk (continuous_const : Continuous (fun _ : X => (0 : PhaseSpace))))
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (hH.clm_apply continuous_const).clm_apply continuous_const

theorem admissible_generated_gaussian {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (g : X → Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j))
    (hg0 : ∀ p i j, g p i j 0 = if i = j then 1 else 0)
    (hdg0 : ∀ p i j, fderiv ℝ (g p i j) 0 = 0)
    (φ : X → PhaseSpace → ℝ) (hφ : ∀ p, ContDiff ℝ ∞ (φ p))
    (hφ0 : Continuous (fun p => φ p 0))
    (hφ2 : Continuous (fun q : X × PhaseSpace => iteratedFDeriv ℝ 2 (φ q.1) q.2))
    (z : X → Fin 3 → ℂ) (hz : Continuous z)
    (Q : X → ComplexPhaseMatrix) (hQ : Continuous Q)
    (hn : ∀ p, ∑ i, z p i*z p i = -1)
    (C : ℝ) {κ : ℝ} (hκ : 0 < κ)
    (hv : ∀ p, PhaseMatrixValid (actualHessianForm (φ p)) (z p) κ C (Q p))
    (L : ℕ) (hL : 2 ≤ L)
    (hgj : ∀ i j k, k < L → Continuous (fun p => iteratedFDeriv ℝ k (g p i j) 0)) :
    ∃ r > 0, ∀ p, ∀ x ∈ Metric.ball (0 : PhaseSpace) r,
      (realPolyEval (smoothPhasePolynomial (g p) (φ p 0 : ℂ) (z p) (Q p) L) (fun i => x i)).re -
        φ p x ≤ ‖phaseRealVector (z p)-gradient (φ p) 0‖*‖x‖-κ*‖x‖^2 := by
  let T := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).toContinuousLinearMap
  have hsymm : ∀ p, ∀ i j, Q p i j = Q p j i :=
    fun p i j => congrFun (congrFun (hv p).1 j) i
  have hQj : ∀ i j, Continuous (fun p => Q p i j) :=
    fun i j => (continuous_apply j).comp ((continuous_apply i).comp hQ)
  have hQz : ∀ p, ∀ k, ∑ i, z p i * Q p k i = 0 :=
    fun p k => phase_matrix_annihilation _ _ (hv p).2.1 k
  have hl : ∀ p ∈ (univ : Set X), ∀ v : PhaseSpace,
      (∑ i, (T v i : ℂ)*z p i).re - fderiv ℝ (φ p) 0 v ≤
        ‖phaseRealVector (z p)-gradient (φ p) 0‖*‖v‖ := by
    intro p _ v
    exact phase_linear_gradient_bound (φ p) (z p) v
  have hgap : ∀ p ∈ (univ : Set X), ∀ v : PhaseSpace,
      (∑ i, ∑ j, (T v i : ℂ)*(T v j : ℂ)*Q p j i).re -
        fderiv ℝ (fderiv ℝ (φ p)) 0 v v ≤ -4*κ*‖v‖^2 := by
    intro p _ v
    exact phase_matrix_gaussian_gap (actualHessianForm (φ p)) (z p) (Q p) (hv p) v
  obtain ⟨r,hr,h⟩ := generated_phase_gaussian (E := PhaseSpace) (X := X) (σ := Fin 3)
    (K := univ) (c := κ) T g hg hg0 hdg0
    (fun p => (φ p 0 : ℂ)) (Complex.continuous_ofReal.comp hφ0)
    z (fun i => (continuous_apply i).comp hz) (fun p => phase_vector_ne_zero _ (hn p))
    Q hsymm hQj hn hQz L hL hgj φ hφ hφ2
    (fun _ => rfl) isCompact_univ (fun p => ‖phaseRealVector (z p)-gradient (φ p) 0‖)
    hκ hl hgap
  exact ⟨r,hr,fun p => h p (mem_univ p)⟩

theorem all_admissible_generated_gaussian {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (g : X → Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j))
    (hg0 : ∀ p i j, g p i j 0 = if i = j then 1 else 0)
    (hdg0 : ∀ p i j, fderiv ℝ (g p i j) 0 = 0)
    (φ : X → PhaseSpace → ℝ) (hφ : ∀ p, ContDiff ℝ ∞ (φ p))
    (hφ0 : Continuous (fun p => φ p 0))
    (hφ2 : Continuous (fun q : X × PhaseSpace => iteratedFDeriv ℝ 2 (φ q.1) q.2))
    (L : ℕ) (hL : 2 ≤ L)
    (hgj : ∀ i j k, k < L → Continuous (fun p => iteratedFDeriv ℝ k (g p i j) 0))
    (B C : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ r > 0, ∀ p z Q, ‖z‖ ≤ B → (∑ i, z i*z i = -1) →
      PhaseMatrixValid (actualHessianForm (φ p)) z κ C Q →
      ∀ x ∈ Metric.ball (0 : PhaseSpace) r,
      (realPolyEval (smoothPhasePolynomial (g p) (φ p 0 : ℂ) z Q L) (fun i => x i)).re -
        φ p x ≤ ‖phaseRealVector z-gradient (φ p) 0‖*‖x‖-κ*‖x‖^2 := by
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
  have hgj' : ∀ i j k, k < L → Continuous (fun p : W => iteratedFDeriv ℝ k (g (partition p) i j) 0) := by
    intro i j k hk
    exact (hgj i j k hk).comp hπ
  have hφ2' : Continuous (fun q : W × PhaseSpace => iteratedFDeriv ℝ 2 (φ (partition q.1)) q.2) :=
    hφ2.comp (f := fun q : W × PhaseSpace => (partition q.1,q.2))
      ((hπ.comp continuous_fst).prodMk continuous_snd)
  obtain ⟨r,hr,h⟩ := admissible_generated_gaussian
    (fun p : W => g (partition p)) (fun p => hg (partition p)) (fun p => hg0 (partition p))
    (fun p => hdg0 (partition p)) (fun p => φ (partition p)) (fun p => hφ (partition p))
    (hφ0.comp hπ) hφ2' z hz Q hQ hn C hκ hv L hL hgj'
  refine ⟨r,hr,?_⟩
  intro p z Q hz hn hQ x hx
  exact h ⟨((p,z),Q),hz,hn,hQ⟩ x hx

end YauCounterexamples

end

end OAI
