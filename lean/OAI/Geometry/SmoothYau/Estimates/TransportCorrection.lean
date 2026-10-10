import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.BoundedDegreeMonomials

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
namespace YauCounterexamples
variable {σ : Type*} [Fintype σ]

def transportCorrection (A : σ → MvPolynomial σ ℂ) (B V F : MvPolynomial σ ℂ)
    (z : σ → ℂ) (N : ℕ) : MvPolynomial σ ℂ :=
  wavePrimitive z N (-((2:ℂ)⁻¹) • homogeneousComponent N (waveTransport A B V + F))

theorem transportCorrection_homogeneous (A : σ → MvPolynomial σ ℂ)
    (B V F : MvPolynomial σ ℂ) (z : σ → ℂ) (N : ℕ) :
    (transportCorrection A B V F z N).IsHomogeneous (N+1) := by
  apply wavePrimitive_homogeneous
  simpa only [C_mul'] using
    (homogeneousComponent_isHomogeneous N (waveTransport A B V + F)).C_mul (-((2:ℂ)⁻¹))

theorem transportCorrection_raises (A : σ → MvPolynomial σ ℂ)
    (B V F : MvPolynomial σ ℂ) (z : σ → ℂ) (hz : z ≠ 0) (N : ℕ)
    (hA : ∀ i, constantCoeff (A i) = 2*z i)
    (hR : VanishTo (waveTransport A B V + F) N) :
    VanishTo (waveTransport A B (V + transportCorrection A B V F z N) + F) (N+1) := by
  have hp : (-((2:ℂ)⁻¹) • homogeneousComponent N (waveTransport A B V + F)).IsHomogeneous N := by
    simpa only [C_mul'] using
      (homogeneousComponent_isHomogeneous N (waveTransport A B V + F)).C_mul (-((2:ℂ)⁻¹))
  have hd : 2 * waveDirectionalDerivative z (transportCorrection A B V F z N) =
      -homogeneousComponent N (waveTransport A B V + F) := by
    rw [transportCorrection,wavePrimitive_derivative z hz N _ hp,two_mul,← add_smul]
    norm_num
    abel
  have hl := transport_linearization A B z N hA _
    (VanishTo.of_homogeneous (transportCorrection_homogeneous A B V F z N))
  have H := hl.add hR.remove_component
  convert H using 1
  rw [hd,waveTransport_add]
  ring

def transportIter (A : σ → MvPolynomial σ ℂ) (B F : MvPolynomial σ ℂ)
    (z : σ → ℂ) (c : ℂ) : ℕ → MvPolynomial σ ℂ
  | 0 => C c
  | N+1 => transportIter A B F z c N +
      transportCorrection A B (transportIter A B F z c N) F z N

theorem transportIter_spec (A : σ → MvPolynomial σ ℂ)
    (B F : MvPolynomial σ ℂ) (z : σ → ℂ) (hz : z ≠ 0)
    (hA : ∀ i, constantCoeff (A i) = 2*z i) (c : ℂ) (N : ℕ) :
    constantCoeff (transportIter A B F z c N) = c ∧
      VanishTo (waveTransport A B (transportIter A B F z c N) + F) N ∧
      (transportIter A B F z c N).totalDegree ≤ N := by
  induction N with
  | zero => exact ⟨by simp [transportIter],VanishTo.order_zero _,by simp [transportIter]⟩
  | succ N ih =>
    have hc := (VanishTo.of_homogeneous
      (transportCorrection_homogeneous A B (transportIter A B F z c N) F z N)).constantCoeff_eq_zero (by omega)
    refine ⟨?_,transportCorrection_raises A B _ F z hz N hA ih.2.1,?_⟩
    · simp [transportIter,ih.1,hc]
    · exact (totalDegree_add _ _).trans (max_le (by omega)
        (transportCorrection_homogeneous A B (transportIter A B F z c N) F z N).totalDegree_le)

variable {X : Type*} [TopologicalSpace X]

theorem waveTransport_coeffContinuous (A : X → σ → MvPolynomial σ ℂ)
    (hA : ∀ i, CoeffContinuous (fun x => A x i))
    (B V : X → MvPolynomial σ ℂ) (hB : CoeffContinuous B) (hV : CoeffContinuous V) :
    CoeffContinuous (fun x => waveTransport (A x) (B x) (V x)) := by
  exact (CoeffContinuous.sum Finset.univ _ (fun i _ => (hA i).mul (hV.pderiv i))).add (hB.mul hV)

theorem transportIter_coeffContinuous (A : X → σ → MvPolynomial σ ℂ)
    (hA : ∀ i, CoeffContinuous (fun x => A x i)) (B F : X → MvPolynomial σ ℂ)
    (hB : CoeffContinuous B) (hF : CoeffContinuous F) (z : X → σ → ℂ)
    (hz : ∀ i, Continuous (fun x => z x i)) (hz₀ : ∀ x, z x ≠ 0)
    (c : X → ℂ) (hc : Continuous c) (N : ℕ) :
    CoeffContinuous (fun x => transportIter (A x) (B x) (F x) (z x) (c x) N) := by
  classical
  induction N with
  | zero =>
    intro m
    simp only [transportIter,coeff_C]
    split_ifs
    · exact hc
    · exact continuous_const
  | succ N ih =>
    apply ih.add
    apply canonical_wavePrimitive_coeffContinuous z hz hz₀
    exact (((waveTransport_coeffContinuous A hA B _ hB ih).add hF).homogeneousComponent N).smul continuous_const

end YauCounterexamples

end

end OAI
