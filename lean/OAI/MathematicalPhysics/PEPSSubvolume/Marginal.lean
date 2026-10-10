import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.LocalOperators
import OAI.MathematicalPhysics.PEPSSubvolume.Diagonal
import OAI.MathematicalPhysics.PEPSSubvolume.JointSpectrum

namespace OAI

/-! Exact optimizing marginal identities including singular filters. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open scoped BigOperators
open scoped Topology
open Filter
open scoped MatrixOrder
open scoped BigOperators Matrix.Norms.L2Operator
open PolynomialPEPS.PinnedEntropy

namespace PolynomialPEPS.Subvolume.OptimizerMarginal
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open PolynomialPEPS.Subvolume.OptimizerGauge PolynomialPEPS.Subvolume.ActualTransition
open PolynomialPEPS.Subvolume.TraceStripping PolynomialPEPS.Subvolume.SpectralCurve
variable {L q : ℕ}

theorem optimizer_trace_moment (hq : 0 < q)
    (X : ℕ → Finset (Vertex L)) (hX : Monotone X)
    (a : ℕ → ℝ) (ψ : State L q) (n : ℕ)
    (F : (j : ℕ) → LocalPositiveFilter q (X j))
    (hF : IsFilterOptimizer ψ (fun j : Fin n => a j.val) (fun j : Fin n => F j.val))
    (k : ℕ) (hk : k < n)
    (H : Matrix (RegionConfiguration q (X k)) (RegionConfiguration q (X k)) ℂ) :
    let A : ℕ → Operator L q := fun j => liftLocal (X j) (F j).matrix
    let v : State L q := asMap (L := L) (q := q) (orderedPrefix A n) ψ
    (H * reducedDensity v (X k)).trace =
      inner ℂ v (replacementOutput A (X k) ψ k n hk (H*(F k).matrix)) := by
  dsimp only
  have hs := optimizer_strip_outer hq X hX a ψ n F hF (k+1) (by omega)
    (liftLocal (X k) H) (fun j hkj hj =>
      SupportedOn.mono (hX (by omega : k≤j)) ⟨H,rfl⟩)
  dsimp only at hs
  rw [inner_liftLocal_trace,insertedProduct_left _ _ k n hk] at hs
  simpa only [replacementOutput,LinearMap.coe_mk,AddHom.coe_mk,liftLocal_mul] using hs

theorem optimizer_marginal_commute (hq : 0 < q)
    (X : ℕ → Finset (Vertex L)) (hX : Monotone X)
    (a : ℕ → ℝ) (ψ : State L q) (n : ℕ)
    (F : (j : ℕ) → LocalPositiveFilter q (X j))
    (hF : IsFilterOptimizer ψ (fun j : Fin n => a j.val) (fun j : Fin n => F j.val))
    (k : ℕ) (hk : k < n) :
    let A : ℕ → Operator L q := fun j => liftLocal (X j) (F j).matrix
    let v : State L q := asMap (L := L) (q := q) (orderedPrefix A n) ψ
    Commute (F k).matrix (reducedDensity v (X k)) := by
  dsimp only
  let A : ℕ → Operator L q := fun j => liftLocal (X j) (F j).matrix
  let v : State L q := asMap (L := L) (q := q) (orderedPrefix A n) ψ
  let σ := reducedDensity v (X k)
  have hc (H : Matrix (RegionConfiguration q (X k)) (RegionConfiguration q (X k)) ℂ) :
      (H*((F k).matrix*σ)).trace = (H*(σ*(F k).matrix)).trace := by
    rw [← mul_assoc,optimizer_trace_moment hq X hX a ψ n F hF k hk]
    have hm := optimizer_moment_commute hq X hX a ψ n F hF k hk (H*(F k).matrix)
    rw [hm]
    have ht := optimizer_trace_moment hq X hX a ψ n F hF k hk ((F k).matrix*H)
    rw [mul_assoc] at ht
    rw [← ht]
    change ((F k).matrix * H * σ).trace = (H*(σ*(F k).matrix)).trace
    rw [Matrix.trace_mul_comm ((F k).matrix*H) σ,← mul_assoc,
      Matrix.trace_mul_comm (σ*(F k).matrix) H]
  change (F k).matrix*σ = σ*(F k).matrix
  ext i j
  have ht := hc (Matrix.single j i 1)
  simpa [Matrix.trace_single_mul] using ht

theorem optimizer_marginal_spectral (hq : 0 < q)
    (X : ℕ → Finset (Vertex L)) (hX : Monotone X)
    (a : ℕ → ℝ) (ψ : State L q) (n : ℕ)
    (F : (j : ℕ) → LocalPositiveFilter q (X j))
    (hF : IsFilterOptimizer ψ (fun j : Fin n => a j.val) (fun j : Fin n => F j.val))
    (k : ℕ) (hk : k < n) (hp : 2/a k ≠ 0) :
    let A : ℕ → Operator L q := fun j => liftLocal (X j) (F j).matrix
    let v : State L q := asMap (L := L) (q := q) (orderedPrefix A n) ψ
    ∃ (U : unitary (Matrix (RegionConfiguration q (X k)) (RegionConfiguration q (X k)) ℂ))
      (e : RegionConfiguration q (X k) → ℝ),
      (∀ i, 0 ≤ e i) ∧
      (F k).matrix = spectralHom U (fun i => (e i:ℂ)) ∧
      reducedDensity v (X k) = (‖v‖^2:ℂ) • spectralHom U (fun i => (((e i)^(2/a k):ℝ):ℂ)) := by
  dsimp only
  let A : ℕ → Operator L q := fun j => liftLocal (X j) (F j).matrix
  let v : State L q := asMap (L := L) (q := q) (orderedPrefix A n) ψ
  let σ := reducedDensity v (X k)
  have hc := optimizer_marginal_commute hq X hX a ψ n F hF k hk
  obtain ⟨U,e,d,he,hd,hrepF,hrepσ⟩ := JointDiagonalization.exists_positive_unitary
    (F k).matrix σ (F k).positive (reducedDensity_posSemidef v (X k)) hc
  change (F k).matrix = spectralHom U (fun i => (e i:ℂ)) at hrepF
  change σ = spectralHom U (fun i => (d i:ℂ)) at hrepσ
  have hmoment (h : RegionConfiguration q (X k) → ℝ) :
      (∑ i, h i*d i) = ‖v‖^2 * ∑ i, (e i)^(2/a k)*h i := by
    have ht := optimizer_trace_moment hq X hX a ψ n F hF k hk
      (spectralHom U (fun i => (h i:ℂ)))
    change (spectralHom U (fun i => (h i:ℂ))*σ).trace = _ at ht
    rw [hrepσ,← map_mul,trace_spectralHom] at ht
    rw [hrepF,← map_mul] at ht
    have hm := ActualDiagonal.optimizer_diagonal_moment hq X hX a ψ n F hF k hk hp U e h he hrepF
    have hprod : (fun i => (h i:ℂ))*(fun i => (e i:ℂ)) = fun i => (e i*h i:ℂ) := by
      ext i
      simp only [Pi.mul_apply,mul_comm]
    rw [hprod] at ht
    dsimp only at hm
    rw [← ht] at hm
    simpa only [Complex.re_sum,Pi.mul_apply,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,mul_zero,sub_zero] using hm
  have hdval (i : RegionConfiguration q (X k)) : d i = ‖v‖^2 * (e i)^(2/a k) := by
    simpa [Pi.single_apply] using hmoment (Pi.single i 1)
  refine ⟨U,e,he,hrepF,?_⟩
  change σ = _
  rw [hrepσ,← map_smul]
  apply congrArg (spectralHom U)
  ext i
  simp only [Pi.smul_apply,smul_eq_mul,hdval,Complex.ofReal_mul,Complex.ofReal_pow]
  rfl

end PolynomialPEPS.Subvolume.OptimizerMarginal

end

end OAI
