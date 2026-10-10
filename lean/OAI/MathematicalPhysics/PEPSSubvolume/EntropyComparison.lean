import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.LocalOperators
import OAI.MathematicalPhysics.PEPSSubvolume.EntropyHolder
import OAI.MathematicalPhysics.PEPSSubvolume.PhysicalCurve

namespace OAI

/-! Marginal regularization and unpinned nested entropy comparison. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open scoped BigOperators
open scoped Topology
open Filter
open scoped MatrixOrder
open scoped BigOperators Matrix.Norms.L2Operator
open scoped ComplexOrder BigOperators Matrix.Norms.L2Operator
open Matrix
open Filter Topology
open Set Filter Complex Complex.HadamardThreeLines
open PolynomialPEPS.PinnedEntropy

namespace PolynomialPEPS.Subvolume
open scoped Matrix.Norms.L2Operator

namespace SpectralCurve
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrix_eq_spectralHom {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    A = spectralHom hA.eigenvectorUnitary (fun i => (hA.eigenvalues i : ℂ)) := by
  exact hA.spectral_theorem

theorem trace_rates_pairing {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (b : ι → ℝ) :
    (Matrix.trace (spectralHom hA.eigenvectorUnitary (fun i => (b i : ℂ)) * A)).re =
      ∑ i, b i * hA.eigenvalues i := by
  conv_lhs => arg 1; arg 1; arg 2; rw [matrix_eq_spectralHom hA]
  rw [← map_mul, trace_spectralHom]
  simp only [Pi.mul_apply, Complex.re_sum, ← Complex.ofReal_mul, Complex.ofReal_re]

end SpectralCurve

namespace MarginalRegularization
variable {ι : Type*} [Fintype ι]

def probabilities (lam : ι → ℝ) (ε : ℝ) (i : ι) : ℝ :=
  (lam i + ε) / (1 + ε * Fintype.card ι)

theorem probabilities_pos (lam : ι → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (ε : ℝ) (hε : 0 < ε) (i : ι) : 0 < probabilities lam ε i := by
  exact div_pos (add_pos_of_nonneg_of_pos (hlam i) hε)
    (by positivity)

theorem probabilities_sum (lam : ι → ℝ) (hlam : ∑ i, lam i = 1)
    (ε : ℝ) (hε : 0 < ε) : ∑ i, probabilities lam ε i = 1 := by
  unfold probabilities
  rw [← Finset.sum_div, Finset.sum_add_distrib, hlam]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [mul_comm (Fintype.card ι : ℝ) ε, div_self]
  positivity

theorem tendsto_weight_log (lam : ι → ℝ) (hlam : ∀ i, 0 ≤ lam i) (i : ι) :
    Tendsto (fun ε : ℝ => -lam i * Real.log (probabilities lam ε i)) (𝓝 0)
      (𝓝 (Real.negMulLog (lam i))) := by
  by_cases hz : lam i = 0
  · simp only [hz, neg_zero, zero_mul, Real.negMulLog_zero]
    exact tendsto_const_nhds
  · have hp : 0 < lam i := lt_of_le_of_ne (hlam i) (Ne.symm hz)
    have hd : ContinuousAt (fun ε : ℝ => probabilities lam ε i) 0 :=
      (continuousAt_const.add continuousAt_id).div
        (continuousAt_const.add (continuousAt_id.mul continuousAt_const)) (by norm_num)
    have hv : probabilities lam 0 i = lam i := by simp [probabilities]
    have hc : ContinuousAt (fun ε : ℝ => -lam i * Real.log (probabilities lam ε i)) 0 :=
      continuousAt_const.mul (hd.log (by rw [hv]; exact hz))
    simpa only [hv, Real.negMulLog_def, neg_mul] using hc.tendsto

end MarginalRegularization
end PolynomialPEPS.Subvolume

namespace PolynomialPEPS.Subvolume.PhysicalCurve
open scoped Matrix.Norms.L2Operator BigOperators ComplexOrder Topology
open PolynomialPEPS.Subvolume.SpectralCurve PolynomialPEPS.Subvolume.MarginalRegularization

theorem optimizer_cost_le_sum_entropy {L q : ℕ} (hq : 0 < q)
    (X : ℕ → Finset (Vertex L)) (hX : Monotone X)
    (a : ℕ → ℝ) (ha : ∀ j, 0 < a j)
    (ψ : State L q) (hψ : ‖ψ‖ = 1) (n : ℕ)
    (F : FilterFamily q n (fun j => X j.val))
    (hF : IsFilterOptimizer ψ (fun j => a j.val) F) :
    -Real.log (‖filteredVector F ψ‖ ^ 2) ≤
      ∑ j ∈ Finset.range n, a j * vonNeumannEntropy ψ (X j) := by
  let w := fun j => (reducedDensity_isHermitian ψ (X j)).eigenvalues
  let U := fun j => (reducedDensity_isHermitian ψ (X j)).eigenvectorUnitary
  have hw : ∀ j i, 0 ≤ w j i := fun j i =>
    (reducedDensity_posSemidef ψ (X j)).eigenvalues_nonneg i
  have hsum : ∀ j, ∑ i, w j i = 1 := fun j => marginal_eigenvalues_sum ψ hψ (X j)
  have hreg (ε : ℝ) (hε : 0 < ε) :
      -Real.log (‖filteredVector F ψ‖ ^ 2) ≤
        ∑ j ∈ Finset.range n, a j * ∑ i, -w j i * Real.log (probabilities (w j) ε i) := by
    have hp := fun j i => probabilities_pos (w j) (hw j) ε hε i
    have hs := fun j => probabilities_sum (w j) (hsum j) ε hε
    have h := optimizer_cost_le_trace_rates X U hq hX
      (fun j => probabilities (w j) ε) hp hs a ha ψ hψ n F hF
    simp only [Complex.re_sum, U, trace_rates_pairing] at h
    convert h using 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [powerRates, w]
    ring
  have hlim : Tendsto
      (fun ε : ℝ => ∑ j ∈ Finset.range n,
        a j * ∑ i, -w j i * Real.log (probabilities (w j) ε i))
      (𝓝 0) (𝓝 (∑ j ∈ Finset.range n, a j * vonNeumannEntropy ψ (X j))) := by
    apply tendsto_finsetSum
    intro j hj
    apply Filter.Tendsto.const_mul
    exact tendsto_finsetSum Finset.univ (fun i _ => tendsto_weight_log (w j) (hw j) i)
  apply le_of_tendsto_of_tendsto tendsto_const_nhds (hlim.mono_left nhdsWithin_le_nhds
    : Tendsto _ (𝓝[>] (0 : ℝ)) _)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hreg ε hε

end PolynomialPEPS.Subvolume.PhysicalCurve

namespace PolynomialPEPS.Subvolume.PhysicalCurve
open scoped Matrix.Norms.L2Operator BigOperators ComplexOrder Topology
open PolynomialPEPS.Subvolume.SpectralCurve PolynomialPEPS.Subvolume.MarginalRegularization
variable {L q : ℕ}
variable (X : ℕ → Finset (Vertex L))
  (U : (j : ℕ) → unitary (Matrix (RegionConfiguration q (X j))
    (RegionConfiguration q (X j)) ℂ))

theorem amplitude_right_of_bound (hq : 0 < q) (hX : Monotone X)
    (p : (j : ℕ) → RegionConfiguration q (X j) → ℝ)
    (hp : ∀ j i, 0 < p j i) (hsum : ∀ j, ∑ i, p j i = 1)
    (a : ℕ → ℝ) (ha : ∀ j, 0 < a j)
    (ψ : State L q) (n : ℕ)
    (N : ℝ) (hB : ∀ G : FilterFamily q n (fun j => X j.val),
      FilterFeasible (fun j => a j.val) G → ‖filteredVector G ψ‖ ≤ N)
    (z : ℂ) (hz : z.re = 1) :
    ‖amplitude X U (powerRates X p a) ψ n z‖ ≤ ‖ψ‖ * N := by
  let r := powerRates X p a
  let V : (j : ℕ) → unitary (Matrix (RegionConfiguration q (X j))
      (RegionConfiguration q (X j)) ℂ) := fun j =>
    ⟨curve (U j) (r j) (z-1), curve_mem_unitary (U j) (r j) (z-1) (by simp [hz])⟩
  let P : (j : ℕ) → Matrix (RegionConfiguration q (X j))
      (RegionConfiguration q (X j)) ℂ := fun j => curve (U j) (r j) 1
  have hP : ∀ j, (P j).PosSemidef := fun j => curve_posSemidef (U j) (r j) 1
  let G : (j : ℕ) → LocalPositiveFilter q (X j) := fun j =>
    ⟨gaugedMatrix hq X hX V P j, gaugedMatrix_posSemidef hq X hX V P hP j⟩
  have hG : FilterFeasible (fun j : Fin n => a j.val) (fun j : Fin n => G j.val) := by
    intro j
    change (∑ i, Real.rpow
      ((gaugedMatrix_posSemidef hq X hX V P hP j.val).isHermitian.eigenvalues i)
        (2 / a j.val)) = 1
    rw [gaugedMatrix_eigenvalues hq X hX V P hP j.val]
    exact tracePower_curve_one (U j.val) (p j.val) (hp j.val) (hsum j.val) (a j.val) (ha j.val)
  have heq (j : ℕ) : curve (U j) (r j) z = (V j : Matrix _ _ ℂ) * P j := by
    change curve (U j) (r j) z = curve (U j) (r j) (z-1) * curve (U j) (r j) 1
    rw [← curve_add, sub_add_cancel]
  have hv : ‖asMap (prefixCurve X U r n z) ψ‖ =
      ‖filteredVector (fun j : Fin n => G j.val) ψ‖ := by
    change ‖asMap (orderedPrefix (fun j => liftLocal (X j) (curve (U j) (r j) z)) n) ψ‖ = _
    simp_rw [heq]
    rw [norm_orderedPrefix_gauge hq X hX V P]
    change _ = ‖asMap (orderedFilterProduct (fun j : Fin n => G j.val)) ψ‖
    rw [orderedFilterProduct_eq_prefix]
  calc
    ‖amplitude X U r ψ n z‖ ≤ ‖ψ‖ * ‖asMap (prefixCurve X U r n z) ψ‖ :=
      norm_inner_le_norm (𝕜 := ℂ) ψ _
    _ = ‖ψ‖ * ‖filteredVector (fun j : Fin n => G j.val) ψ‖ := by rw [hv]
    _ ≤ ‖ψ‖ * N :=
      mul_le_mul_of_nonneg_left (hB _ hG) (norm_nonneg _)

include U in
theorem filter_bound_pos
    (p : (j : ℕ) → RegionConfiguration q (X j) → ℝ)
    (hp : ∀ j i, 0 < p j i) (hsum : ∀ j, ∑ i, p j i = 1)
    (a : ℕ → ℝ) (ha : ∀ j, 0 < a j)
    (ψ : State L q) (hψ : ‖ψ‖ = 1) (n : ℕ)
    (N : ℝ) (hB : ∀ G : FilterFamily q n (fun j => X j.val),
      FilterFeasible (fun j => a j.val) G → ‖filteredVector G ψ‖ ≤ N) :
    0 < N := by
  let r := powerRates X p a
  let G : (j : ℕ) → LocalPositiveFilter q (X j) := fun j =>
    ⟨curve (U j) (r j) 1, curve_posSemidef (U j) (r j) 1⟩
  have hG : FilterFeasible (fun j : Fin n => a j.val) (fun j : Fin n => G j.val) := by
    intro j
    exact tracePower_curve_one (U j.val) (p j.val) (hp j.val) (hsum j.val)
      (a j.val) (ha j.val)
  have hψ0 : ψ ≠ 0 := by
    intro hz
    simp only [hz, norm_zero] at hψ
    exact zero_ne_one hψ
  have hg : 0 < ‖filteredVector (fun j : Fin n => G j.val) ψ‖ := by
    unfold filteredVector
    rw [orderedFilterProduct_eq_prefix]
    exact norm_asMap_pos_of_isUnit (prefixCurve X U r n 1)
      (prefixCurve_isUnit X U r n 1) ψ hψ0
  exact hg.trans_le (hB _ hG)

theorem filter_bound_cost_le_trace_rates (hq : 0 < q) (hX : Monotone X)
    (p : (j : ℕ) → RegionConfiguration q (X j) → ℝ)
    (hp : ∀ j i, 0 < p j i) (hsum : ∀ j, ∑ i, p j i = 1)
    (a : ℕ → ℝ) (ha : ∀ j, 0 < a j)
    (ψ : State L q) (hψ : ‖ψ‖ = 1) (n : ℕ)
    (N : ℝ) (hB : ∀ G : FilterFamily q n (fun j => X j.val),
      FilterFeasible (fun j => a j.val) G → ‖filteredVector G ψ‖ ≤ N) :
    -Real.log (N ^ 2) ≤
      -2 * (∑ j ∈ Finset.range n, Matrix.trace
        (spectralHom (U j) (fun i => ((powerRates X p a j i) : ℂ)) *
          reducedDensity ψ (X j))).re := by
  let r := powerRates X p a
  have hpos := filter_bound_pos X U p hp hsum a ha ψ hψ n N hB
  have hstrip : BddAbove ((norm ∘ amplitude X U r ψ n) '' verticalClosedStrip 0 1) := by
    refine ⟨1, ?_⟩
    rintro b ⟨z,hz,rfl⟩
    exact amplitude_stripBound X U r (powerRates_nonpos X p hp hsum a ha)
      ψ hψ n z hz.1
  have hr : ∀ z ∈ re ⁻¹' {1}, ‖amplitude X U r ψ n z‖ ≤ N := by
    intro z hz
    have h := amplitude_right_of_bound X U hq hX p hp hsum a ha ψ n N hB z hz
    simpa only [hψ, one_mul] using h
  have h := FilterInterpolation.threeLines_tangent_zero hpos
    (amplitude_zero X U r ψ hψ n)
    (hasDerivAt_amplitude_zero X U r ψ n)
    (differentiable_amplitude X U r ψ n).diffContOnCl hstrip
    (fun z hz => amplitude_left X U r ψ hψ n z hz) hr
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith

end PolynomialPEPS.Subvolume.PhysicalCurve

namespace PolynomialPEPS.Subvolume.PhysicalCurve
open scoped Matrix.Norms.L2Operator BigOperators ComplexOrder Topology
open PolynomialPEPS.Subvolume.SpectralCurve PolynomialPEPS.Subvolume.MarginalRegularization

theorem filter_bound_cost_le_sum_entropy {L q : ℕ} (hq : 0 < q)
    (X : ℕ → Finset (Vertex L)) (hX : Monotone X)
    (a : ℕ → ℝ) (ha : ∀ j, 0 < a j)
    (ψ : State L q) (hψ : ‖ψ‖ = 1) (n : ℕ)
    (N : ℝ) (hB : ∀ G : FilterFamily q n (fun j => X j.val),
      FilterFeasible (fun j => a j.val) G → ‖filteredVector G ψ‖ ≤ N) :
    -Real.log (N ^ 2) ≤
      ∑ j ∈ Finset.range n, a j * vonNeumannEntropy ψ (X j) := by
  let w := fun j => (reducedDensity_isHermitian ψ (X j)).eigenvalues
  let U := fun j => (reducedDensity_isHermitian ψ (X j)).eigenvectorUnitary
  have hw : ∀ j i, 0 ≤ w j i := fun j i =>
    (reducedDensity_posSemidef ψ (X j)).eigenvalues_nonneg i
  have hsum : ∀ j, ∑ i, w j i = 1 := fun j => marginal_eigenvalues_sum ψ hψ (X j)
  have hreg (ε : ℝ) (hε : 0 < ε) :
      -Real.log (N ^ 2) ≤
        ∑ j ∈ Finset.range n, a j * ∑ i, -w j i * Real.log (probabilities (w j) ε i) := by
    have hp := fun j i => probabilities_pos (w j) (hw j) ε hε i
    have hs := fun j => probabilities_sum (w j) (hsum j) ε hε
    have h := filter_bound_cost_le_trace_rates X U hq hX
      (fun j => probabilities (w j) ε) hp hs a ha ψ hψ n N hB
    simp only [Complex.re_sum, U, trace_rates_pairing] at h
    convert h using 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [powerRates, w]
    ring
  have hlim : Tendsto
      (fun ε : ℝ => ∑ j ∈ Finset.range n,
        a j * ∑ i, -w j i * Real.log (probabilities (w j) ε i))
      (𝓝 0) (𝓝 (∑ j ∈ Finset.range n, a j * vonNeumannEntropy ψ (X j))) := by
    apply tendsto_finsetSum
    intro j hj
    apply Filter.Tendsto.const_mul
    exact tendsto_finsetSum Finset.univ (fun i _ => tendsto_weight_log (w j) (hw j) i)
  apply le_of_tendsto_of_tendsto tendsto_const_nhds (hlim.mono_left nhdsWithin_le_nhds
    : Tendsto _ (𝓝[>] (0 : ℝ)) _)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hreg ε hε

end PolynomialPEPS.Subvolume.PhysicalCurve

end

end OAI
