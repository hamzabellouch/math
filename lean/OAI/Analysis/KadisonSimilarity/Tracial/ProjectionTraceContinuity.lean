import OAI.Analysis.KadisonSimilarity.Representation.CountableProjectionJoin
import OAI.Analysis.KadisonSimilarity.Representation.MonotoneProjectionLimits

namespace OAI

/-! Small trace projections act strongly as zero. The argument uses
countable joins and geometric trace tails, rather than assuming normality
of a star isomorphism between concrete von Neumann algebras. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge Filter
open scoped ComplexOrder Topology

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

local instance projectionContinuity_closed (M : VonNeumannAlgebra H) :
    IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (M : Set (H →L[ℂ] H))
  infer_instance

/-- Decreasing projections with vanishing faithful trace converge strongly
to zero in the original concrete representation. -/
theorem antitone_projection_tendsto_zero
    (M : VonNeumannAlgebra H) (τ : M.toStarSubalgebra →ₚ[ℂ] ℂ)
    (hf : ∀ q, IsStarProjection q → (τ q).re = 0 → q = 0)
    (p : ℕ → M.toStarSubalgebra) (hp : ∀ n, IsStarProjection (p n))
    (hanti : ∀ i j, i ≤ j → p i * p j = p j)
    (ht : Tendsto (fun n => (τ (p n)).re) atTop (𝓝 0)) (x : H) :
    Tendsto (fun n => (p n : H →L[ℂ] H) x) atTop (𝓝 0) := by
  obtain ⟨q, hq, hlim, hbelow⟩ := exists_antitone_projection_limit M p hp hanti
  have hqle : (τ q).re ≤ 0 := ge_of_tendsto ht
    (Eventually.of_forall fun n => trace_projection_le τ q (p n) hq (hp n) (hbelow n))
  have hqge : 0 ≤ (τ q).re := (τ.map_nonneg hq.nonneg).1
  have hzero := hf q hq (le_antisymm hqle hqge)
  simpa only [hzero, ZeroMemClass.coe_zero, zero_apply] using hlim x

/-- A sequence of projections with a geometric trace bound acts strongly
as zero, even in a different faithful concrete normal model. -/
theorem geometric_projection_tendsto_zero
    (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K)
    [IsClosed (N.toStarSubalgebra : Set (K →L[ℂ] K))]
    (e : M.toStarSubalgebra ≃⋆ₐ[ℂ] N.toStarSubalgebra)
    (υ : TracialRepresentation N)
    (τ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (σ : N.toStarSubalgebra →ₚ[ℂ] ℂ)
    (hσ : ∀ b, σ b = υ.trace b) (he : ∀ a, σ (e a) = τ a)
    (hf : ∀ q, IsStarProjection q → (τ q).re = 0 → q = 0)
    (p : ℕ → M.toStarSubalgebra) (hp : ∀ n, IsStarProjection (p n))
    (hpt : ∀ n, (τ (p n)).re ≤ (1 / 2 : ℝ) ^ n) (x : H) :
    Tendsto (fun n => (p n : H →L[ℂ] H) x) atTop (𝓝 0) := by
  classical
  have htail (m n : ℕ) :
      ∑ i ∈ Finset.range n, (τ (p (m + i))).re ≤ 2 * (1 / 2 : ℝ) ^ m := by
    calc
      _ ≤ ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ (m + i) :=
        Finset.sum_le_sum (fun i _ => hpt (m + i))
      _ = (1 / 2 : ℝ) ^ m * ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ i := by
        simp only [pow_add, Finset.mul_sum]
      _ ≤ (1 / 2 : ℝ) ^ m * 2 :=
        mul_le_mul_of_nonneg_left (sum_geometric_two_le n) (by positivity)
      _ = 2 * (1 / 2 : ℝ) ^ m := mul_comm _ _
  have hex (m : ℕ) := exists_countable_projection_join_of_equiv M N e υ τ σ hσ he
    (fun i => p (m + i)) (fun i => hp (m + i)) (2 * (1 / 2 : ℝ) ^ m) (htail m)
  choose q hq hqt hqp hleast using hex
  have hanti (m n : ℕ) (hmn : m ≤ n) : q m * q n = q n := by
    apply hleast n (q m) (hq m)
    intro i
    have hidx : m + (n - m + i) = n + i := by omega
    simpa only [hidx] using hqp m (n - m + i)
  have htrace : Tendsto (fun n => (τ (q n)).re) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => (τ.map_nonneg (hq n).nonneg).1) hqt
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul 2
  have hqzero := antitone_projection_tendsto_zero M τ hf q hq hanti htrace x
  have hnorm (n : ℕ) : ‖(p n : H →L[ℂ] H) x‖ ≤ ‖(q n : H →L[ℂ] H) x‖ := by
    have hqp' : q n * p n = p n := by simpa only [Nat.add_zero] using hqp n 0
    have hpq : p n * q n = p n := by
      simpa only [star_mul, (hp n).isSelfAdjoint.star_eq, (hq n).isSelfAdjoint.star_eq]
        using congrArg star hqp'
    calc
      _ = ‖(p n : H →L[ℂ] H) ((q n : H →L[ℂ] H) x)‖ :=
        congrArg norm (congrArg (fun a : M.toStarSubalgebra => (a : H →L[ℂ] H) x) hpq).symm
      _ ≤ ‖(p n : H →L[ℂ] H)‖ * ‖(q n : H →L[ℂ] H) x‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖(q n : H →L[ℂ] H) x‖ :=
        mul_le_mul_of_nonneg_right ((hp n).map M.toStarSubalgebra.subtype).norm_le (norm_nonneg _)
      _ = ‖(q n : H →L[ℂ] H) x‖ := one_mul _
  exact squeeze_zero_norm hnorm (by simpa using hqzero.norm)

/-- Vanishing trace of arbitrary projections forces strong convergence to
zero. A hypothetical fixed violation supplies a geometric-trace sequence,
which contradicts the preceding countable-join argument. -/
theorem projection_tendsto_zero_of_trace_tendsto_zero
    (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K)
    [IsClosed (N.toStarSubalgebra : Set (K →L[ℂ] K))]
    (e : M.toStarSubalgebra ≃⋆ₐ[ℂ] N.toStarSubalgebra)
    (υ : TracialRepresentation N)
    (τ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (σ : N.toStarSubalgebra →ₚ[ℂ] ℂ)
    (hσ : ∀ b, σ b = υ.trace b) (he : ∀ a, σ (e a) = τ a)
    (hf : ∀ q, IsStarProjection q → (τ q).re = 0 → q = 0)
    (p : ℕ → M.toStarSubalgebra) (hp : ∀ n, IsStarProjection (p n))
    (ht : Tendsto (fun n => (τ (p n)).re) atTop (𝓝 0)) (x : H) :
    Tendsto (fun n => (p n : H →L[ℂ] H) x) atTop (𝓝 0) := by
  classical
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  simp only [dist_zero_right]
  by_contra! hbad
  have hex (i : ℕ) : ∃ n, (τ (p n)).re ≤ (1 / 2 : ℝ) ^ i ∧
      ε ≤ ‖(p n : H →L[ℂ] H) x‖ := by
    have hevent : ∀ᶠ n in atTop, (τ (p n)).re < (1 / 2 : ℝ) ^ i :=
      ht (Iio_mem_nhds (by positivity))
    obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
    obtain ⟨n, hn, hnx⟩ := hbad N
    exact ⟨n, (hN n hn).le, hnx⟩
  choose f hft hfx using hex
  have hz := geometric_projection_tendsto_zero M N e υ τ σ hσ he hf
    (fun i => p (f i)) (fun i => hp (f i)) hft x
  obtain ⟨n, hn⟩ := Metric.tendsto_atTop.mp hz ε hε
  have hsmall := hn n le_rfl
  rw [dist_zero_right] at hsmall
  exact (not_lt_of_ge (hfx n)) hsmall

end KadisonSimilarity

end

end OAI
