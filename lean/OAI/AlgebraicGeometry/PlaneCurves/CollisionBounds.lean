import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

namespace OAI

/-!
# Coefficient convergence, collision estimates, and compactness
-/

section

/-! Coefficient convergence for a fixed finite family of local scalar section
expressions. This supplies the uniform-convergence part of the fixed-τ
compactness argument independently of how those section expressions are built. -/

namespace Nagata.W20

open Filter Metric
open scoped Topology BigOperators

variable {R : Type*} [NormedRing R]

/-- Finite coefficient convergence is uniform wherever all basis functions
have fixed uniform bounds. -/
theorem uniform_linear_combination_of_bounds {ι X : Type*} [Fintype ι]
    (K : Set X) (b : ι → X → R) (B : ι → ℝ)
    (hB : ∀ i z, z ∈ K → ‖b i z‖ ≤ B i)
    (c : ℕ → ι → R) (c₀ : ι → R)
    (hc : ∀ i, Tendsto (fun n => c n i) atTop (𝓝 (c₀ i))) :
    TendstoUniformlyOn (fun n z => ∑ i, c n i * b i z)
      (fun z => ∑ i, c₀ i * b i z) atTop K := by
  classical
  have herr : Tendsto (fun n => ∑ i, ‖c n i - c₀ i‖ * B i) atTop (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.univ : Finset ι) (fun i _ =>
      ((hc i).sub (tendsto_const_nhds (x := c₀ i))).norm.mul (tendsto_const_nhds (x := B i)))
    simpa only [sub_self, norm_zero, zero_mul, Finset.sum_const_zero] using h
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [herr.eventually_lt_const hε] with n hn
  intro z hz
  calc
    dist (∑ i, c₀ i * b i z) (∑ i, c n i * b i z)
        = ‖∑ i, (c n i - c₀ i) * b i z‖ := by
            rw [dist_comm, dist_eq_norm, ← Finset.sum_sub_distrib]
            simp only [sub_mul]
    _ ≤ ∑ i, ‖(c n i - c₀ i) * b i z‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖c n i - c₀ i‖ * ‖b i z‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact norm_mul_le _ _
    _ ≤ ∑ i, ‖c n i - c₀ i‖ * B i := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hB i z hz) (norm_nonneg _)
    _ < ε := hn

/-- On a compact set, continuity of the finitely many fixed basis functions
supplies the required bounds. -/
theorem uniform_linear_combination_on_compact {ι X : Type*} [Fintype ι]
    [TopologicalSpace X] (K : Set X) (hK : IsCompact K)
    (b : ι → X → R) (hb : ∀ i, ContinuousOn (b i) K)
    (c : ℕ → ι → R) (c₀ : ι → R)
    (hc : ∀ i, Tendsto (fun n => c n i) atTop (𝓝 (c₀ i))) :
    TendstoUniformlyOn (fun n z => ∑ i, c n i * b i z)
      (fun z => ∑ i, c₀ i * b i z) atTop K := by
  classical
  have hbounds := fun i => hK.exists_bound_of_continuousOn (hb i)
  let B : ι → ℝ := fun i => Classical.choose (hbounds i)
  apply uniform_linear_combination_of_bounds K b B
  · intro i z hz
    exact Classical.choose_spec (hbounds i) z hz
  · exact hc

/-- For a finite holomorphic (or merely continuous) local basis on an open
complex domain, coefficient convergence gives locally uniform convergence. -/
theorem locally_uniform_linear_combination {ι X : Type*} [Fintype ι]
    [TopologicalSpace X] [LocallyCompactSpace X]
    {U : Set X} (hU : IsOpen U) (b : ι → X → R)
    (hb : ∀ i, ContinuousOn (b i) U)
    (c : ℕ → ι → R) (c₀ : ι → R)
    (hc : ∀ i, Tendsto (fun n => c n i) atTop (𝓝 (c₀ i))) :
    TendstoLocallyUniformlyOn (fun n z => ∑ i, c n i * b i z)
      (fun z => ∑ i, c₀ i * b i z) atTop U := by
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mpr
  intro K hKU hK
  exact uniform_linear_combination_on_compact K hK b (fun i => (hb i).mono hKU) c c₀ hc

end Nagata.W20

end

section

namespace Nagata.W20

open Filter
open scoped Topology

/-- Unit coefficient vectors have a subsequence with a nonzero unit limit.
The `ProperSpace` instance is supplied by finite dimensionality over ℝ or ℂ. -/
theorem unit_subsequence {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    (v : ℕ → E) (hv : ∀ n, ‖v n‖ = 1) :
    ∃ a : E, ‖a‖ = 1 ∧ a ≠ 0 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (v ∘ φ) atTop (𝓝 a) := by
  obtain ⟨a, ha, φ, hφ, hlim⟩ :=
    (isCompact_sphere (0 : E) 1).tendsto_subseq (fun n => by
      simpa only [Metric.mem_sphere, dist_zero_right] using hv n)
  have hnorm : ‖a‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using ha
  refine ⟨a, hnorm, ?_, φ, hφ, hlim⟩
  intro ha0
  simp [ha0] at hnorm

/-- A fixed continuous map which vanishes on a convergent sequence vanishes
at the limit. This applies to each fixed finite-dimensional jet functional. -/
theorem continuous_zero_at_limit {E F : Type*}
    [TopologicalSpace E] [TopologicalSpace F] [T2Space F] [Zero F]
    (f : E → F) (hf : Continuous f) (v : ℕ → E) (a : E)
    (hv : Tendsto v atTop (𝓝 a)) (hzero : ∀ n, f (v n) = 0) : f a = 0 := by
  have hlim : Tendsto (f ∘ v) atTop (𝓝 (f a)) := (hf.tendsto a).comp hv
  have hz : f ∘ v = fun _ => 0 := funext hzero
  rw [hz] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

/-- Compactness and continuity preserve a nontrivial kernel witness. The map
is fixed: varying jet centers require the separate analytic collision bridge. -/
theorem nonzero_kernel_limit {E F : Type*} [NormedAddCommGroup E] [ProperSpace E]
    [TopologicalSpace F] [T2Space F] [Zero F]
    (f : E → F) (hf : Continuous f)
    (v : ℕ → E) (hv : ∀ n, ‖v n‖ = 1) (hz : ∀ n, f (v n) = 0) :
    ∃ a : E, ‖a‖ = 1 ∧ a ≠ 0 ∧ f a = 0 := by
  obtain ⟨a, ha, ha0, φ, _, hlim⟩ := unit_subsequence v hv
  exact ⟨a, ha, ha0, continuous_zero_at_limit f hf (v ∘ φ) a hlim
    (fun n => hz (φ n))⟩

end Nagata.W20

end

section

namespace Nagata.W20
open Filter Metric
open scoped Topology BigOperators
variable {𝕜 : Type*} [NormedField 𝕜]

/-- A point in the half disk stays at least half a radius from its boundary. -/
theorem boundary_distance_lower {z ξ : 𝕜} {r : ℝ}
    (hz : ‖z‖ = r) (hξ : ‖ξ‖ ≤ r / 2) : r / 2 ≤ ‖z - ξ‖ := by
  have h := norm_sub_norm_le z ξ
  linarith

/-- Uniform lower bound on the collision divisor along the boundary circle. -/
theorem collision_product_boundary_lower {ι : Type*} [Fintype ι]
    (ξ : ι → 𝕜) (k : ℕ) {r : ℝ} (hr : 0 < r)
    (hξ : ∀ i, ‖ξ i‖ ≤ r / 2) {z : 𝕜} (hz : ‖z‖ = r) :
    (r / 2) ^ (k * Fintype.card ι) ≤ ‖∏ i, (z - ξ i) ^ k‖ := by
  classical
  rw [norm_prod]
  have hp : (∏ _i : ι, (r / 2) ^ k) ≤ ∏ i : ι, ‖(z - ξ i) ^ k‖ := by
    apply Finset.prod_le_prod₀
    · intro i _
      exact pow_nonneg (by positivity) k
    · intro i _
      rw [norm_pow]
      exact pow_le_pow_left₀ (by positivity) (boundary_distance_lower hz (hξ i)) k
  simpa only [Finset.prod_const, Finset.card_univ, ← pow_mul] using hp

/-- The explicit collision factors converge to the expected power, with
exponent equal to the sum of the multiplicities of all factors. -/
theorem collision_product_tendsto {ι : Type*} [Fintype ι]
    (ξ : ℕ → ι → 𝕜) (k : ℕ) (hξ : ∀ i, Tendsto (fun n => ξ n i) atTop (𝓝 0))
    (z : 𝕜) :
    Tendsto (fun n => ∏ i, (z - ξ n i) ^ k) atTop
      (𝓝 (z ^ (k * Fintype.card ι))) := by
  classical
  have hp := tendsto_finsetProd (Finset.univ : Finset ι)
    (fun i _ => ((tendsto_const_nhds (x := z)).sub (hξ i)).pow k)
  simpa only [sub_zero, Finset.prod_const, Finset.card_univ, ← pow_mul] using hp

/-- Bounded holomorphic quotients are enough for the quantitative collision
estimate; convergence of the quotients themselves is unnecessary. This lemma
is pointwise and its quotient bound is supplied by the maximum modulus lemma. -/
theorem collision_limit_growth {ι : Type*} [Fintype ι]
    (ξ : ℕ → ι → 𝕜) (k : ℕ) (hξ : ∀ i, Tendsto (fun n => ξ n i) atTop (𝓝 0))
    (H G : ℕ → 𝕜 → 𝕜) (f : 𝕜 → 𝕜) (z : 𝕜) (C : ℝ)
    (hlim : Tendsto (fun n => H n z) atTop (𝓝 (f z)))
    (hfactor : ∀ n, H n z = (∏ i, (z - ξ n i) ^ k) * G n z)
    (hbound : ∀ n, ‖G n z‖ ≤ C) :
    ‖f z‖ ≤ ‖z‖ ^ (k * Fintype.card ι) * C := by
  have hp := (collision_product_tendsto ξ k hξ z).norm.mul
    (tendsto_const_nhds (x := C))
  apply le_of_tendsto_of_tendsto' hlim.norm (by simpa only [norm_pow] using hp)
  intro n
  rw [hfactor n, norm_mul]
  exact mul_le_mul_of_nonneg_left (hbound n) (norm_nonneg _)

/-- Version of the collision growth estimate allowing a finite initial
segment to be discarded, as required by locally uniform convergence. -/
theorem collision_limit_growth_eventually {ι : Type*} [Fintype ι]
    (ξ : ℕ → ι → 𝕜) (k : ℕ) (hξ : ∀ i, Tendsto (fun n => ξ n i) atTop (𝓝 0))
    (H G : ℕ → 𝕜 → 𝕜) (f : 𝕜 → 𝕜) (z : 𝕜) (C : ℝ)
    (hlim : Tendsto (fun n => H n z) atTop (𝓝 (f z)))
    (hfactor : ∀ n, H n z = (∏ i, (z - ξ n i) ^ k) * G n z)
    (hbound : ∀ᶠ n in atTop, ‖G n z‖ ≤ C) :
    ‖f z‖ ≤ ‖z‖ ^ (k * Fintype.card ι) * C := by
  have hp := (collision_product_tendsto ξ k hξ z).norm.mul
    (tendsto_const_nhds (x := C))
  apply le_of_tendsto_of_tendsto hlim.norm (by simpa only [norm_pow] using hp)
  filter_upwards [hbound] with n hn
  rw [hfactor n, norm_mul]
  exact mul_le_mul_of_nonneg_left hn (norm_nonneg _)

end Nagata.W20

end

section

/-! Explicit distinct configurations approaching the origin inside any prescribed
open neighborhood. All choices are made at a fixed parameter value. -/

namespace Nagata.W20
open Filter Metric
open scoped Topology

/-- Distinct real points in the complex disk, scaled to zero. -/
noncomputable def collisionCenters (q : ℕ) (r : ℝ) (n : ℕ) (i : Fin q) : ℂ :=
  ((r * (i.val : ℝ) / ((q + 1 : ℝ) * (n + 1 : ℝ)) : ℝ) : ℂ)

theorem collisionCenters_injective (q : ℕ) {r : ℝ} (hr : 0 < r) (n : ℕ) :
    Function.Injective (collisionCenters q r n) := by
  intro i j hij
  apply Fin.ext
  apply Nat.cast_injective (R := ℝ)
  have heq : r * (i.val : ℝ) / ((q + 1 : ℝ) * (n + 1 : ℝ)) =
      r * (j.val : ℝ) / ((q + 1 : ℝ) * (n + 1 : ℝ)) :=
    Complex.ofReal_injective hij
  have hd : ((q + 1 : ℝ) * (n + 1 : ℝ)) ≠ 0 := by positivity
  exact mul_left_cancel₀ (ne_of_gt hr) ((div_left_inj' hd).mp heq)

theorem collisionCenters_mem_ball (q : ℕ) {r : ℝ} (hr : 0 < r)
    (n : ℕ) (i : Fin q) : collisionCenters q r n i ∈ ball 0 r := by
  have hi : (i.val : ℝ) < q + 1 := by exact_mod_cast Nat.lt_succ_of_lt i.isLt
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hd : (0 : ℝ) < (q + 1) * (n + 1) := by positivity
  have hir : (i.val : ℝ) < (q + 1 : ℝ) * (n + 1 : ℝ) := by nlinarith
  have hnonneg : 0 ≤ r * (i.val : ℝ) / ((q + 1 : ℝ) * (n + 1 : ℝ)) := by positivity
  simp only [Metric.mem_ball, dist_zero_right, collisionCenters, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact (div_lt_iff₀ hd).mpr (mul_lt_mul_of_pos_left hir hr)

theorem collisionCenters_tendsto (q : ℕ) (r : ℝ) (i : Fin q) :
    Tendsto (fun n => collisionCenters q r n i) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => (r * (i.val : ℝ) / (q + 1 : ℝ)) *
      (1 / (n + 1 : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := r * (i.val : ℝ) / (q + 1 : ℝ))).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp h
  simpa [collisionCenters, div_mul_eq_div_mul_one_div, Function.comp_def] using hc

/-- Every open neighborhood of zero admits one sequence of injective q-tuples,
all lying in the neighborhood, with every point converging to zero. -/
theorem exists_collision_centers {U : Set ℂ} (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U)
    (q : ℕ) : ∃ ξ : ℕ → Fin q → ℂ,
      (∀ n, Function.Injective (ξ n)) ∧ (∀ n i, ξ n i ∈ U) ∧
      (∀ i, Tendsto (fun n => ξ n i) atTop (𝓝 0)) := by
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0)
  exact ⟨collisionCenters q r, collisionCenters_injective q hr,
    fun n i => hsub (collisionCenters_mem_ball q hr n i), collisionCenters_tendsto q r⟩

end Nagata.W20

end

section

/-! A quantitative replacement for the zero-count portion of Rouché's theorem:
a power growth bound on a holomorphic function forces the corresponding order
of vanishing, by extending its bounded quotient across the origin. -/

namespace Nagata.W20

open Filter Metric Set
open scoped Topology

/-- A holomorphic function bounded by C |z|^N has vanishing order at least N.
The proof uses the actual removable-singularity theorem, not an order axiom. -/
theorem analyticOrderAt_lower_of_growth (f : ℂ → ℂ) (N : ℕ) {r C : ℝ}
    (hr : 0 < r) (hf : DifferentiableOn ℂ f (ball 0 r))
    (hbound : ∀ z ∈ ball (0 : ℂ) r, ‖f z‖ ≤ ‖z‖ ^ N * C) :
    (N : ℕ∞) ≤ analyticOrderAt f 0 := by
  by_cases hN : N = 0
  · simp [hN]
  let Q : ℂ → ℂ := fun z => f z / z ^ N
  have hQdiff : DifferentiableOn ℂ Q (ball 0 r \ {0}) := by
    apply (hf.mono sdiff_subset).div (differentiableOn_id.pow N)
    intro z hz
    exact pow_ne_zero N hz.2
  have hQbound : BddAbove ((norm ∘ Q) '' (ball 0 r \ {0})) := by
    refine ⟨C, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    change ‖f z / z ^ N‖ ≤ C
    rw [norm_div, norm_pow]
    apply (div_le_iff₀ (pow_pos (norm_pos_iff.mpr hz.2) N)).mpr
    simpa only [mul_comm] using hbound z hz.1
  let G := Function.update Q 0 (limUnder (𝓝[≠] (0 : ℂ)) Q)
  have hG : DifferentiableOn ℂ G (ball 0 r) :=
    Complex.differentiableOn_update_limUnder_of_bddAbove (ball_mem_nhds _ hr)
      hQdiff hQbound
  apply (natCast_le_analyticOrderAt (hf.analyticAt (ball_mem_nhds _ hr))).mpr
  refine ⟨G, hG.analyticAt (ball_mem_nhds _ hr), ?_⟩
  filter_upwards [ball_mem_nhds (0 : ℂ) hr] with z hz
  by_cases hz0 : z = 0
  · subst z
    have hf0 : f 0 = 0 := by
      have h := hbound 0 (mem_ball_self hr)
      simpa [zero_pow hN] using h
    simp [hf0, zero_pow hN]
  · change f z = (z - 0) ^ N • Function.update Q 0 (limUnder (𝓝[≠] (0 : ℂ)) Q) z
    rw [Function.update_of_ne hz0, sub_zero, smul_eq_mul]
    change f z = z ^ N * (f z / z ^ N)
    rw [mul_comm, div_mul_cancel₀ _ (pow_ne_zero N hz0)]

/-- The same growth estimate expressed in the derivative form used by the
collision jet matrix. -/
theorem iteratedDeriv_zero_of_growth (f : ℂ → ℂ) (N : ℕ) {r C : ℝ}
    (hr : 0 < r) (hf : DifferentiableOn ℂ f (ball 0 r))
    (hbound : ∀ z ∈ ball (0 : ℂ) r, ‖f z‖ ≤ ‖z‖ ^ N * C) :
    ∀ ℓ < N, iteratedDeriv ℓ f 0 = 0 :=
  (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
    (hf.analyticAt (ball_mem_nhds _ hr))).mp
      (analyticOrderAt_lower_of_growth f N hr hf hbound)

end Nagata.W20

end

section

namespace Nagata.W20

open Filter Metric
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E]

/-- Uniform convergence on a compact set gives one bound for all sufficiently
late functions, by bounding the limit and taking uniform error at most one. -/
theorem eventual_uniform_bound_on_compact {X : Type*} [TopologicalSpace X]
    (K : Set X) (hK : IsCompact K) (H : ℕ → X → E) (f : X → E)
    (hf : ContinuousOn f K) (hlim : TendstoUniformlyOn H f atTop K) :
    ∃ M : ℝ, ∀ᶠ n in atTop, ∀ z ∈ K, ‖H n z‖ ≤ M := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hf
  refine ⟨M + 1, ?_⟩
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hlim) 1 zero_lt_one] with n hn
  intro z hz
  apply (norm_le_norm_add_norm_sub (f z) (H n z)).trans
  apply add_le_add (hM z hz)
  exact le_of_lt (by simpa only [dist_eq_norm] using hn z hz)

/-- Finitely many centers converging to zero eventually all belong to the
same half disk. No uniformity in an infinite index set is presumed. -/
theorem centers_eventually_half_disk {ι : Type*} [Finite ι]
    (ξ : ℕ → ι → E) (hξ : ∀ i, Tendsto (fun n => ξ n i) atTop (𝓝 0))
    {r : ℝ} (hr : 0 < r) :
    ∀ᶠ n in atTop, ∀ i, ‖ξ n i‖ ≤ r / 2 := by
  apply Filter.eventually_all.mpr
  intro i
  filter_upwards [(hξ i).eventually (ball_mem_nhds (0 : E) (half_pos hr))] with n hn
  exact le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using hn)

end Nagata.W20

end

section

namespace Nagata.W20
open Filter Metric
open scoped Topology BigOperators

/-- Maximum-modulus quotient estimate. If f=P*g on the boundary, P is
bounded away from zero there, and the actual quotient g is holomorphic inside,
then g is uniformly bounded on the whole closed disk. -/
theorem quotient_bound_on_closedBall (f P g : ℂ → ℂ) {r a M : ℝ}
    (hr : 0 < r) (ha : 0 < a)
    (hg : DiffContOnCl ℂ g (ball 0 r))
    (hfactor : ∀ z ∈ sphere (0 : ℂ) r, f z = P z * g z)
    (hlower : ∀ z ∈ sphere (0 : ℂ) r, a ≤ ‖P z‖)
    (hupper : ∀ z ∈ sphere (0 : ℂ) r, ‖f z‖ ≤ M)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) r) : ‖g z‖ ≤ M / a := by
  apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hg
  · intro w hw
    have hws : w ∈ sphere (0 : ℂ) r := by
      simpa only [frontier_ball (0 : ℂ) hr.ne'] using hw
    apply (le_div_iff₀ ha).mpr
    calc
      ‖g w‖ * a ≤ ‖g w‖ * ‖P w‖ :=
        mul_le_mul_of_nonneg_left (hlower w hws) (norm_nonneg _)
      _ = ‖f w‖ := by rw [hfactor w hws, norm_mul, mul_comm]
      _ ≤ M := hupper w hws
  · simpa only [closure_ball (0 : ℂ) hr.ne'] using hz

end Nagata.W20

end

end OAI
