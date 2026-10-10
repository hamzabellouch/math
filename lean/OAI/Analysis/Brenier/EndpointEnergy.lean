import Mathlib

namespace OAI

/-! Bounded intercept speeds give finite endpoint values in the moving-site argument. -/

noncomputable section
open Set Filter
open scoped Topology BigOperators NNReal

namespace Problem358

/-- A differentiable intercept with uniformly bounded speed is Lipschitz on its
open parameter interval. No value or continuity at either endpoint is assumed. -/
theorem intercept_lipschitzOn {a b : ℝ} {c c' : ℝ → ℝ} {L : ℝ≥0}
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt c (c' t) t)
    (hbound : ∀ t ∈ Ioo a b, |c' t| ≤ L) :
    LipschitzOnWith L c (Ioo a b) := by
  apply (convex_Ioo a b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun t ht => (hderiv t ht).hasDerivWithinAt)
  intro t ht
  exact_mod_cast (show ‖c' t‖ ≤ (L : ℝ) by simpa only [Real.norm_eq_abs] using hbound t ht)

/-- An intercept with bounded speed admits a globally Lipschitz extension from
the open parameter interval. This is used only for endpoint existence. -/
theorem exists_intercept_extension {a b : ℝ} {c c' : ℝ → ℝ} {L : ℝ≥0}
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt c (c' t) t)
    (hbound : ∀ t ∈ Ioo a b, |c' t| ≤ L) :
    ∃ g : ℝ → ℝ, LipschitzWith L g ∧ EqOn c g (Ioo a b) :=
  (intercept_lipschitzOn hderiv hbound).extend_real

/-- The original intercept tends to the values of any continuous extension at
both endpoints, from inside the parameter interval. -/
theorem intercept_endpoint_limits {a b : ℝ} (hab : a < b) {c g : ℝ → ℝ}
    (hg : Continuous g) (hcg : EqOn c g (Ioo a b)) :
    Tendsto c (𝓝[>] a) (𝓝 (g a)) ∧ Tendsto c (𝓝[<] b) (𝓝 (g b)) := by
  have hlimit (x : ℝ) : Tendsto c (𝓝[Ioo a b] x) (𝓝 (g x)) := by
    apply Filter.Tendsto.congr' _ ((hg.tendsto x).mono_left nhdsWithin_le_nhds)
    filter_upwards [eventually_mem_nhdsWithin] with t ht
    exact (hcg ht).symm
  constructor
  · simpa only [nhdsWithin_Ioo_eq_nhdsGT hab] using hlimit a
  · simpa only [nhdsWithin_Ioo_eq_nhdsLT hab] using hlimit b

/-- Finite one-sided endpoint limits follow directly from the derivative bound. -/
theorem exists_intercept_endpoint_limits {a b : ℝ} (hab : a < b)
    {c c' : ℝ → ℝ} {L : ℝ≥0}
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt c (c' t) t)
    (hbound : ∀ t ∈ Ioo a b, |c' t| ≤ L) :
    ∃ ca cb : ℝ, Tendsto c (𝓝[>] a) (𝓝 ca) ∧
      Tendsto c (𝓝[<] b) (𝓝 cb) ∧ |cb - ca| ≤ L * (b - a) := by
  obtain ⟨g, hg, hcg⟩ := exists_intercept_extension hderiv hbound
  obtain ⟨ha, hb⟩ := intercept_endpoint_limits hab hg.continuous hcg
  refine ⟨g a, g b, ha, hb, ?_⟩
  simpa only [Real.dist_eq, abs_of_pos (sub_pos.mpr hab)] using hg.dist_le_mul b a

/-- The extensions can be chosen simultaneously for a finite family of intercepts. -/
theorem exists_finite_intercept_extensions {ι : Type*} {a b : ℝ}
    {c c' : ι → ℝ → ℝ} {L : ι → ℝ≥0}
    (hderiv : ∀ i t, t ∈ Ioo a b → HasDerivAt (c i) (c' i t) t)
    (hbound : ∀ i t, t ∈ Ioo a b → |c' i t| ≤ L i) :
    ∃ g : ι → ℝ → ℝ, ∀ i, LipschitzWith (L i) (g i) ∧ EqOn (c i) (g i) (Ioo a b) := by
  exact Classical.axiomOfChoice fun i => exists_intercept_extension (hderiv i) (hbound i)

/-- Weighted normalization on the interior persists at both endpoints of a
continuous family. This avoids any mass-dependent endpoint estimate. -/
theorem intercept_normalization_closed {ι : Type*} [Fintype ι]
    {a b : ℝ} (hab : a < b) (m : ι → ℝ) {g : ι → ℝ → ℝ}
    (hg : ∀ i, Continuous (g i))
    (hnorm : ∀ t ∈ Ioo a b, ∑ i, m i * g i t = 0) :
    ∀ t ∈ Icc a b, ∑ i, m i * g i t = 0 := by
  have heq : EqOn (fun t => ∑ i, m i * g i t) (fun _ => (0 : ℝ)) (Ioo a b) := hnorm
  have hc : Continuous (fun t => ∑ i, m i * g i t) := by fun_prop
  have hclosed := heq.closure hc continuous_const
  intro t ht
  exact hclosed (by simpa only [closure_Ioo hab.ne] using ht)

end Problem358

end

noncomputable section

open Set Filter
open scoped BigOperators Topology NNReal

namespace Problem358
namespace InterceptEndpointExtension

/-- A positive weighted quadratic-energy bound controls every coordinate.
The mass dependence is used only to construct endpoint intercepts. -/
theorem abs_le_sqrt_energy_div_mass
    {ι : Type*} [Fintype ι] (m r : ι → ℝ) {energy : ℝ}
    (hm : ∀ i, 0 < m i)
    (henergy : (∑ i, m i * r i ^ 2) ≤ energy) (i : ι) :
    |r i| ≤ Real.sqrt (energy / m i) := by
  classical
  have hsingle : m i * r i ^ 2 ≤ energy :=
    (Finset.single_le_sum
      (fun j _ => mul_nonneg (hm j).le (sq_nonneg (r j)))
      (Finset.mem_univ i)).trans henergy
  have hsquare : r i ^ 2 ≤ energy / m i := by
    apply (le_div_iff₀ (hm i)).mpr
    simpa only [mul_comm] using hsingle
  simpa only [Real.sqrt_sq_eq_abs] using Real.sqrt_le_sqrt hsquare

/-- Intercept derivatives with a uniform weighted energy bound give a
coordinatewise Lipschitz estimate on the entire open time interval. -/
theorem lipschitzOnWith_of_weighted_derivative_energy
    {ι : Type*} [Fintype ι] (m : ι → ℝ) (c r : ι → ℝ → ℝ)
    {a b energy : ℝ} (hm : ∀ i, 0 < m i)
    (hderiv : ∀ i t, t ∈ Ioo a b → HasDerivAt (c i) (r i t) t)
    (henergy : ∀ t ∈ Ioo a b, (∑ i, m i * r i t ^ 2) ≤ energy)
    (i : ι) :
    LipschitzOnWith ⟨Real.sqrt (energy / m i), Real.sqrt_nonneg _⟩ (c i) (Ioo a b) := by
  apply (convex_Ioo a b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun t ht => (hderiv i t ht).hasDerivWithinAt)
  intro t ht
  change ‖r i t‖ ≤ Real.sqrt (energy / m i)
  simpa only [Real.norm_eq_abs] using
    abs_le_sqrt_energy_div_mass m (fun j => r j t) hm (henergy t ht) i

/-- A fixed-mass intercept path with bounded weighted derivative energy has
continuous endpoint values.  The extension agrees on the interior and has the
same interior derivatives.  No separation of endpoint sites is required. -/
theorem exists_lipschitz_extension
    {ι : Type*} [Fintype ι] (m : ι → ℝ) (c r : ι → ℝ → ℝ)
    {a b energy : ℝ} (hm : ∀ i, 0 < m i)
    (hderiv : ∀ i t, t ∈ Ioo a b → HasDerivAt (c i) (r i t) t)
    (henergy : ∀ t ∈ Ioo a b, (∑ i, m i * r i t ^ 2) ≤ energy) :
    ∃ C : ι → ℝ → ℝ,
      (∀ i, LipschitzWith ⟨Real.sqrt (energy / m i), Real.sqrt_nonneg _⟩ (C i)) ∧
      (∀ i, EqOn (c i) (C i) (Ioo a b)) ∧
      (∀ i t, t ∈ Ioo a b → HasDerivAt (C i) (r i t) t) := by
  classical
  choose C hC hEq using fun i =>
    (lipschitzOnWith_of_weighted_derivative_energy m c r hm hderiv henergy i).extend_real
  refine ⟨C, hC, hEq, ?_⟩
  intro i t ht
  apply (hderiv i t ht).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds ht] with q hq
  exact (hEq i hq).symm

/-- The normalization of an interior intercept path extends to both endpoints.
The extension is globally measurable, hence can be used directly by the finite
affine-potential time-integration interface. -/
theorem exists_normalized_lipschitz_extension
    {ι : Type*} [Fintype ι] (m : ι → ℝ) (c r : ι → ℝ → ℝ)
    {a b energy : ℝ} (hab : a < b) (hm : ∀ i, 0 < m i)
    (hderiv : ∀ i t, t ∈ Ioo a b → HasDerivAt (c i) (r i t) t)
    (henergy : ∀ t ∈ Ioo a b, (∑ i, m i * r i t ^ 2) ≤ energy)
    (hnormal : ∀ t ∈ Ioo a b, (∑ i, m i * c i t) = 0) :
    ∃ C : ι → ℝ → ℝ,
      (∀ i, LipschitzWith ⟨Real.sqrt (energy / m i), Real.sqrt_nonneg _⟩ (C i)) ∧
      (∀ i, EqOn (c i) (C i) (Ioo a b)) ∧
      (∀ i t, t ∈ Ioo a b → HasDerivAt (C i) (r i t) t) ∧
      (∀ t ∈ Icc a b, (∑ i, m i * C i t) = 0) ∧
      (∀ i, Measurable (C i)) := by
  classical
  obtain ⟨C, hC, hEq, hdC⟩ := exists_lipschitz_extension m c r hm hderiv henergy
  refine ⟨C, hC, hEq, hdC, ?_, fun i => (hC i).continuous.measurable⟩
  have hsum : EqOn (fun t => ∑ i, m i * C i t) (fun _ => 0) (Ioo a b) := by
    intro t ht
    rw [← hnormal t ht]
    exact Finset.sum_congr rfl (fun i _ => congrArg (fun x => m i * x) (hEq i ht).symm)
  have hcont : Continuous (fun t => ∑ i, m i * C i t) :=
    continuous_finsetSum _ (fun i _ => continuous_const.mul (hC i).continuous)
  have hclosure := hsum.closure hcont continuous_const
  intro t ht
  apply hclosure
  simpa only [closure_Ioo hab.ne] using ht

end InterceptEndpointExtension
end Problem358

end

noncomputable section

open Set WithLp
open scoped BigOperators NNReal

namespace Problem358.WeightedEndpointEnergy

variable {ι : Type*} [Fintype ι]

/-- Encode the weighted coefficient norm in a Euclidean space. -/
def weightedVector (m z : ι → ℝ) : EuclideanSpace ℝ ι :=
  toLp 2 (fun i => Real.sqrt (m i) * z i)

theorem norm_weightedVector_sq (m z : ι → ℝ) (hm : ∀ i, 0 ≤ m i) :
    ‖weightedVector m z‖ ^ 2 = ∑ i, m i * z i ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  simp only [weightedVector, PiLp.toLp_apply, mul_pow, Real.sq_sqrt (hm i)]

omit [Fintype ι] in
theorem weightedVector_sub (m z w : ι → ℝ) :
    weightedVector m (z - w) = weightedVector m z - weightedVector m w := by
  ext i
  simp only [weightedVector, PiLp.toLp_apply, Pi.sub_apply, PiLp.sub_apply, mul_sub]

theorem hasDerivAt_weightedVector (m : ι → ℝ) (c r : ι → ℝ → ℝ) {t : ℝ}
    (hd : ∀ i, HasDerivAt (c i) (r i t) t) :
    HasDerivAt (fun s => weightedVector m (fun i => c i s))
      (weightedVector m (fun i => r i t)) t := by
  have hpi : HasDerivAt (fun s i => Real.sqrt (m i) * c i s)
      (fun i => Real.sqrt (m i) * r i t) t :=
    hasDerivAt_pi.mpr (fun i => (hd i).const_mul _)
  exact (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 _).comp_hasDerivAt t hpi

/-- The weighted coefficient path is Lipschitz with the square root of its
aggregate energy bound, independently of the number and sizes of the masses. -/
theorem weighted_path_lipschitzOn_Ioo
    (m : ι → ℝ) (c r : ι → ℝ → ℝ) {a b energy : ℝ}
    (hm : ∀ i, 0 ≤ m i) (he : 0 ≤ energy)
    (hd : ∀ i t, t ∈ Ioo a b → HasDerivAt (c i) (r i t) t)
    (henergy : ∀ t ∈ Ioo a b, ∑ i, m i * r i t ^ 2 ≤ energy) :
    LipschitzOnWith ⟨Real.sqrt energy, Real.sqrt_nonneg _⟩
      (fun t => weightedVector m (fun i => c i t)) (Ioo a b) := by
  apply (convex_Ioo a b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun t ht => (hasDerivAt_weightedVector m c r (fun i => hd i t ht)).hasDerivWithinAt)
  intro t ht
  change ‖weightedVector m (fun i => r i t)‖ ≤ Real.sqrt energy
  apply (Real.le_sqrt (norm_nonneg _) he).2
  rw [norm_weightedVector_sq m _ hm]
  exact henergy t ht

/-- Continuity extends the mass-independent weighted Lipschitz estimate to the
endpoints. Zero masses are allowed in this estimate. -/
theorem weighted_path_lipschitzOn_Icc
    (m : ι → ℝ) (c r : ι → ℝ → ℝ) {a b energy : ℝ}
    (hab : a < b) (hm : ∀ i, 0 ≤ m i) (he : 0 ≤ energy)
    (hc : ∀ i, ContinuousOn (c i) (Icc a b))
    (hd : ∀ i t, t ∈ Ioo a b → HasDerivAt (c i) (r i t) t)
    (henergy : ∀ t ∈ Ioo a b, ∑ i, m i * r i t ^ 2 ≤ energy) :
    LipschitzOnWith ⟨Real.sqrt energy, Real.sqrt_nonneg _⟩
      (fun t => weightedVector m (fun i => c i t)) (Icc a b) := by
  have hc' : ContinuousOn (fun t => weightedVector m (fun i => c i t)) (Icc a b) := by
    apply (PiLp.continuous_toLp 2 _).comp_continuousOn
    exact continuousOn_pi.mpr (fun i => continuousOn_const.mul (hc i))
  have hLip := weighted_path_lipschitzOn_Ioo m c r hm he hd henergy
  have hc'' : ContinuousOn (fun t => weightedVector m (fun i => c i t))
      (closure (Ioo a b)) := by simpa only [closure_Ioo hab.ne] using hc'
  simpa only [closure_Ioo hab.ne] using LipschitzOnWith.closure hc'' hLip

/-- Aggregate endpoint coefficient displacement inherits exactly the derivative
energy constant; unlike coordinatewise summation there is no cardinality loss. -/
theorem weighted_displacement_sq_le
    (m : ι → ℝ) (c r : ι → ℝ → ℝ) {a b energy s t : ℝ}
    (hab : a < b) (hm : ∀ i, 0 ≤ m i) (he : 0 ≤ energy)
    (hc : ∀ i, ContinuousOn (c i) (Icc a b))
    (hd : ∀ i q, q ∈ Ioo a b → HasDerivAt (c i) (r i q) q)
    (henergy : ∀ q ∈ Ioo a b, ∑ i, m i * r i q ^ 2 ≤ energy)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ∑ i, m i * (c i t - c i s) ^ 2 ≤ energy * (t - s) ^ 2 := by
  have hLip := weighted_path_lipschitzOn_Icc m c r hab hm he hc hd henergy
  have hbound := hLip.dist_le_mul t ht s hs
  rw [dist_eq_norm, Real.dist_eq] at hbound
  change ‖weightedVector m (fun i => c i t) - weightedVector m (fun i => c i s)‖ ≤
    Real.sqrt energy * |t - s| at hbound
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hbound 2
  rw [mul_pow, Real.sq_sqrt he, sq_abs] at hsq
  rw [← weightedVector_sub, norm_weightedVector_sq m _ hm] at hsq
  exact hsq

end Problem358.WeightedEndpointEnergy

end

end OAI
