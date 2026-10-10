import OAI.Analysis.Brenier.NormalizedPaths

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace NNReal BigOperators

namespace Problem358

/-- The finite-affine time estimate stated directly in terms of genuine closed
cell masses. A jointly measurable maximizing selector and its exact masses are
constructed internally. Injectivity is required only on the interval of use. -/
theorem finite_affine_path_L2_bound_of_closedCell
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {K : Set (E d)} (hK : MeasurableSet K)
    [IsFiniteMeasure (uniformMeasure K)]
    (y v : ι → ℝ → E d) (c r : ι → ℝ → ℝ) (m : ι → ℝ)
    {a b w κ : ℝ} {R A B : ℝ≥0}
    (hab : a < b) (hw : 0 ≤ w) (hκ : 0 ≤ κ)
    (hxR : ∀ᵐ x ∂uniformMeasure K, ‖x‖ ≤ R)
    (hy : ∀ i, Measurable (y i)) (hc : ∀ i, Measurable (c i))
    (hv : ∀ i, Measurable (v i)) (hr : ∀ i, Measurable (r i))
    (hdy : ∀ i q, q ∈ Icc a b → HasDerivAt (y i) (v i q) q)
    (hdc : ∀ i q, q ∈ Icc a b → HasDerivAt (c i) (r i q) q)
    (hvBound : ∀ i q, q ∈ Icc a b → ‖v i q‖ ≤ A)
    (hrBound : ∀ i q, q ∈ Icc a b → ‖r i q‖ ≤ B)
    (hinj : ∀ q ∈ Ioc a b, Function.Injective (fun i => y i q))
    (hm : ∀ q ∈ Ioc a b, ∀ i,
      (uniformMeasure K).real
        (CellGeometry.closedCell K (fun j => y j q) (fun j => c j q) i) = m i)
    (hvEnergy : ∀ q ∈ Ioc a b, (∑ i, m i * ‖v i q‖ ^ 2) ≤ w ^ 2)
    (hrEnergy : ∀ q ∈ Ioc a b,
      (∑ i, m i * r i q ^ 2) ≤ κ * (R : ℝ) ^ 2 * w ^ 2) :
    Real.sqrt (∫ x,
      (FiniteMaxDerivative.maxValue (fun i q => ⟪x, y i q⟫ + c i q) b -
        FiniteMaxDerivative.maxValue (fun i q => ⟪x, y i q⟫ + c i q) a) ^ 2
      ∂uniformMeasure K) ≤ (Real.sqrt (2 * (1 + κ)) * R * w) * (b - a) := by
  obtain ⟨active, hactiveMeas, hactive, hmass⟩ :=
    CellGeometry.exists_joint_measurable_selector_prescribed_masses hK
      (fun q i => y i q) (fun q i => c i q) (fun _ i => m i) (Ioc a b)
      hy hc hinj hm
  have hinjAE : ∀ᵐ q ∂volume.restrict (Ioc a b),
      Function.Injective (fun i => y i q) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with q hq
    exact hinj q hq
  exact finite_affine_path_L2_bound K y v c r active m hab hw hκ hxR hy hc hv hr
    hactiveMeas hdy hdc hvBound hrBound hinjAE
    (Filter.Eventually.of_forall fun p => hactive p.1 p.2)
    hmass hvEnergy hrEnergy

end Problem358

end

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators RealInnerProductSpace

namespace Problem358

/-- Complete stability from the genuine geometric intercept-path assertion.
All endpoint construction, finite optimal coupling, potential interpolation,
optimal-map uniqueness and finite-to-general approximation are discharged.
The remaining premise is precisely a normalized positive closed-cell path
with its weighted derivative-energy bound. -/
theorem one_third_stability_of_closedCell_intercept_paths
    {d : ℕ} {K Y : Set (E d)}
    (hK : IsCompact K) (hKconv : Convex ℝ K)
    (hKint : (interior K).Nonempty) (hY : IsCompact Y) (hYne : Y.Nonempty)
    (R L : ℝ≥0) (hxR : ∀ᵐ x ∂uniformMeasure K, ‖x‖ ≤ R)
    (hYL : ∀ z ∈ Y, ‖z‖ ≤ L) {κ : ℝ} (hκ : 0 ≤ κ)
    (hpaths : ∀ (n : ℕ), 0 < n →
      ∀ (m : Fin n → ℝ) (y z : Fin n → E d),
      (∀ i, 0 < m i) → (∑ i, m i) = 1 →
      (∀ i, ‖y i‖ ≤ L) → (∀ i, ‖z i‖ ≤ L) →
      (∀ t : ℝ, 0 < t → t < 1 →
        Function.Injective (fun i => (1-t) • y i + t • z i)) →
      ∃ c r : Fin n → ℝ → ℝ,
        (∀ i, Measurable (c i)) ∧
        (∀ i, ContinuousOn (r i) (Ioo 0 1)) ∧
        (∀ i t, t ∈ Ioo 0 1 → HasDerivAt (c i) (r i t) t) ∧
        (∀ t ∈ Ioo 0 1, ∀ i,
          (uniformMeasure K).real (CellGeometry.closedCell K
            (fun j => (1-t) • y j + t • z j) (fun j => c j t) i) = m i) ∧
        (∀ t ∈ Ioo 0 1, (∑ i, m i * c i t) = 0) ∧
        ∀ t ∈ Ioo 0 1, (∑ i, m i * r i t ^ 2) ≤
          κ * (R : ℝ) ^ 2 * ∑ i, m i * ‖y i - z i‖ ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ ν : Measure (E d)),
      IsProbabilityMeasure μ → IsProbabilityMeasure ν →
      IsSupported μ Y → IsSupported ν Y →
      ∃ Tμ Tν : E d → E d,
        IsUniqueQuadraticOptimalMap (uniformMeasure K) μ Tμ ∧
        IsUniqueQuadraticOptimalMap (uniformMeasure K) ν Tν ∧
        mapL2Dist (uniformMeasure K) Tμ Tν ≤
          C * Real.rpow (wasserstein2 μ ν) (1 / 3 : ℝ) := by
  apply one_third_stability_of_atomic_potential_estimate hK hKconv hKint hY hYne
    L hYL (Real.sqrt (2 * (1 + κ)) * R)
  intro n hn m y z hm hsum hyL hzL hinj
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  obtain ⟨c, r, hc, hr, hdc, hmass, hnormal, henergy⟩ :=
    hpaths n hn m y z hm hsum hyL hzL hinj
  let e : ℝ := ∑ i, m i * ‖y i - z i‖ ^ 2
  have he : 0 ≤ e := Finset.sum_nonneg fun i _ => mul_nonneg (hm i).le (sq_nonneg _)
  have hsqrt : Real.sqrt e ^ 2 = e := Real.sq_sqrt he
  let path : Fin n → ℝ → E d := fun i t => (1-t) • y i + t • z i
  let velocity : Fin n → ℝ → E d := fun i _ => z i - y i
  have hpath : ∀ i, Continuous (path i) := by intro i; dsimp [path]; fun_prop
  have hdpath : ∀ i t, HasDerivAt (path i) (velocity i t) t := by
    intro i t
    have heq : path i = fun q : ℝ => y i + q • (z i - y i) := by
      funext q
      dsimp [path]
      module
    rw [heq]
    simpa only [velocity, one_smul] using!
      ((hasDerivAt_id t).smul_const (z i - y i)).const_add (y i)
  have hvEnergy : ∀ t ∈ Ioo (0 : ℝ) 1,
      (∑ i, m i * ‖velocity i t‖ ^ 2) ≤ Real.sqrt e ^ 2 := by
    intro t _
    rw [hsqrt]
    exact le_of_eq (Finset.sum_congr rfl fun i _ => by simp only [velocity, norm_sub_rev])
  obtain ⟨u₀, u₁, T₀, T₁, hu₀, hu₁, hT₀, hT₁, hT₀L, hT₁L, hμ, hν, hb⟩ :=
    exists_supporting_pair_of_closedCell_path hK hKconv hKint path velocity c r m
      (Real.sqrt_nonneg e) hκ hxR hm hsum hpath hc
      (fun _ => continuousOn_const) hr (fun i t _ => hdpath i t) hdc
      (fun t ht => hinj t ht.1 ht.2) hmass hnormal hvEnergy
      (fun t ht => by simpa only [hsqrt] using henergy t ht)
      (fun i => by simpa [path] using hyL i)
      (fun i => by simpa [path] using hzL i)
  refine ⟨u₀, u₁, T₀, T₁, hu₀, hu₁, hT₀, hT₁, hT₀L, hT₁L,
    ?_, ?_, 0, ?_⟩
  · simpa [path] using hμ
  · simpa [path] using hν
  · have hP : (Real.sqrt (2 * (1 + κ)) * (R : ℝ)) ^ 2 =
        2 * (1 + κ) * (R : ℝ) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
    simpa only [sub_zero, hP, hsqrt] using hb

end Problem358

end

end OAI
