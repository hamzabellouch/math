import OAI.Analysis.Brenier.AtomicPaths
import OAI.Analysis.Brenier.EndpointEnergy
import OAI.Analysis.Brenier.MaxLimits

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped NNReal BigOperators RealInnerProductSpace

namespace Problem358

/-- The bounded-energy, normalized interior intercept path itself supplies
continuous endpoint potentials with the uniform L² estimate.  In particular,
no limits or regularity of the original coefficients at times zero and one
are assumptions of this theorem. -/
theorem exists_normalized_finite_affine_endpoint_potentials
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (K : Set (E d)) [IsFiniteMeasure (uniformMeasure K)]
    (y v : ι → ℝ → E d) (c r : ι → ℝ → ℝ)
    (active : ℝ × E d → ι) (m : ι → ℝ)
    {w κ : ℝ} {R : ℝ≥0} (hw : 0 ≤ w) (hκ : 0 ≤ κ)
    (hxR : ∀ᵐ x ∂uniformMeasure K, ‖x‖ ≤ R)
    (hpositive : ∀ i, 0 < m i)
    (hy : ∀ i, Continuous (y i))
    (hv : ∀ i, ContinuousOn (v i) (Ioo 0 1))
    (hr : ∀ i, ContinuousOn (r i) (Ioo 0 1))
    (hactiveMeas : Measurable active)
    (hdy : ∀ i q, q ∈ Ioo 0 1 → HasDerivAt (y i) (v i q) q)
    (hdc : ∀ i q, q ∈ Ioo 0 1 → HasDerivAt (c i) (r i q) q)
    (hinj : ∀ q ∈ Ioo 0 1, Function.Injective (fun i => y i q))
    (hactive : ∀ q ∈ Ioo 0 1, ∀ x j,
      ⟪x, y j q⟫ + c j q ≤
        ⟪x, y (active (q, x)) q⟫ + c (active (q, x)) q)
    (hm : ∀ q ∈ Ioo 0 1, ∀ i,
      (uniformMeasure K).real {x | active (q, x) = i} = m i)
    (hnormal : ∀ q ∈ Ioo 0 1, (∑ i, m i * c i q) = 0)
    (hvEnergy : ∀ q ∈ Ioo 0 1, (∑ i, m i * ‖v i q‖ ^ 2) ≤ w ^ 2)
    (hrEnergy : ∀ q ∈ Ioo 0 1,
      (∑ i, m i * r i q ^ 2) ≤ κ * (R : ℝ) ^ 2 * w ^ 2) :
    ∃ cbar : ι → ℝ → ℝ,
      (∀ i, Continuous (cbar i)) ∧
      (∀ i, EqOn (c i) (cbar i) (Ioo 0 1)) ∧
      (∀ i q, q ∈ Ioo 0 1 → HasDerivAt (cbar i) (r i q) q) ∧
      (∀ q ∈ Icc 0 1, (∑ i, m i * cbar i q) = 0) ∧
      Real.sqrt (∫ x,
        (FiniteAffine.potential (fun i => y i 1) (fun i => cbar i 1) x -
         FiniteAffine.potential (fun i => y i 0) (fun i => cbar i 0) x) ^ 2
        ∂uniformMeasure K) ≤ Real.sqrt (2 * (1 + κ)) * R * w ∧
      (∫ x,
        (FiniteAffine.potential (fun i => y i 1) (fun i => cbar i 1) x -
         FiniteAffine.potential (fun i => y i 0) (fun i => cbar i 0) x) ^ 2
        ∂uniformMeasure K) ≤ 2 * (1 + κ) * (R : ℝ) ^ 2 * w ^ 2 := by
  obtain ⟨cbar, hLip, hEq, hdbar, hnormbar, _⟩ :=
    InterceptEndpointExtension.exists_normalized_lipschitz_extension
      m c r (by norm_num : (0 : ℝ) < 1) hpositive hdc hrEnergy hnormal
  have hcont (i : ι) : Continuous (cbar i) := (hLip i).continuous
  have hactivebar : ∀ q ∈ Ioo 0 1, ∀ x j,
      ⟪x, y j q⟫ + cbar j q ≤
        ⟪x, y (active (q, x)) q⟫ + cbar (active (q, x)) q := by
    intro q hq x j
    rw [← hEq j hq, ← hEq (active (q, x)) hq]
    exact hactive q hq x j
  have hbound := finite_affine_C1_path_endpoint_L2_bound K y v cbar r active m
    hw hκ hxR hy hcont hv hr hactiveMeas hdy hdbar hinj hactivebar hm hvEnergy hrEnergy
  refine ⟨cbar, hcont, hEq, hdbar, hnormbar, hbound, ?_⟩
  have hsquare : (Real.sqrt (2 * (1 + κ)) * R * w) ^ 2 =
      2 * (1 + κ) * (R : ℝ) ^ 2 * w ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  simpa only [hsquare] using (Real.sqrt_le_iff.mp hbound).2

end Problem358

end

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Problem358

/-- An everywhere maximizing affine-slope selection supports its finite maximum
at every point, including the tie set. -/
theorem MaxPotential.supports_of_maximizers
    {ι V : Type*} [Fintype ι] [Nonempty ι]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (y : ι → V) (c : ι → ℝ) {T : V → V}
    (hactive : ∀ x, ∃ i, T x = y i ∧
      ∀ j, inner ℝ x (y j) + c j ≤ inner ℝ x (y i) + c i) :
    SupportingMapInterpolation.Supports (MaxPotential.potential y c) T := by
  intro x z
  obtain ⟨i, hi, hmax⟩ := hactive x
  rw [hi]
  exact MaxPotential.supporting_inequality y c x z i hmax

/-- The exact endpoint maps of a continuous finite-affine path have global
supporting certificates and inherit the endpoint slope bounds. The interval-law
construction is supplied by `exists_unique_optimal_finite_affine_path_endpoints`;
no injectivity or positive individual mass is needed at the endpoints. -/
theorem exists_bounded_supporting_finite_affine_endpoint_pair
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hinterior : (interior K).Nonempty)
    {a b : ℝ} (hab : a < b)
    {y : ℝ → ι → E d} {c : ℝ → ι → ℝ}
    {T : ℝ → E d → E d}
    (w : ι → ℝ≥0∞) (hw : ∑ i, w i = 1)
    (hy : ∀ i, ContinuousOn (fun t => y t i) (Set.Icc a b))
    (hc : ∀ i, ContinuousOn (fun t => c t i) (Set.Icc a b))
    (hTm : ∀ t ∈ Set.Ioo a b, Measurable (T t))
    (hT : ∀ t ∈ Set.Ioo a b, ∀ᵐ x ∂uniformMeasure K,
      ∃ i, T t x = y t i ∧
        ∀ j, inner ℝ x (y t j) + c t j ≤ inner ℝ x (y t i) + c t i)
    (hpush : ∀ t ∈ Set.Ioo a b,
      Measure.map (T t) (uniformMeasure K) = ∑ i, w i • Measure.dirac (y t i))
    {L : ℝ} (hLa : ∀ i, ‖y a i‖ ≤ L) (hLb : ∀ i, ‖y b i‖ ≤ L) :
    ∃ Ta Tb : E d → E d,
      Measurable Ta ∧ Measurable Tb ∧
      Measure.map Ta (uniformMeasure K) = ∑ i, w i • Measure.dirac (y a i) ∧
      Measure.map Tb (uniformMeasure K) = ∑ i, w i • Measure.dirac (y b i) ∧
      SupportingMapInterpolation.Supports (MaxPotential.potential (y a) (c a)) Ta ∧
      SupportingMapInterpolation.Supports (MaxPotential.potential (y b) (c b)) Tb ∧
      (∀ x, ‖Ta x‖ ≤ L) ∧ (∀ x, ‖Tb x‖ ≤ L) ∧
      IsUniqueQuadraticOptimalMap (uniformMeasure K)
        (∑ i, w i • Measure.dirac (y a i)) Ta ∧
      IsUniqueQuadraticOptimalMap (uniformMeasure K)
        (∑ i, w i • Measure.dirac (y b i)) Tb := by
  obtain ⟨Ta, Tb, hTa, hTb, hoptA, hoptB⟩ :=
    exists_unique_optimal_finite_affine_path_endpoints
      hK hconv hinterior hab w hw hy hc hTm hT hpush
  refine ⟨Ta, Tb, hoptA.1.1, hoptB.1.1, hoptA.1.2.1, hoptB.1.2.1,
    MaxPotential.supports_of_maximizers (y a) (c a) hTa,
    MaxPotential.supports_of_maximizers (y b) (c b) hTb, ?_, ?_, hoptA, hoptB⟩
  · intro x
    obtain ⟨i, hi, _⟩ := hTa x
    rw [hi]
    exact hLa i
  · intro x
    obtain ⟨i, hi, _⟩ := hTb x
    rw [hi]
    exact hLb i

end Problem358

end

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators RealInnerProductSpace

namespace Problem358

/-- A normalized positive-mass affine motion gives the actual endpoint
supporting potentials and their exact atomic laws, together with the uniform
potential estimate. Neither separation nor intercept limits at the endpoints
are assumptions. -/
theorem exists_supporting_pair_of_normalized_affine_path
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {K : Set (E d)} (hK : IsCompact K) (hKconv : Convex ℝ K)
    (hKint : (interior K).Nonempty)
    (y v : ι → ℝ → E d) (c r : ι → ℝ → ℝ)
    (active : ℝ × E d → ι) (m : ι → ℝ)
    {w κ : ℝ} {R L : ℝ≥0} (hw : 0 ≤ w) (hκ : 0 ≤ κ)
    (hxR : ∀ᵐ x ∂uniformMeasure K, ‖x‖ ≤ R)
    (hpositive : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (hy : ∀ i, Continuous (y i))
    (hv : ∀ i, ContinuousOn (v i) (Ioo 0 1))
    (hr : ∀ i, ContinuousOn (r i) (Ioo 0 1))
    (hactiveMeas : Measurable active)
    (hdy : ∀ i q, q ∈ Ioo 0 1 → HasDerivAt (y i) (v i q) q)
    (hdc : ∀ i q, q ∈ Ioo 0 1 → HasDerivAt (c i) (r i q) q)
    (hinj : ∀ q ∈ Ioo 0 1, Function.Injective (fun i => y i q))
    (hactive : ∀ q ∈ Ioo 0 1, ∀ x j,
      ⟪x, y j q⟫ + c j q ≤
        ⟪x, y (active (q, x)) q⟫ + c (active (q, x)) q)
    (hm : ∀ q ∈ Ioo 0 1, ∀ i,
      (uniformMeasure K).real {x | active (q, x) = i} = m i)
    (hnormal : ∀ q ∈ Ioo 0 1, (∑ i, m i * c i q) = 0)
    (hvEnergy : ∀ q ∈ Ioo 0 1, (∑ i, m i * ‖v i q‖ ^ 2) ≤ w ^ 2)
    (hrEnergy : ∀ q ∈ Ioo 0 1,
      (∑ i, m i * r i q ^ 2) ≤ κ * (R : ℝ) ^ 2 * w ^ 2)
    (hy0 : ∀ i, ‖y i 0‖ ≤ L) (hy1 : ∀ i, ‖y i 1‖ ≤ L) :
    ∃ (u₀ u₁ : E d → ℝ) (T₀ T₁ : E d → E d),
      SupportingMapInterpolation.Supports u₀ T₀ ∧
      SupportingMapInterpolation.Supports u₁ T₁ ∧
      Measurable T₀ ∧ Measurable T₁ ∧
      (∀ x, ‖T₀ x‖ ≤ L) ∧ (∀ x, ‖T₁ x‖ ≤ L) ∧
      Measure.map T₀ (uniformMeasure K) =
        ∑ i, ENNReal.ofReal (m i) • Measure.dirac (y i 0) ∧
      Measure.map T₁ (uniformMeasure K) =
        ∑ i, ENNReal.ofReal (m i) • Measure.dirac (y i 1) ∧
      (∫ x, (u₀ x - u₁ x) ^ 2 ∂uniformMeasure K) ≤
        2 * (1 + κ) * (R : ℝ) ^ 2 * w ^ 2 := by
  let : IsProbabilityMeasure (uniformMeasure K) := UniformSource.probability hK hKint
  obtain ⟨cbar, hcbar, hEq, _, _, _, hbound⟩ :=
    exists_normalized_finite_affine_endpoint_potentials K y v c r active m
      hw hκ hxR hpositive hy hv hr hactiveMeas hdy hdc hinj hactive hm
      hnormal hvEnergy hrEnergy
  let T : ℝ → E d → E d := fun q x => y (active (q, x)) q
  have hTm (q : ℝ) : Measurable (T q) :=
    (measurable_of_countable (fun i => y i q)).comp
      (hactiveMeas.comp (measurable_const.prodMk measurable_id))
  have hweights : (∑ i, ENNReal.ofReal (m i)) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => (hpositive i).le), hsum]
    exact ENNReal.ofReal_one
  have hactivebar : ∀ q ∈ Ioo 0 1, ∀ x j,
      ⟪x, y j q⟫ + cbar j q ≤
        ⟪x, y (active (q, x)) q⟫ + cbar (active (q, x)) q := by
    intro q hq x j
    rw [← hEq j hq, ← hEq (active (q, x)) hq]
    exact hactive q hq x j
  have hpush (q : ℝ) (hq : q ∈ Ioo 0 1) :
      Measure.map (T q) (uniformMeasure K) =
        ∑ i, ENNReal.ofReal (m i) • Measure.dirac (y i q) := by
    apply map_finite_selector_of_masses (uniformMeasure K)
      (fun x => active (q, x))
      (hactiveMeas.comp (measurable_const.prodMk measurable_id))
      (fun i => y i q) (fun i => ENNReal.ofReal (m i))
    intro i
    rw [← hm q hq i]
    exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  obtain ⟨T₀, T₁, hT₀active, hT₁active, hT₀opt, hT₁opt⟩ :=
    exists_unique_optimal_finite_affine_path_endpoints hK hKconv hKint
      (by norm_num : (0 : ℝ) < 1) (fun i => ENNReal.ofReal (m i)) hweights
      (fun i => (hy i).continuousOn) (fun i => (hcbar i).continuousOn)
      (fun q _ => hTm q)
      (fun q hq => Filter.Eventually.of_forall fun x =>
        ⟨active (q, x), rfl, hactivebar q hq x⟩) hpush
  refine ⟨MaxPotential.potential (fun i => y i 0) (fun i => cbar i 0),
    MaxPotential.potential (fun i => y i 1) (fun i => cbar i 1), T₀, T₁,
    ?_, ?_, hT₀opt.1.1, hT₁opt.1.1, ?_, ?_, hT₀opt.1.2.1, hT₁opt.1.2.1, ?_⟩
  · intro x z
    obtain ⟨i, hi, hmax⟩ := hT₀active x
    rw [hi]
    exact MaxPotential.supporting_inequality _ _ x z i hmax
  · intro x z
    obtain ⟨i, hi, hmax⟩ := hT₁active x
    rw [hi]
    exact MaxPotential.supporting_inequality _ _ x z i hmax
  · intro x
    obtain ⟨i, hi, _⟩ := hT₀active x
    rw [hi]
    exact hy0 i
  · intro x
    obtain ⟨i, hi, _⟩ := hT₁active x
    rw [hi]
    exact hy1 i
  · convert hbound using 1
    congr 1
    funext x
    dsimp only [MaxPotential.potential, FiniteAffine.potential]
    ring

end Problem358

namespace Problem358

/-- The geometric closed-cell mass equations suffice for the endpoint potential
pair construction. A common measurable maximizing selector and all its mass
identities are derived, not supplied as additional path assumptions. -/
theorem exists_supporting_pair_of_closedCell_path
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {K : Set (E d)} (hK : IsCompact K) (hKconv : Convex ℝ K)
    (hKint : (interior K).Nonempty)
    (y v : ι → ℝ → E d) (c r : ι → ℝ → ℝ) (m : ι → ℝ)
    {w κ : ℝ} {R L : ℝ≥0} (hw : 0 ≤ w) (hκ : 0 ≤ κ)
    (hxR : ∀ᵐ x ∂uniformMeasure K, ‖x‖ ≤ R)
    (hpositive : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (hy : ∀ i, Continuous (y i)) (hc : ∀ i, Measurable (c i))
    (hv : ∀ i, ContinuousOn (v i) (Ioo 0 1))
    (hr : ∀ i, ContinuousOn (r i) (Ioo 0 1))
    (hdy : ∀ i q, q ∈ Ioo 0 1 → HasDerivAt (y i) (v i q) q)
    (hdc : ∀ i q, q ∈ Ioo 0 1 → HasDerivAt (c i) (r i q) q)
    (hinj : ∀ q ∈ Ioo 0 1, Function.Injective (fun i => y i q))
    (hm : ∀ q ∈ Ioo 0 1, ∀ i,
      (uniformMeasure K).real
        (CellGeometry.closedCell K (fun j => y j q) (fun j => c j q) i) = m i)
    (hnormal : ∀ q ∈ Ioo 0 1, (∑ i, m i * c i q) = 0)
    (hvEnergy : ∀ q ∈ Ioo 0 1, (∑ i, m i * ‖v i q‖ ^ 2) ≤ w ^ 2)
    (hrEnergy : ∀ q ∈ Ioo 0 1,
      (∑ i, m i * r i q ^ 2) ≤ κ * (R : ℝ) ^ 2 * w ^ 2)
    (hy0 : ∀ i, ‖y i 0‖ ≤ L) (hy1 : ∀ i, ‖y i 1‖ ≤ L) :
    ∃ (u₀ u₁ : E d → ℝ) (T₀ T₁ : E d → E d),
      SupportingMapInterpolation.Supports u₀ T₀ ∧
      SupportingMapInterpolation.Supports u₁ T₁ ∧
      Measurable T₀ ∧ Measurable T₁ ∧
      (∀ x, ‖T₀ x‖ ≤ L) ∧ (∀ x, ‖T₁ x‖ ≤ L) ∧
      Measure.map T₀ (uniformMeasure K) =
        ∑ i, ENNReal.ofReal (m i) • Measure.dirac (y i 0) ∧
      Measure.map T₁ (uniformMeasure K) =
        ∑ i, ENNReal.ofReal (m i) • Measure.dirac (y i 1) ∧
      (∫ x, (u₀ x - u₁ x) ^ 2 ∂uniformMeasure K) ≤
        2 * (1 + κ) * (R : ℝ) ^ 2 * w ^ 2 := by
  obtain ⟨active, hactiveMeas, hactive, hmass⟩ :=
    CellGeometry.exists_joint_measurable_selector_prescribed_masses hK.measurableSet
      (fun q i => y i q) (fun q i => c i q) (fun _ i => m i) (Ioo 0 1)
      (fun i => (hy i).measurable) hc hinj hm
  exact exists_supporting_pair_of_normalized_affine_path hK hKconv hKint
    y v c r active m hw hκ hxR hpositive hsum hy hv hr hactiveMeas hdy hdc
    hinj (fun q _ => hactive q) hmass hnormal hvEnergy hrEnergy hy0 hy1

end Problem358

end

end OAI
