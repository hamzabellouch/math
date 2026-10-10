import OAI.Analysis.Brenier.AffinePaths
import OAI.Analysis.Brenier.Approximation
import OAI.Analysis.Brenier.AtomicTransport
import OAI.Analysis.Brenier.UniformInterpolation

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators RealInnerProductSpace NNReal

namespace Problem358

/-- The interior potential estimate for an actual linear motion of the sites.
All auxiliary boundedness and joint-selector hypotheses of the time-integration
theorem are consequences of the positive masses and the energy bounds. -/
theorem atomic_potential_path_L2_bound
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (K : Set (E d)) [IsFiniteMeasure (uniformMeasure K)]
    (y z : ι → E d) (m : ι → ℝ) (c r : ι → ℝ → ℝ)
    {w κ : ℝ} {R : ℝ≥0}
    (hw : 0 ≤ w) (hκ : 0 ≤ κ) (hm : ∀ i, 0 < m i)
    (hxR : ∀ᵐ x ∂uniformMeasure K, ‖x‖ ≤ R)
    (hc : ∀ i, Measurable (c i)) (hr : ∀ i, Measurable (r i))
    (hdc : ∀ i t, t ∈ Ioo (0 : ℝ) 1 → HasDerivAt (c i) (r i t) t)
    (hinj : ∀ t ∈ Ioo (0 : ℝ) 1,
      Function.Injective (fun i => (1-t) • y i + t • z i))
    (hcell : ∀ t ∈ Ioo (0 : ℝ) 1, ∃ k : E d → ι,
      (∀ᵐ x ∂uniformMeasure K, ∀ j,
        ⟪x, (1-t) • y j + t • z j⟫ + c j t ≤
        ⟪x, (1-t) • y (k x) + t • z (k x)⟫ + c (k x) t) ∧
      ∀ i, (uniformMeasure K).real {x | k x = i} = m i)
    (hvEnergy : (∑ i, m i * ‖z i-y i‖ ^ 2) ≤ w ^ 2)
    (hrEnergy : ∀ t ∈ Ioo (0 : ℝ) 1,
      (∑ i, m i * r i t ^ 2) ≤ κ * (R : ℝ) ^ 2 * w ^ 2)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    Real.sqrt (∫ x,
      (FiniteAffine.potential (fun i => (1-b) • y i + b • z i) (fun i => c i b) x -
        FiniteAffine.potential (fun i => (1-a) • y i + a • z i) (fun i => c i a) x) ^ 2
      ∂uniformMeasure K) ≤ (Real.sqrt (2 * (1 + κ)) * R * w) * (b - a) := by
  let Y : ι → ℝ → E d := fun i t => (1-t) • y i + t • z i
  let V : ι → ℝ → E d := fun i _ => z i-y i
  have hY : ∀ i, Measurable (Y i) := by intro i; dsimp [Y]; fun_prop
  have hV : ∀ i, Measurable (V i) := fun _ => measurable_const
  have hdY : ∀ i t, HasDerivAt (Y i) (V i t) t := by
    intro i t
    have hYeq : Y i = fun q : ℝ => y i + q • (z i-y i) := by
      funext q
      dsimp [Y]
      module
    rw [hYeq]
    simpa only [V, one_smul] using!
      ((hasDerivAt_id t).smul_const (z i-y i)).const_add (y i)
  have htime : Icc a b ⊆ Ioo (0 : ℝ) 1 := by
    intro t ht
    exact ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩
  apply finite_affine_path_L2_bound_of_positive_cell_masses K Y V c r m
    hab hw hκ hm hxR hY hc hV hr
  · intro i t _
    exact hdY i t
  · intro i t ht
    exact hdc i t (htime ht)
  · intro t ht
    exact hinj t (htime (Ioc_subset_Icc_self ht))
  · intro t ht
    exact hcell t (htime (Ioc_subset_Icc_self ht))
  · intro t _
    exact hvEnergy
  · intro t ht
    exact hrEnergy t (htime ht)

/-- The same actual atomic-motion estimate takes the canonical closed-cell mass
equations directly. In particular, existence or measurability of prescribed-mass
active selectors is not an additional hypothesis on the intercept path. -/
theorem atomic_potential_path_L2_bound_of_closed_masses
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {K : Set (E d)} [IsFiniteMeasure (uniformMeasure K)] (hK : MeasurableSet K)
    (y z : ι → E d) (m : ι → ℝ) (c r : ι → ℝ → ℝ)
    {w κ : ℝ} {R : ℝ≥0}
    (hw : 0 ≤ w) (hκ : 0 ≤ κ) (hm : ∀ i, 0 < m i)
    (hxR : ∀ᵐ x ∂uniformMeasure K, ‖x‖ ≤ R)
    (hc : ∀ i, Measurable (c i)) (hr : ∀ i, Measurable (r i))
    (hdc : ∀ i t, t ∈ Ioo (0 : ℝ) 1 → HasDerivAt (c i) (r i t) t)
    (hinj : ∀ t ∈ Ioo (0 : ℝ) 1,
      Function.Injective (fun i => (1-t) • y i + t • z i))
    (hcell : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ i,
      (uniformMeasure K).real (CellGeometry.closedCell K
        (fun j => (1-t) • y j + t • z j) (fun j => c j t) i) = m i)
    (hvEnergy : (∑ i, m i * ‖z i-y i‖ ^ 2) ≤ w ^ 2)
    (hrEnergy : ∀ t ∈ Ioo (0 : ℝ) 1,
      (∑ i, m i * r i t ^ 2) ≤ κ * (R : ℝ) ^ 2 * w ^ 2)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    Real.sqrt (∫ x,
      (FiniteAffine.potential (fun i => (1-b) • y i + b • z i) (fun i => c i b) x -
        FiniteAffine.potential (fun i => (1-a) • y i + a • z i) (fun i => c i a) x) ^ 2
      ∂uniformMeasure K) ≤ (Real.sqrt (2 * (1 + κ)) * R * w) * (b - a) := by
  obtain ⟨active, _, hmax, hmass⟩ :=
    CellGeometry.exists_joint_measurable_selector_prescribed_masses hK
      (fun t i => (1-t) • y i + t • z i) (fun t i => c i t) (fun _ => m)
      (Ioo (0 : ℝ) 1) (fun i => by fun_prop) hc hinj hcell
  apply atomic_potential_path_L2_bound K y z m c r hw hκ hm hxR
    hc hr hdc hinj _ hvEnergy hrEnergy ha hab hb
  intro t ht
  exact ⟨fun x => active (t, x), ae_of_all _ (fun x j => hmax t x j), hmass t ht⟩

end Problem358

end

noncomputable section

open MeasureTheory
open scoped NNReal RealInnerProductSpace

namespace Problem358

namespace SupportingMapInterpolation

/-- A globally supporting map with bounded values makes its potential Lipschitz.
No differentiability or convexity premise is needed for this implication. -/
theorem Supports.lipschitzWith {d : ℕ} {u : E d → ℝ} {T : E d → E d}
    (h : Supports u T) {L : ℝ≥0} (hL : ∀ x, ‖T x‖ ≤ L) :
    LipschitzWith L u := by
  apply LipschitzWith.of_le_add_mul L
  intro x z
  have hs := h x z
  rw [show z - x = -(x - z) by abel, inner_neg_left] at hs
  have hi : ⟪x - z, T x⟫ ≤ (L : ℝ) * dist x z := by
    calc
      ⟪x - z, T x⟫ ≤ |⟪x - z, T x⟫| := le_abs_self _
      _ ≤ ‖x - z‖ * ‖T x‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖x - z‖ * L := mul_le_mul_of_nonneg_left (hL x) (norm_nonneg _)
      _ = (L : ℝ) * dist x z := by rw [dist_eq_norm, mul_comm]
  linarith

end SupportingMapInterpolation

/-- The exact compact-target stability conclusion reduces to a uniform potential
estimate for finite targets. The supplier only gives supporting maps and their
laws: optimality, uniqueness, the one-third interpolation, and passage to
arbitrary compactly supported probabilities are all proved here. -/
theorem one_third_stability_of_finite_potential_estimate
    {d : ℕ} {K Y : Set (E d)}
    (hK : IsCompact K) (hKconv : Convex ℝ K)
    (hKint : (interior K).Nonempty) (hY : IsCompact Y) (hYne : Y.Nonempty)
    (L : ℝ≥0) (P : ℝ)
    (hpotential : ∀ (μ ν : Measure (E d)),
      IsProbabilityMeasure μ → IsProbabilityMeasure ν →
      (∃ F : Set (E d), F.Finite ∧ F ⊆ Y ∧ IsSupported μ F) →
      (∃ G : Set (E d), G.Finite ∧ G ⊆ Y ∧ IsSupported ν G) →
      ∃ (u v : E d → ℝ) (T S : E d → E d),
        SupportingMapInterpolation.Supports u T ∧
        SupportingMapInterpolation.Supports v S ∧
        Measurable T ∧ Measurable S ∧
        (∀ x, ‖T x‖ ≤ L) ∧ (∀ x, ‖S x‖ ≤ L) ∧
        Measure.map T (uniformMeasure K) = μ ∧
        Measure.map S (uniformMeasure K) = ν ∧
        ∃ c : ℝ, (∫ x, (u x - v x - c) ^ 2 ∂uniformMeasure K) ≤
          P ^ 2 * wasserstein2 μ ν ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ ν : Measure (E d)),
      IsProbabilityMeasure μ → IsProbabilityMeasure ν →
      IsSupported μ Y → IsSupported ν Y →
      ∃ Tμ Tν : E d → E d,
        IsUniqueQuadraticOptimalMap (uniformMeasure K) μ Tμ ∧
        IsUniqueQuadraticOptimalMap (uniformMeasure K) ν Tν ∧
        mapL2Dist (uniformMeasure K) Tμ Tν ≤
          C * Real.rpow (wasserstein2 μ ν) (1 / 3 : ℝ) := by
  obtain ⟨C, hC, hinterpolate⟩ :=
    UniformInterpolation.exists_normalized_one_third_constant hK hKconv hKint L P
  refine ⟨C, hC, one_third_stability_of_finite_targets hK hKconv hKint hY hYne hC ?_⟩
  intro μ ν hμprob hνprob hμfinite hνfinite
  let : IsProbabilityMeasure μ := hμprob
  let : IsProbabilityMeasure ν := hνprob
  obtain ⟨u, v, T, S, hu, hv, hT, hS, hTL, hSL, hTlaw, hSlaw, hbound⟩ :=
    hpotential μ ν hμprob hνprob hμfinite hνfinite
  have hμY : IsSupported μ Y := by
    obtain ⟨F, _, hFY, hμF⟩ := hμfinite
    exact le_antisymm ((measure_mono (Set.compl_subset_compl.mpr hFY)).trans_eq hμF)
      zero_le
  have hνY : IsSupported ν Y := by
    obtain ⟨G, _, hGY, hνG⟩ := hνfinite
    exact le_antisymm ((measure_mono (Set.compl_subset_compl.mpr hGY)).trans_eq hνG)
      zero_le
  have huLip := hu.lipschitzWith hTL
  have hvLip := hv.lipschitzWith hSL
  have hKne : K.Nonempty := hKint.mono interior_subset
  refine ⟨T, S, ?_, ?_, ?_⟩
  · apply isUniqueQuadraticOptimalMap_of_supporting_potential hK hKconv hKne
      hY hμY huLip.lipschitzOnWith hT hTlaw
    exact Filter.Eventually.of_forall fun x z _ => by
      simpa only [real_inner_comm (T x) (z - x)] using hu x z
  · apply isUniqueQuadraticOptimalMap_of_supporting_potential hK hKconv hKne
      hY hνY hvLip.lipschitzOnWith hS hSlaw
    exact Filter.Eventually.of_forall fun x z _ => by
      simpa only [real_inner_comm (S x) (z - x)] using hv x z
  · exact hinterpolate u v T S huLip.continuous hvLip.continuous hu hv hT hS
      hTL hSL (wasserstein2 μ ν) (wasserstein2_nonneg μ ν) hbound

end Problem358

end

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Problem358

/-- A potential estimate for positive fixed-mass, noncolliding atomic motions
implies the full compact-target theorem. The optimal finite coupling, zero-mass
deletion, endpoint laws and exact Wasserstein energy are supplied internally. -/
theorem one_third_stability_of_atomic_potential_estimate
    {d : ℕ} {K Y : Set (E d)}
    (hK : IsCompact K) (hKconv : Convex ℝ K)
    (hKint : (interior K).Nonempty) (hY : IsCompact Y) (hYne : Y.Nonempty)
    (L : ℝ≥0) (hYL : ∀ z ∈ Y, ‖z‖ ≤ L) (P : ℝ)
    (hpotential : ∀ (n : ℕ), 0 < n →
      ∀ (m : Fin n → ℝ) (y z : Fin n → E d),
      (∀ i, 0 < m i) → (∑ i, m i) = 1 →
      (∀ i, ‖y i‖ ≤ L) → (∀ i, ‖z i‖ ≤ L) →
      (∀ t : ℝ, 0 < t → t < 1 →
        Function.Injective (fun i => (1-t) • y i + t • z i)) →
      ∃ (u v : E d → ℝ) (T S : E d → E d),
        SupportingMapInterpolation.Supports u T ∧
        SupportingMapInterpolation.Supports v S ∧
        Measurable T ∧ Measurable S ∧
        (∀ x, ‖T x‖ ≤ L) ∧ (∀ x, ‖S x‖ ≤ L) ∧
        Measure.map T (uniformMeasure K) =
          ∑ i, ENNReal.ofReal (m i) • Measure.dirac (y i) ∧
        Measure.map S (uniformMeasure K) =
          ∑ i, ENNReal.ofReal (m i) • Measure.dirac (z i) ∧
        ∃ c : ℝ, (∫ x, (u x - v x - c) ^ 2 ∂uniformMeasure K) ≤
          P ^ 2 * ∑ i, m i * ‖y i - z i‖ ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ ν : Measure (E d)),
      IsProbabilityMeasure μ → IsProbabilityMeasure ν →
      IsSupported μ Y → IsSupported ν Y →
      ∃ Tμ Tν : E d → E d,
        IsUniqueQuadraticOptimalMap (uniformMeasure K) μ Tμ ∧
        IsUniqueQuadraticOptimalMap (uniformMeasure K) ν Tν ∧
        mapL2Dist (uniformMeasure K) Tμ Tν ≤
          C * Real.rpow (wasserstein2 μ ν) (1 / 3 : ℝ) := by
  apply one_third_stability_of_finite_potential_estimate hK hKconv hKint hY hYne L P
  intro μ ν hμprob hνprob hμfinite hνfinite
  let : IsProbabilityMeasure μ := hμprob
  let : IsProbabilityMeasure ν := hνprob
  obtain ⟨F, hF, hFY, hμF⟩ := hμfinite
  obtain ⟨G, hG, hGY, hνG⟩ := hνfinite
  obtain ⟨n, hn, m, y, z, hm, hsum, hyF, hzG, hμeq, hνeq, _, henergy, hinj⟩ :=
    exists_finite_atomic_motion hF hG hμF hνG
  obtain ⟨u, v, T, S, hu, hv, hT, hS, hTL, hSL, hTlaw, hSlaw, c, hc⟩ :=
    hpotential n hn m y z hm hsum (fun i => hYL _ (hFY (hyF i)))
      (fun i => hYL _ (hGY (hzG i))) hinj
  refine ⟨u, v, T, S, hu, hv, hT, hS, hTL, hSL,
    hTlaw.trans hμeq.symm, hSlaw.trans hνeq.symm, c, ?_⟩
  simpa only [henergy] using hc

end Problem358

end

end OAI
