import OAI.Analysis.Brenier.CellGeometry
import OAI.Analysis.Brenier.Minimizers

namespace OAI

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace BigOperators

namespace Problem358.MaxPotential

variable {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- An absolutely continuous probability with finite first moment realizes every
strictly positive finite mass vector by an affine maximum partition. -/
theorem exists_prescribed_cell_masses_of_ac_volume
    (ρ : Measure (E d)) [IsProbabilityMeasure ρ]
    (hac : ρ ≪ (volume : Measure (E d)))
    (hρ : Integrable (fun x : E d => ‖x‖) ρ)
    (y : ι → E d) (hinj : Function.Injective y) (m : ι → ℝ)
    (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1) :
    ∃ (c : ι → ℝ) (k : E d → ι),
      (∑ i, m i * c i) = 0 ∧ Measurable k ∧
      (∀ x j, ⟪x, y j⟫ + c j ≤ ⟪x, y (k x)⟫ + c (k x)) ∧
      (∀ i, ρ.real {x | k x = i} = m i) := by
  let L : NNReal := ∑ i, ‖y i‖₊
  have hL : ∀ i, ‖y i‖ ≤ L := by
    intro i
    have hi : ‖y i‖₊ ≤ L :=
      Finset.single_le_sum (fun j _ => (show (0 : NNReal) ≤ ‖y j‖₊ from zero_le)) (Finset.mem_univ i)
    exact_mod_cast hi
  apply exists_prescribed_cell_masses ρ y m hm hsum L hL hρ
  intro c
  filter_upwards [hac.ae_le (ae_affine_tie_implies_slopes_eq volume y c)] with x hx
  intro i j hij heq
  exact hij (hinj (hx i j heq))

/-- The prescribed-mass affine partition exists for the uniform source on a compact body.
Compactness supplies the first moment; no cell calculus is assumed. -/
theorem exists_prescribed_cell_masses_uniform
    (K : Set (E d)) [IsProbabilityMeasure (uniformMeasure K)]
    (hK : IsCompact K) (y : ι → E d) (hinj : Function.Injective y) (m : ι → ℝ)
    (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1) :
    ∃ (c : ι → ℝ) (k : E d → ι),
      (∑ i, m i * c i) = 0 ∧ Measurable k ∧
      (∀ x j, ⟪x, y j⟫ + c j ≤ ⟪x, y (k x)⟫ + c (k x)) ∧
      (∀ i, (uniformMeasure K).real {x | k x = i} = m i) := by
  have hac : uniformMeasure K ≪ (volume : Measure (E d)) :=
    Measure.absolutelyContinuous_restrict.smul_left _
  have hae : ∀ᵐ x ∂uniformMeasure K, x ∈ K :=
    Measure.ae_smul_measure (ae_restrict_mem hK.measurableSet) _
  have hnorm : Integrable (fun x : E d => ‖x‖) (uniformMeasure K) := by
    have hi := ContinuousOn.integrableOn_compact hK continuous_norm.continuousOn
      (μ := uniformMeasure K)
    rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae] at hi
  exact exists_prescribed_cell_masses_of_ac_volume (uniformMeasure K) hac hnorm
    y hinj m hm hsum

end Problem358.MaxPotential

end

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace BigOperators Topology ENNReal

namespace Problem358.MaxPotential

variable {ι V : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V]

/-- Prescribed cell masses yield the supporting inequality for the integrated
potential. This is the elementary subgradient argument, with no differentiation. -/
theorem integral_subgradient_of_cell_masses (ρ : Measure V) [IsFiniteMeasure ρ]
    (y : ι → V) (c a m : ι → ℝ) (k : V → ι)
    (hk : ∀ i, MeasurableSet {x | k x = i})
    (hmax : ∀ᵐ x ∂ρ, ∀ j, ⟪x, y j⟫ + c j ≤ ⟪x, y (k x)⟫ + c (k x))
    (hmass : ∀ i, ρ.real {x | k x = i} = m i)
    (hc : Integrable (potential y c) ρ) (ha : Integrable (potential y a) ρ) :
    (∫ x, potential y c x ∂ρ) + (∑ i, m i * (a i - c i)) ≤
      ∫ x, potential y a x ∂ρ := by
  have hsel := FiniteMaxDerivative.integrable_finite_selection (μ := ρ)
    (fun i => a i - c i) k hk
  have hle : ∀ᵐ x ∂ρ, potential y c x + (a (k x) - c (k x)) ≤ potential y a x := by
    filter_upwards [hmax] with x hx
    rw [affine_eq_potential y c x (k x) hx]
    linarith [affine_le_potential y a x (k x)]
  have hi := integral_mono_ae (hc.add hsel) ha hle
  simp only [Pi.add_apply] at hi
  rw [integral_add hc hsel, FiniteMaxDerivative.integral_finite_selection (fun i => a i - c i) k hk] at hi
  simpa only [hmass] using hi

/-- Every normalized prescribed-mass solution minimizes the normalized objective. -/
theorem isMin_of_cell_masses (ρ : Measure V) [IsFiniteMeasure ρ]
    (y : ι → V) (c m : ι → ℝ) (k : V → ι)
    (hc0 : ∑ i, m i * c i = 0)
    (hk : ∀ i, MeasurableSet {x | k x = i})
    (hmax : ∀ᵐ x ∂ρ, ∀ j, ⟪x, y j⟫ + c j ≤ ⟪x, y (k x)⟫ + c (k x))
    (hmass : ∀ i, ρ.real {x | k x = i} = m i)
    (hint : ∀ a : ι → ℝ, Integrable (potential y a) ρ) :
    ∀ a : ι → ℝ, (∑ i, m i * a i) = 0 →
      (∫ x, potential y c x ∂ρ) ≤ ∫ x, potential y a x ∂ρ := by
  intro a ha0
  have h := integral_subgradient_of_cell_masses ρ y c a m k hk hmax hmass (hint c) (hint a)
  simpa only [mul_sub, Finset.sum_sub_distrib, ha0, hc0, sub_self, add_zero] using h

/-- Prescribed positive masses determine normalized intercepts uniquely for a
connected full-support source. Only affine null ties, not cell calculus, are needed. -/
theorem prescribed_cell_masses_unique (ρ : Measure V) [IsFiniteMeasure ρ] {K : Set V}
    (hK : IsPreconnected K) (hKs : K ⊆ ρ.support) (hKae : ∀ᵐ x ∂ρ, x ∈ K)
    (y : ι → V) (c b m : ι → ℝ) (k l : V → ι)
    (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (hc0 : ∑ i, m i * c i = 0) (hb0 : ∑ i, m i * b i = 0)
    (hk : ∀ i, MeasurableSet {x | k x = i})
    (hl : ∀ i, MeasurableSet {x | l x = i})
    (hmaxc : ∀ᵐ x ∂ρ, ∀ j, ⟪x, y j⟫ + c j ≤ ⟪x, y (k x)⟫ + c (k x))
    (hmaxb : ∀ᵐ x ∂ρ, ∀ j, ⟪x, y j⟫ + b j ≤ ⟪x, y (l x)⟫ + b (l x))
    (hmassc : ∀ i, ρ.real {x | k x = i} = m i)
    (hmassb : ∀ i, ρ.real {x | l x = i} = m i)
    (hties : ∀ᵐ x ∂ρ, ∀ i j, i ≠ j →
      ⟪x, y i⟫ + c i ≠ ⟪x, y j⟫ + c j)
    (hint : ∀ a : ι → ℝ, Integrable (potential y a) ρ) : c = b := by
  apply normalized_minimizer_unique ρ hK hKs hKae y c b m k hsum hc0 hb0 hint
    (isMin_of_cell_masses ρ y c m k hc0 hk hmaxc hmassc hint)
    (isMin_of_cell_masses ρ y b m l hb0 hl hmaxb hmassb hint)
  · filter_upwards [hties, hmaxc] with x hx hmax
    intro j hj
    exact lt_of_le_of_ne (hmax j) (hx j (k x) hj)
  · intro i hz
    have hzero : ρ.real {x | k x = i} = 0 := by simp [measureReal_def, hz]
    have := hm i
    rw [hmassc i] at hzero
    linarith

end Problem358.MaxPotential

end

noncomputable section

open MeasureTheory Filter
open scoped BigOperators RealInnerProductSpace Topology

namespace Problem358.CellGeometry

variable {d : ℕ} {ι : Type*}

/-- On a source contained in a radius-`R` ball, intercept differences of
nonempty cells are controlled by the distance between their sites. This does
not require distinct sites, measurable selectors, or a lower mass bound. -/
theorem abs_intercept_sub_le_of_nonempty_closedCells
    {K : Set (E d)} (y : ι → E d) (c : ι → ℝ) {R : ℝ}
    (hR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hne : ∀ i, (closedCell K y c i).Nonempty) :
    ∀ i j, |c i - c j| ≤ R * ‖y i - y j‖ := by
  have hupper : ∀ i j, c i - c j ≤ R * ‖y i - y j‖ := by
    intro i j
    obtain ⟨x, hx⟩ := hne j
    calc
      c i - c j ≤ ⟪x, y j - y i⟫ := by
        rw [inner_sub_right]
        linarith [hx.2 i]
      _ ≤ ‖x‖ * ‖y j - y i‖ := real_inner_le_norm _ _
      _ ≤ R * ‖y j - y i‖ :=
        mul_le_mul_of_nonneg_right (hR x hx.1) (norm_nonneg _)
      _ = R * ‖y i - y j‖ := by rw [norm_sub_rev]
  intro i j
  refine abs_le.mpr ⟨?_, hupper i j⟩
  have h := hupper j i
  rw [norm_sub_rev (y j) (y i)] at h
  linarith

/-- The preceding estimate applies directly to positive real closed-cell
masses, independently of any argmax selection. -/
theorem abs_intercept_sub_le_of_positive_closedCells
    {K : Set (E d)} (ρ : Measure (E d)) (y : ι → E d) (c : ι → ℝ)
    {R : ℝ} (hR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hpos : ∀ i, 0 < ρ.real (closedCell K y c i)) :
    ∀ i j, |c i - c j| ≤ R * ‖y i - y j‖ := by
  apply abs_intercept_sub_le_of_nonempty_closedCells y c hR
  intro i
  by_contra h
  have hempty : closedCell K y c i = ∅ := Set.not_nonempty_iff_eq_empty.mp h
  have hi := hpos i
  simp [hempty] at hi

/-- Weighted normalization yields a mass-independent compact box for the
actual closed-cell intercept problem. Only nonemptiness of each cell is used. -/
theorem abs_intercept_le_of_normalized_closedCells [Fintype ι]
    {K : Set (E d)} (y : ι → E d) (c m : ι → ℝ) {R L : ℝ}
    (hR : ∀ x ∈ K, ‖x‖ ≤ R) (hL : 0 ≤ L) (hy : ∀ i, ‖y i‖ ≤ L)
    (hne : ∀ i, (closedCell K y c i).Nonempty)
    (hm : ∀ i, 0 ≤ m i) (hsum : ∑ i, m i = 1)
    (hnormal : ∑ i, m i * c i = 0) :
    ∀ i, |c i| ≤ 2 * R * L := by
  apply MaxPotential.abs_intercept_le_of_normalized c m hm hsum hnormal
  apply MaxPotential.abs_intercept_sub_le_of_active y c hL hy
  intro i
  obtain ⟨x, hx⟩ := hne i
  exact ⟨x, hR x hx.1, hx.2⟩

/-- A direct quantitative consequence of prescribed positive closed-cell
masses and normalization, in the spelling used by the actual mass map. -/
theorem abs_intercept_le_of_prescribed_closedCells [Fintype ι]
    {K : Set (E d)} (ρ : Measure (E d)) (y : ι → E d) (c m : ι → ℝ)
    {R L : ℝ} (hR : ∀ x ∈ K, ‖x‖ ≤ R) (hL : 0 ≤ L)
    (hy : ∀ i, ‖y i‖ ≤ L) (hm : ∀ i, 0 < m i)
    (hsum : ∑ i, m i = 1) (hnormal : ∑ i, m i * c i = 0)
    (hmass : ∀ i, ρ.real (closedCell K y c i) = m i) :
    ∀ i, |c i| ≤ 2 * R * L := by
  apply abs_intercept_le_of_normalized_closedCells y c m hR hL hy
    ?_ (fun i => (hm i).le) hsum hnormal
  intro i
  by_contra h
  have hempty : closedCell K y c i = ∅ := Set.not_nonempty_iff_eq_empty.mp h
  have hi := hm i
  rw [← hmass i] at hi
  simp [hempty] at hi

/-- The geometric spread estimate survives coefficient limits, even if sites
collide and individual closed-cell masses cease to be continuous. -/
theorem abs_intercept_sub_le_of_closedCell_limit
    {A : Type*} {l : Filter A} [NeBot l] {K : Set (E d)}
    (y : A → ι → E d) (c : A → ι → ℝ) (y₀ : ι → E d) (c₀ : ι → ℝ)
    {R : ℝ} (hR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hne : ∀ᶠ t in l, ∀ i, (closedCell K (y t) (c t) i).Nonempty)
    (hy : ∀ i, Tendsto (fun t => y t i) l (𝓝 (y₀ i)))
    (hc : ∀ i, Tendsto (fun t => c t i) l (𝓝 (c₀ i))) :
    ∀ i j, |c₀ i - c₀ j| ≤ R * ‖y₀ i - y₀ j‖ := by
  intro i j
  apply le_of_tendsto_of_tendsto ((hc i).sub (hc j)).abs
    (tendsto_const_nhds.mul ((hy i).sub (hy j)).norm)
  filter_upwards [hne] with t ht
  exact abs_intercept_sub_le_of_nonempty_closedCells (y t) (c t) hR ht i j

/-- In a limit of nonempty fixed-source cells, colliding sites necessarily
have equal intercepts. Endpoint coalescence therefore needs no choice of a
largest intercept among these repeated slopes. -/
theorem intercept_eq_of_eq_site_of_closedCell_limit
    {A : Type*} {l : Filter A} [NeBot l] {K : Set (E d)}
    (y : A → ι → E d) (c : A → ι → ℝ) (y₀ : ι → E d) (c₀ : ι → ℝ)
    {R : ℝ} (hR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hne : ∀ᶠ t in l, ∀ i, (closedCell K (y t) (c t) i).Nonempty)
    (hy : ∀ i, Tendsto (fun t => y t i) l (𝓝 (y₀ i)))
    (hc : ∀ i, Tendsto (fun t => c t i) l (𝓝 (c₀ i)))
    {i j : ι} (hij : y₀ i = y₀ j) : c₀ i = c₀ j := by
  have h := abs_intercept_sub_le_of_closedCell_limit y c y₀ c₀ hR hne hy hc i j
  simpa only [hij, sub_self, norm_zero, mul_zero, abs_nonpos_iff, sub_eq_zero] using h

end Problem358.CellGeometry

end

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace BigOperators

namespace Problem358.MaxPotential

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- On a compact convex body, positive prescribed masses and weighted normalization
uniquely determine the intercepts of distinct affine sites. -/
theorem uniform_prescribed_cell_masses_unique {d : ℕ} {K : Set (E d)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : (interior K).Nonempty)
    (y : ι → E d) (hy : Function.Injective y) (c b m : ι → ℝ) (k l : E d → ι)
    (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (hc0 : ∑ i, m i * c i = 0) (hb0 : ∑ i, m i * b i = 0)
    (hk : ∀ i, MeasurableSet {x | k x = i})
    (hl : ∀ i, MeasurableSet {x | l x = i})
    (hmaxc : ∀ᵐ x ∂uniformMeasure K, ∀ j,
      ⟪x, y j⟫ + c j ≤ ⟪x, y (k x)⟫ + c (k x))
    (hmaxb : ∀ᵐ x ∂uniformMeasure K, ∀ j,
      ⟪x, y j⟫ + b j ≤ ⟪x, y (l x)⟫ + b (l x))
    (hmassc : ∀ i, (uniformMeasure K).real {x | k x = i} = m i)
    (hmassb : ∀ i, (uniformMeasure K).real {x | l x = i} = m i) : c = b := by
  let := UniformSource.probability hK hne
  apply prescribed_cell_masses_unique (uniformMeasure K) hconv.isPreconnected
    (UniformSource.subset_support hK hconv hne) (UniformSource.ae_mem hK.measurableSet)
    y c b m k l hm hsum hc0 hb0 hk hl hmaxc hmaxb hmassc hmassb
  · filter_upwards [uniform_ae_affine_tie_implies_slopes_eq K y c] with x hx
    intro i j hij heq
    exact hij (hy (hx i j heq))
  · intro a
    exact UniformSource.integrable_continuousOn hK (continuous_potential y a).continuousOn

end Problem358.MaxPotential

namespace Problem358.MaxPotential

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- For distinct sites and positive normalized weights the normalized uniform-source
variational objective has at most one minimizer. All geometric hypotheses are concrete. -/
theorem uniform_normalized_minimizer_unique {d : ℕ} {K : Set (E d)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : (interior K).Nonempty)
    (y : ι → E d) (hy : Function.Injective y) (m : ι → ℝ)
    (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (c b : ι → ℝ) (hc0 : ∑ i, m i * c i = 0) (hb0 : ∑ i, m i * b i = 0)
    (hcmin : ∀ a : ι → ℝ, (∑ i, m i * a i) = 0 →
      (∫ x, potential y c x ∂uniformMeasure K) ≤ ∫ x, potential y a x ∂uniformMeasure K)
    (hbmin : ∀ a : ι → ℝ, (∑ i, m i * a i) = 0 →
      (∫ x, potential y b x ∂uniformMeasure K) ≤ ∫ x, potential y a x ∂uniformMeasure K) :
    c = b := by
  classical
  let : MeasurableSpace ι := ⊤
  let := UniformSource.probability hK hne
  have htie : ∀ a : ι → ℝ, ∀ᵐ x ∂uniformMeasure K, ∀ i j, i ≠ j →
      ⟪x, y i⟫ + a i ≠ ⟪x, y j⟫ + a j := by
    intro a
    filter_upwards [uniform_ae_affine_tie_implies_slopes_eq K y a] with x hx
    intro i j hij heq
    exact hij (hy (hx i j heq))
  obtain ⟨a, k, ha0, hk, hmax, hmass⟩ := exists_prescribed_cell_masses
    (uniformMeasure K) y m hm hsum ‖y‖₊ (fun i => norm_le_pi_norm y i)
    (UniformSource.integrable_norm hK) htie
  have hfib : ∀ i, MeasurableSet {x | k x = i} := by
    intro i
    exact hk (measurableSet_singleton i)
  have hint : ∀ a' : ι → ℝ, Integrable (potential y a') (uniformMeasure K) :=
    fun a' => UniformSource.integrable_continuousOn hK (continuous_potential y a').continuousOn
  have hamin := isMin_of_cell_masses (uniformMeasure K) y a m k ha0 hfib
    (Filter.Eventually.of_forall hmax) hmass hint
  have hstrict : ∀ᵐ x ∂uniformMeasure K, ∀ j, j ≠ k x →
      ⟪x, y j⟫ + a j < ⟪x, y (k x)⟫ + a (k x) := by
    filter_upwards [htie a] with x hx
    intro j hj
    exact lt_of_le_of_ne (hmax x j) (hx j (k x) hj)
  have hpos : ∀ i, (uniformMeasure K) {x | k x = i} ≠ 0 := by
    intro i hz
    have hz' : (uniformMeasure K).real {x | k x = i} = 0 := by simp [measureReal_def, hz]
    rw [hmass i] at hz'
    exact (ne_of_gt (hm i)) hz'
  have huniq (z : ι → ℝ) (hz0 : ∑ i, m i * z i = 0)
      (hzmin : ∀ a' : ι → ℝ, (∑ i, m i * a' i) = 0 →
        (∫ x, potential y z x ∂uniformMeasure K) ≤ ∫ x, potential y a' x ∂uniformMeasure K) :
      a = z :=
    normalized_minimizer_unique (uniformMeasure K) hconv.isPreconnected
      (UniformSource.subset_support hK hconv hne) (UniformSource.ae_mem hK.measurableSet)
      y a z m k hsum ha0 hz0 hint hamin hzmin hstrict hpos
  exact (huniq c hc0 hcmin).symm.trans (huniq b hb0 hbmin)

end Problem358.MaxPotential

end

end OAI
