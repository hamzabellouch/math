import OAI.Analysis.Brenier.Laplacian
import OAI.Analysis.Brenier.PrescribedCells

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators RealInnerProductSpace Topology ContDiff

namespace Problem358.FixedMassIntercepts

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- The actual closed-cell mass vector, without a choice of maximizing selector. -/
def masses (K : Set (E d)) (y : ι → E d) (c : ι → ℝ) : ι → ℝ :=
  fun i => (uniformMeasure K).real (CellGeometry.closedCell K y c i)

/-- Null ties identify every maximizing selector's fibers with the closed cells. -/
theorem closedCell_ae_eq_selector {K : Set (E d)} (hK : MeasurableSet K)
    (y : ι → E d) (hy : Function.Injective y) (c : ι → ℝ)
    (k : E d → ι)
    (hk : ∀ x j, ⟪x, y j⟫ + c j ≤ ⟪x, y (k x)⟫ + c (k x)) (i : ι) :
    CellGeometry.closedCell K y c i =ᵐ[uniformMeasure K] {x | k x = i} := by
  filter_upwards [UniformSource.ae_mem hK,
    uniform_ae_affine_tie_implies_slopes_eq K y c] with x hx ht
  apply propext
  change (x ∈ K ∧ ∀ j, ⟪x, y j⟫ + c j ≤ ⟪x, y i⟫ + c i) ↔ k x = i
  constructor
  · intro hc
    apply hy
    exact ht (k x) i (le_antisymm (hc.2 (k x)) (hk x i))
  · intro hi
    exact ⟨hx, fun j => by simpa only [hi] using hk x j⟩

/-- The selector law and geometric closed-cell masses have exactly the same real masses. -/
theorem masses_eq_selector {K : Set (E d)} (hK : MeasurableSet K)
    (y : ι → E d) (hy : Function.Injective y) (c : ι → ℝ)
    (k : E d → ι)
    (hk : ∀ x j, ⟪x, y j⟫ + c j ≤ ⟪x, y (k x)⟫ + c (k x)) (i : ι) :
    masses K y c i = (uniformMeasure K).real {x | k x = i} := by
  exact congrArg ENNReal.toReal
    (measure_congr (closedCell_ae_eq_selector hK y hy c k hk i))

variable [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- Prescribed positive masses uniquely determine a normalized intercept vector.
This is an actual existence and uniqueness result for the geometric cells; it has
no cell-differentiability hypothesis. -/
theorem existsUnique_normalized {K : Set (E d)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : (interior K).Nonempty)
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (y : ι → E d) (hy : Function.Injective y) :
    ∃! c : CellLaplacian.normalizedSpace m, masses K y c = m := by
  let := UniformSource.probability hK hne
  obtain ⟨c, k, hc, hk, hmax, hmass⟩ :=
    MaxPotential.exists_prescribed_cell_masses_uniform K hK y hy m hm hsum
  have hcm : masses K y c = m := by
    funext i
    exact (masses_eq_selector hK.measurableSet y hy c k hmax i).trans (hmass i)
  refine ⟨⟨c, hc⟩, hcm, ?_⟩
  intro b hb
  obtain ⟨l, hl, _, hlmax⟩ := exists_measurable_argmax
    (fun i (x : E d) => ⟪x, y i⟫ + (b : ι → ℝ) i)
    (fun i => ((continuous_id.inner continuous_const).add continuous_const).measurable)
  apply Subtype.ext
  apply MaxPotential.uniform_prescribed_cell_masses_unique hK hconv hne
    y hy b c m l k hm hsum b.property hc
    (fun i => hl (measurableSet_singleton i))
    (fun i => hk (measurableSet_singleton i))
    (Eventually.of_forall hlmax) (Eventually.of_forall hmax)
  · intro i
    exact (masses_eq_selector hK.measurableSet y hy b l hlmax i).symm.trans
      (congrFun hb i)
  · exact hmass

/-- The canonical normalized intercept vector. It is zero on configurations with
repeated sites; all uses of the prescribed-mass specification have distinct sites. -/
def intercepts {K : Set (E d)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : (interior K).Nonempty)
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (y : ι → E d) : CellLaplacian.normalizedSpace m :=
  if hy : Function.Injective y then
    (existsUnique_normalized hK hconv hne m hm hsum y hy).choose
  else 0

theorem intercepts_spec {K : Set (E d)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : (interior K).Nonempty)
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (y : ι → E d) (hy : Function.Injective y) :
    masses K y (intercepts hK hconv hne m hm hsum y) = m := by
  simp only [intercepts, dite_eq_left hy]
  exact (existsUnique_normalized hK hconv hne m hm hsum y hy).choose_spec.1

theorem eq_intercepts {K : Set (E d)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : (interior K).Nonempty)
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (y : ι → E d) (hy : Function.Injective y)
    (c : CellLaplacian.normalizedSpace m) (hc : masses K y c = m) :
    c = intercepts hK hconv hne m hm hsum y := by
  exact (existsUnique_normalized hK hconv hne m hm hsum y hy).unique hc
    (intercepts_spec hK hconv hne m hm hsum y hy)

end Problem358.FixedMassIntercepts

end

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff

namespace Problem358.CellGeometry

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- The actual closed-cell masses, restricted to normalized intercepts. -/
def normalizedMassMap (K : Set (E d)) (m : ι → ℝ) :
    ((ι → E d) × CellLaplacian.normalizedSpace m) → (ι → ℝ) :=
  fun p i => (uniformMeasure K).real (closedCell K p.1 p.2 i)

/-- Distinctness of finitely many sites persists on a neighborhood. -/
theorem eventually_injective_sites {y : ι → E d} (hy : Function.Injective y) :
    ∀ᶠ z in 𝓝 y, Function.Injective z := by
  classical
  simp only [Function.Injective, Filter.eventually_all]
  intro i j
  by_cases hij : i = j
  · exact Filter.Eventually.of_forall (fun _ _ => hij)
  · have hn : ∀ᶠ z in 𝓝 y, z i ≠ z j :=
      (isClosed_eq (continuous_apply i) (continuous_apply j)).isOpen_compl.mem_nhds (hy.ne hij)
    exact hn.mono (fun z hz heq => (hz heq).elim)

/-- The coordinate mass map takes values in probability vectors whenever the
sites are distinct. This is derived from the actual closed-cell partition. -/
theorem sum_normalizedMassMap [Nonempty ι] {K : Set (E d)} (hK : IsCompact K)
    (hne : (interior K).Nonempty) (m : ι → ℝ)
    (p : (ι → E d) × CellLaplacian.normalizedSpace m)
    (hy : Function.Injective p.1) :
    ∑ i, normalizedMassMap K m p i = 1 := by
  let := UniformSource.probability hK hne
  have hρ : uniformMeasure K ≪ (volume : Measure (E d)) :=
    Measure.absolutelyContinuous_restrict.smul_left _
  have hmass : uniformMeasure K K = 1 := by
    calc
      uniformMeasure K K = uniformMeasure K Set.univ := by
        apply measure_congr
        filter_upwards [UniformSource.ae_mem hK.measurableSet] with x hx
        exact propext ⟨fun _ => Set.mem_univ x, fun _ => hx⟩
      _ = 1 := measure_univ
  have h := sum_real_measure_closedCell hρ hK.isClosed p.1 p.2 hy
  simpa only [normalizedMassMap, Measure.real, hmass, ENNReal.toReal_one] using h

/-- The normalized mass residual vanishes exactly at the prescribed physical
closed-cell masses, without a selector or residual-range assumption. -/
theorem normalizedMassResidual_eq_zero_iff [Nonempty ι] {K : Set (E d)} (hK : IsCompact K)
    (hne : (interior K).Nonempty) (m : ι → ℝ) (hm : ∑ i, m i = 1)
    (p : (ι → E d) × CellLaplacian.normalizedSpace m)
    (hy : Function.Injective p.1) :
    CellLaplacian.massResidual m hm (normalizedMassMap K m) p = 0 ↔
      ∀ i, (uniformMeasure K).real (closedCell K p.1 p.2 i) = m i := by
  rw [CellLaplacian.massResidual_eq_zero_iff m hm _ p
    (sum_normalizedMassMap hK hne m p hy)]
  exact funext_iff

/-- Include the normalization hyperplane into the unrestricted configuration space. -/
def normalizedConfigInclusion (m : ι → ℝ) :
    ((ι → E d) × CellLaplacian.normalizedSpace m) →L[ℝ] ((ι → E d) × (ι → ℝ)) :=
  (ContinuousLinearMap.id ℝ (ι → E d)).prodMap (CellLaplacian.normalizedSpace m).subtypeL

@[simp] theorem normalizedConfigInclusion_apply (m : ι → ℝ)
    (p : (ι → E d) × CellLaplacian.normalizedSpace m) :
    normalizedConfigInclusion m p = (p.1, (p.2 : ι → ℝ)) := rfl

/-- Restrict geometric C¹ regularity on ordinary site/intercept coordinates to
the weighted normalization hyperplane used by the implicit function theorem. -/
theorem contDiffAt_normalizedMassMap_of_raw {K : Set (E d)} (m : ι → ℝ)
    (p : (ι → E d) × CellLaplacian.normalizedSpace m)
    (hM : ContDiffAt ℝ 1
      (fun z : (ι → E d) × (ι → ℝ) => fun i =>
        (uniformMeasure K).real (closedCell K z.1 z.2 i))
      (p.1, (p.2 : ι → ℝ))) :
    ContDiffAt ℝ 1 (normalizedMassMap K m) p :=
  hM.comp p (normalizedConfigInclusion m).contDiff.contDiffAt

/-- The normalized mass derivative is the unrestricted geometric derivative
composed with the actual hyperplane inclusion. -/
theorem hasFDerivAt_normalizedMassMap_of_raw {K : Set (E d)} (m : ι → ℝ)
    (p : (ι → E d) × CellLaplacian.normalizedSpace m)
    (A : ((ι → E d) × (ι → ℝ)) →L[ℝ] (ι → ℝ))
    (hD : HasFDerivAt
      (fun z : (ι → E d) × (ι → ℝ) => fun i =>
        (uniformMeasure K).real (closedCell K z.1 z.2 i)) A
      (p.1, (p.2 : ι → ℝ))) :
    HasFDerivAt (normalizedMassMap K m) (A ∘L normalizedConfigInclusion m) p := by
  have h := hD.comp p ((normalizedConfigInclusion (d := d) m).hasFDerivAt (x := p))
  exact h

end Problem358.CellGeometry

end

noncomputable section

open MeasureTheory
open scoped BigOperators ContDiff

namespace Problem358

namespace CellLaplacian

variable {ι : Type*} [Fintype ι] [Subsingleton ι]

/-- For one site, the weighted normalization hyperplane is the zero space.
This uses only the total mass, and does not need positivity or a graph lemma. -/
theorem normalizedSpace_eq_zero_of_subsingleton (m : ι → ℝ)
    (hsum : ∑ i, m i = 1) (q : normalizedSpace m) : q = 0 := by
  apply Subtype.ext
  funext i
  have hmean : ∑ j, m j * (q : ι → ℝ) j = 0 := q.property
  have hconst (j : ι) : (q : ι → ℝ) j = (q : ι → ℝ) i :=
    congrArg (fun k => (q : ι → ℝ) k) (Subsingleton.elim j i)
  simp_rw [hconst] at hmean
  rw [← Finset.sum_mul, hsum, one_mul] at hmean
  exact hmean

theorem subsingleton_normalizedSpace (m : ι → ℝ) (hsum : ∑ i, m i = 1) :
    Subsingleton (normalizedSpace m) := by
  refine ⟨fun q r => ?_⟩
  exact (normalizedSpace_eq_zero_of_subsingleton m hsum q).trans
    (normalizedSpace_eq_zero_of_subsingleton m hsum r).symm

end CellLaplacian

namespace CellGeometry

/-- A one-site closed affine cell is the entire source set. -/
theorem closedCell_eq_of_subsingleton {d : ℕ} {ι : Type*} [Subsingleton ι]
    (K : Set (E d)) (y : ι → E d) (c : ι → ℝ) (i : ι) :
    closedCell K y c i = K := by
  ext x
  constructor
  · exact fun hx => hx.1
  · intro hx
    refine ⟨hx, fun j => ?_⟩
    rw [Subsingleton.elim j i]

end CellGeometry

namespace FixedMassIntercepts

variable {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι] [Subsingleton ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- The actual globally selected normalized intercept is zero for a one-site target. -/
@[simp] theorem intercepts_eq_zero_of_subsingleton {K : Set (E d)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : (interior K).Nonempty)
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (y : ι → E d) : intercepts hK hconv hne m hm hsum y = 0 :=
  CellLaplacian.normalizedSpace_eq_zero_of_subsingleton m hsum _

/-- The one-site intercept selection is smooth independently of any cell calculus. -/
theorem contDiff_intercepts_of_subsingleton {K : Set (E d)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : (interior K).Nonempty)
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (n : ℕ∞ω) : ContDiff ℝ n (intercepts hK hconv hne m hm hsum) := by
  have heq : intercepts hK hconv hne m hm hsum =
      fun _ => (0 : CellLaplacian.normalizedSpace m) := by
    funext y
    exact intercepts_eq_zero_of_subsingleton hK hconv hne m hm hsum y
  rw [heq]
  exact contDiff_const

/-- Even an arbitrary site path gives a constant normalized intercept path if there
is only one site.  In particular its intercept energy is exactly zero. -/
theorem hasDerivAt_intercepts_path_of_subsingleton {K : Set (E d)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : (interior K).Nonempty)
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (y : ℝ → ι → E d) (t : ℝ) :
    HasDerivAt (fun s => intercepts hK hconv hne m hm hsum (y s)) 0 t := by
  simpa only [intercepts_eq_zero_of_subsingleton] using
    (hasDerivAt_const t (0 : CellLaplacian.normalizedSpace m))

end FixedMassIntercepts

end Problem358

end

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff

namespace Problem358.FixedMassIntercepts

variable {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- The actual canonical prescribed-mass intercepts are C¹ at each distinct-site
configuration where the geometric mass map is C¹ with its connected cell Laplacian
as intercept derivative.  Neither continuity nor uniqueness of a chosen branch is
assumed: both are supplied by the geometric closed-cell construction. -/
theorem contDiffAt_intercepts_of_massDifferential {K : Set (E d)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : (interior K).Nonempty)
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (y : ι → E d) (hy : Function.Injective y)
    (g : ι → ι → ℝ) (hsym : ∀ i j, g i j = g j i)
    (hnonneg : ∀ i j, 0 ≤ g i j) (G : SimpleGraph ι)
    (hG : G.Connected) (hpos : ∀ i j, G.Adj i j → 0 < g i j)
    (A : ((ι → E d) × CellLaplacian.normalizedSpace m) →L[ℝ] (ι → ℝ))
    (hM : ContDiffAt ℝ 1 (CellGeometry.normalizedMassMap K m)
      (y, intercepts hK hconv hne m hm hsum y))
    (hD : HasFDerivAt (CellGeometry.normalizedMassMap K m) A
      (y, intercepts hK hconv hne m hm hsum y))
    (hA : ∀ q : CellLaplacian.normalizedSpace m, A (0, q) = CellLaplacian.apply g q) :
    ContDiffAt ℝ 1 (intercepts hK hconv hne m hm hsum) y := by
  let s := intercepts hK hconv hne m hm hsum
  let F := CellLaplacian.massResidual m hsum (CellGeometry.normalizedMassMap K m)
  have hF : ContDiffAt ℝ 1 F (y, s y) :=
    CellLaplacian.contDiffAt_massResidual m hsum hM
  have hDF := CellLaplacian.hasFDerivAt_massResidual m hsum hD
  have hpartial : fderiv ℝ F (y, s y) ∘L
      ContinuousLinearMap.inr ℝ (ι → E d) (CellLaplacian.normalizedSpace m) =
      (CellLaplacian.normalizedEquiv g hsym hnonneg G hG hpos m hsum).toContinuousLinearMap := by
    rw [show fderiv ℝ F (y, s y) = (CellLaplacian.zeroSumProjection m hsum) ∘L A from hDF.fderiv]
    exact CellLaplacian.massResidual_partial_eq g hsym hnonneg G hG hpos m hsum A hA
  have hzero : F (y, s y) = 0 := by
    apply (CellGeometry.normalizedMassResidual_eq_zero_iff hK hne m hsum (y, s y) hy).mpr
    exact fun i => congrFun (intercepts_spec hK hconv hne m hm hsum y hy) i
  have hunique : ∀ᶠ z in 𝓝 y, ∀ c, F (z, c) = 0 → c = s z := by
    filter_upwards [CellGeometry.eventually_injective_sites hy] with z hz
    intro c hc
    apply eq_intercepts hK hconv hne m hm hsum z hz c
    exact funext ((CellGeometry.normalizedMassResidual_eq_zero_iff hK hne m hsum (z, c) hz).mp hc)
  exact CellLaplacian.contDiffAt_normalized_solution (by norm_num) g hsym hnonneg G hG hpos
    m hsum F s y hF hpartial hzero hunique

/-- Along a differentiable site path, the actual canonical intercept derivative
satisfies the differentiated fixed-mass constraint. Its weighted mean vanishes
because it belongs to the normalization subspace. -/
theorem hasDerivAt_intercepts_comp_and_mass_constraint {K : Set (E d)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : (interior K).Nonempty)
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (Y : ℝ → (ι → E d)) (v : ι → E d) (t : ℝ)
    (hY : HasDerivAt Y v t) (hy : Function.Injective (Y t))
    (hs : DifferentiableAt ℝ (intercepts hK hconv hne m hm hsum) (Y t))
    (A : ((ι → E d) × CellLaplacian.normalizedSpace m) →L[ℝ] (ι → ℝ))
    (hD : HasFDerivAt (CellGeometry.normalizedMassMap K m) A
      (Y t, intercepts hK hconv hne m hm hsum (Y t))) :
    let c := fun q => intercepts hK hconv hne m hm hsum (Y q)
    HasDerivAt c (deriv c t) t ∧ A (v, deriv c t) = 0 ∧
      ∑ i, m i * (↑(deriv c t : CellLaplacian.normalizedSpace m) : ι → ℝ) i = 0 := by
  let c := fun q => intercepts hK hconv hne m hm hsum (Y q)
  have hdc : HasDerivAt c (deriv c t) t :=
    (hs.comp t hY.differentiableAt).hasDerivAt
  refine ⟨hdc, ?_, (deriv c t).property⟩
  have hcomp := hD.comp_hasDerivAt t (hY.prodMk hdc)
  have heq : (fun q => CellGeometry.normalizedMassMap K m (Y q, c q)) =ᶠ[𝓝 t]
      (fun _ => m) := by
    filter_upwards [hY.continuousAt.eventually (CellGeometry.eventually_injective_sites hy)] with q hq
    exact intercepts_spec hK hconv hne m hm hsum (Y q) hq
  exact hcomp.unique ((hasDerivAt_const t m).congr_of_eventuallyEq heq)

/-- Coordinate form of the fixed-mass derivative equation. This is the actual
constraint consumed by the symmetric flux / intercept energy calculation. -/
theorem laplacian_intercepts_comp_deriv {K : Set (E d)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : (interior K).Nonempty)
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (Y : ℝ → (ι → E d)) (v : ι → E d) (t : ℝ)
    (hY : HasDerivAt Y v t) (hy : Function.Injective (Y t))
    (hs : DifferentiableAt ℝ (intercepts hK hconv hne m hm hsum) (Y t))
    (A : ((ι → E d) × CellLaplacian.normalizedSpace m) →L[ℝ] (ι → ℝ))
    (hD : HasFDerivAt (CellGeometry.normalizedMassMap K m) A
      (Y t, intercepts hK hconv hne m hm hsum (Y t)))
    (g : ι → ι → ℝ)
    (hA : ∀ q : CellLaplacian.normalizedSpace m, A (0, q) = CellLaplacian.apply g q) :
    CellLaplacian.apply g
      (↑(deriv (fun q => intercepts hK hconv hne m hm hsum (Y q)) t :
        CellLaplacian.normalizedSpace m) : ι → ℝ) =
      -A (v, 0) := by
  let c := fun q => intercepts hK hconv hne m hm hsum (Y q)
  have hz := (hasDerivAt_intercepts_comp_and_mass_constraint hK hconv hne m hm hsum
    Y v t hY hy hs A hD).2.1
  have hsplit : A (v, deriv c t) = A (v, 0) + A (0, deriv c t) := by
    rw [← map_add]
    simp only [Prod.mk_add_mk, add_zero, zero_add]
  rw [hsplit, hA] at hz
  exact eq_neg_of_add_eq_zero_right hz

end Problem358.FixedMassIntercepts

end

end OAI
