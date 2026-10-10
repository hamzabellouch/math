import Mathlib
import OAI.Analysis.Conductivity.Fourier.PeriodicAveragingSmooth
import OAI.Analysis.Conductivity.Walls.SmoothCutoffSmallMargin
import OAI.Analysis.Conductivity.Variational.MatrixOperator

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Set

lemma exists_coordinate_nonzero {L : Coord3 →L[ℝ] ℝ} (hL : L ≠ 0) :
    ∃ i, L (Pi.single i 1) ≠ 0 := by
  by_contra hn
  have hz : ∀ i, L (Pi.single i 1) = 0 := by simpa only [not_exists, not_not] using hn
  apply hL
  ext x
  have hx : x = ∑ i : Fin 3, x i • Pi.single i 1 := by
    ext j
    simp [Pi.single_apply]
  rw [hx, map_sum]
  simp [hz]

def pairedPotential (u : Coord3 → ℝ) (j : Fin 3) (x : Coord3) : Fin 2 → ℝ :=
  ![u x, x j]

def pairedFunctional (L : Coord3 →L[ℝ] ℝ) (j : Fin 3) : Coord3 →L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearMap.pi ![L, ContinuousLinearMap.proj j]

lemma pairedPotential_hasFDerivAt {u : Coord3 → ℝ} {p : Coord3}
    {L : Coord3 →L[ℝ] ℝ} (hu : HasFDerivAt u L p) (j : Fin 3) :
    HasFDerivAt (pairedPotential u j) (pairedFunctional L j) p := by
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hu
  · exact (ContinuousLinearMap.proj j : Coord3 →L[ℝ] ℝ).hasFDerivAt

lemma pairedPotential_contDiff {u : Coord3 → ℝ}
    (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u) (j : Fin 3) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (pairedPotential u j) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact hu
  · exact contDiff_apply ℝ ℝ j

lemma pairedFunctional_surjective {L : Coord3 →L[ℝ] ℝ} {i j : Fin 3}
    (hi : L (Pi.single i 1) ≠ 0) (hij : i ≠ j) :
    Function.Surjective (pairedFunctional L j) := by
  intro v
  let x : Coord3 := ((v 0 - L (Pi.single j 1) * v 1) / L (Pi.single i 1)) •
    Pi.single i 1 + v 1 • Pi.single j 1
  refine ⟨x, ?_⟩
  ext k
  fin_cases k
  · change L x = v 0
    simp only [x, map_add, map_smul, smul_eq_mul]
    field_simp
    ring
  · change x j = v 1
    simp [x, Ne.symm hij]

lemma exists_independent_pairedPotential {u : Coord3 → ℝ}
    (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u) (p : Coord3) (hp : fderiv ℝ u p ≠ 0) :
    ∃ j : Fin 3, Function.Surjective (fderiv ℝ (pairedPotential u j) p) := by
  obtain ⟨i, hi⟩ := exists_coordinate_nonzero hp
  obtain ⟨j, hji⟩ := exists_ne i
  refine ⟨j, ?_⟩
  rw [(pairedPotential_hasFDerivAt ((hu.differentiable (by simp)).differentiableAt.hasFDerivAt) j).fderiv]
  exact pairedFunctional_surjective hi hji.symm

end ScalarConductivity

namespace ScalarConductivity
open MeasureTheory Set Filter Topology
open scoped Manifold ENNReal

lemma exists_smooth_compact_majorant
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Set E} (hK : IsCompact K) :
    ∃ f : SmoothScalar E, HasCompactSupport f.val ∧
      (∀ x, 0 ≤ f.val x ∧ f.val x ≤ 1) ∧ ∀ x ∈ K, f.val x = 1 := by
  obtain ⟨r, hr⟩ := hK.isBounded.subset_ball (0 : E)
  obtain ⟨f, hf₀, hf₁, hfb⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed (𝓘(ℝ, E))
    Metric.isOpen_ball.isClosed_compl hK.isClosed
    (disjoint_left.mpr (fun _ hx hxK => hx (hr hxK))) (n := ⊤)
  have ht : tsupport (f : E → ℝ) ⊆ Metric.ball 0 r := by
    intro x hx
    by_contra hxU
    exact (notMem_tsupport_iff_eventuallyEq.mpr
      (hf₀.filter_mono (nhds_le_nhdsSet hxU))) hx
  refine ⟨⟨f, contMDiff_iff_contDiff.mp f.contMDiff⟩, ?_, hfb, ?_⟩
  · exact (Metric.isBounded_ball.subset ht).isCompact_closure.of_isClosed_subset
      (isClosed_tsupport _) subset_closure
  · intro x hx
    exact (hf₁.filter_mono (nhds_le_nhdsSet hx)).self_of_nhds

lemma chart_pullback_measure_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (X : OpenPartialHomeomorph E E) {V : Set E} (hVX : V ⊆ X.source)
    (hXi : DifferentiableOn ℝ X.symm X.target)
    {C : ℝ} (hC : ∀ y ∈ X '' V, |(fderiv ℝ X.symm y).det| ≤ C)
    {s : Set E} (hs : MeasurableSet s) (hsV : s ⊆ X '' V) :
    μ {x | x ∈ V ∧ X x ∈ s} ≤ ENNReal.ofReal C * μ s := by
  have hsX : s ⊆ X.target := hsV.trans (by
    rintro y ⟨x, hx, rfl⟩; exact X.map_source (hVX hx))
  have he : X.symm '' s = {x | x ∈ V ∧ X x ∈ s} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, hz, hyz⟩ := hsV hy
      subst y
      rw [X.left_inv (hVX hz)]
      exact ⟨hz, hy⟩
    · intro hx
      exact ⟨X x, hx.2, X.left_inv (hVX hx.1)⟩
  rw [← he]
  exact measure_image_le_det μ hs
    (fun y hy => (hXi y (hsX hy)).differentiableAt (X.open_target.mem_nhds (hsX hy)))
    (X.symm.injOn.mono hsX) (fun y hy => hC y (hsV hy))

theorem exists_chart_pure_profile
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (X : OpenPartialHomeomorph E E) {V : Set E} (hV : IsOpen V) (hVX : V ⊆ X.source)
    (hXi : DifferentiableOn ℝ X.symm X.target)
    (hSb : Bornology.IsBounded (X '' V)) (hμS : μ (X '' V) ≠ ∞)
    {C : ℝ} (hCpos : 0 < C) (hC : ∀ y ∈ X '' V, |(fderiv ℝ X.symm y).det| ≤ C)
    (L : E →L[ℝ] ℝ) (hL : L ≠ 0) {θ ε : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hε : 0 < ε) :
    ∃ (χ : SmoothScalar E) (H : SmoothScalar ℝ),
      HasCompactSupport χ.val ∧ tsupport χ.val ⊆ X '' V ∧
      (∀ x, 0 ≤ χ.val x ∧ χ.val x ≤ 1) ∧
      Function.Periodic (smoothDirection 1 H).val 1 ∧
      (∫ t in (0 : ℝ)..1, (smoothDirection 1 H).val t) = 0 ∧
      (∃ b : ℝ, ∀ t, |H.val t| ≤ b) ∧
      (∀ t, -θ ≤ (smoothDirection 1 H).val t ∧
        (smoothDirection 1 H).val t ≤ 1-θ) ∧
      ∀ᶠ n : ℕ in atTop,
        μ {x | x ∈ V ∧
          localPullback X χ.val x * (smoothDirection 1 H).val ((n+1 : ℝ) * L (X x)) ≠ -θ ∧
          localPullback X χ.val x * (smoothDirection 1 H).val ((n+1 : ℝ) * L (X x)) ≠ 1-θ} ≤
          ENNReal.ofReal ε := by
  let η := ε / (4*C)
  have hη : 0 < η := by dsimp [η]; positivity
  have hS : IsOpen (X '' V) := X.isOpen_image_of_subset_source hV hVX
  obtain ⟨χ, hχs, hχc, hχV, hχb, hmargin⟩ := exists_smooth_cutoff_small_margin μ hS hSb hμS
    (ne_of_gt (ENNReal.ofReal_pos.mpr hη))
  let χ' : SmoothScalar E := ⟨χ, hχs⟩
  obtain ⟨f, hfc, hfb, hfS⟩ := exists_smooth_compact_majorant hSb.isCompact_closure
  obtain ⟨δ, hδ, hδθ, hw, hδw, hδη⟩ := exists_transition_width hθ hθ1 hη
    (M := ∫ x, f.val x ∂μ)
  obtain ⟨H, hHder, hHp, hHm, hHb, hHr⟩ := exists_two_state_primitive hδ hδθ hw
  refine ⟨χ', H, hχc, hχV, hχb, hHp, hHm, hHb, hHr, ?_⟩
  have hpure := eventually_impure_measure_le μ L hL f hfc (fun x => (hfb x).1)
    (X '' V) (fun x hx => (hfS x (subset_closure hx)).ge) hδ hδθ hw hδw hδη
  have hcm : μ {x | x ∈ V ∧ χ (X x) ≠ 1} ≤ ENNReal.ofReal C * ENNReal.ofReal η := by
    have hcmeas : MeasurableSet {y | y ∈ X '' V ∧ χ y ≠ 1} :=
      hS.measurableSet.inter (isOpen_ne.preimage hχs.continuous).measurableSet
    have hh := chart_pullback_measure_le μ X hVX hXi hC hcmeas (fun _ hy => hy.1)
    have hset : {x | x ∈ V ∧ X x ∈ {y | y ∈ X '' V ∧ χ y ≠ 1}} =
        {x | x ∈ V ∧ χ (X x) ≠ 1} := by
      ext x
      exact ⟨fun hx => ⟨hx.1, hx.2.2⟩, fun hx => ⟨hx.1, ⟨x, hx.1, rfl⟩, hx.2⟩⟩
    rw [hset] at hh
    exact hh.trans (mul_le_mul_right hmargin.le _)
  filter_upwards [hpure] with n hn
  have himpure := (chart_impure_measure_le μ X L hV hVX hXi hC θ δ (n+1) hθ.le hδ).trans
    (mul_le_mul_right hn (ENNReal.ofReal C))
  calc
    _ ≤ μ ({x | x ∈ V ∧ χ (X x) ≠ 1} ∪
        {x | x ∈ V ∧ periodicPulse θ δ ((n+1 : ℝ) * L (X x)) ≠ 0 ∧
          periodicPulse θ δ ((n+1 : ℝ) * L (X x)) ≠ 1}) := by
      apply measure_mono
      intro x hx
      simp only [Set.mem_ofPred_eq] at hx
      by_cases hc : χ (X x) = 1
      · right
        have hd : localPullback X χ'.val x = 1 := by
          simp only [localPullback, ite_eq_left (hVX hx.1)]
          exact hc
        rw [hd, one_mul, hHder] at hx
        exact ⟨hx.1, fun hz => hx.2.1 (by rw [hz]; ring),
          fun hz => hx.2.2 (by rw [hz])⟩
      · exact Or.inl ⟨hx.1, hc⟩
    _ ≤ _ + _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal η + ENNReal.ofReal C * ENNReal.ofReal η :=
      add_le_add hcm himpure
    _ ≤ ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_mul hCpos.le, ← ENNReal.ofReal_add (mul_nonneg hCpos.le hη.le)
        (mul_nonneg hCpos.le hη.le)]
      apply ENNReal.ofReal_le_ofReal
      dsimp only [η]
      field_simp
      nlinarith

end ScalarConductivity

end

end OAI
