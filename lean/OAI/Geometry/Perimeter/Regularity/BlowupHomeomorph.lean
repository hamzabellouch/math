import OAI.Geometry.Perimeter.Regularity.SmoothFlatOrder
import OAI.Geometry.Perimeter.Regularity.SetIntegralSubLeSymmDiff

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
open scoped ENNReal Topology
open scoped ENNReal Topology ContDiff
open scoped Topology ENNReal
namespace RPISingularHarnack

def blowupHomeomorph {n : ℕ} (c : Euc n) {r : ℝ} (hr : 0 < r) : Euc n ≃ₜ Euc n :=
  (Homeomorph.smulOfNeZero r hr.ne').trans (Homeomorph.addLeft c)

@[simp] theorem blowupHomeomorph_apply {n : ℕ} (c : Euc n) {r : ℝ} (hr : 0 < r)
    (x : Euc n) : blowupHomeomorph c hr x = c + r • x := rfl

@[simp] theorem blowupHomeomorph_symm_apply {n : ℕ} (c : Euc n) {r : ℝ} (hr : 0 < r)
    (x : Euc n) : (blowupHomeomorph c hr).symm x = r⁻¹ • (x-c) := by
  change r⁻¹ • (-c + x) = r⁻¹ • (x-c)
  congr 1
  abel

theorem admissible_comp_blowup {n : ℕ} {U : Set (Euc n)} {V : Euc n → Euc n}
    (hV : PerimeterAdmissible U V) (c : Euc n) {r : ℝ} (hr : 0 < r) :
    PerimeterAdmissible (blownUpSet U c r) (fun z ↦ V (c+r • z)) := by
  refine ⟨hV.1.comp (contDiff_const.add (contDiff_id.const_smul r)),
    hV.2.1.comp_homeomorph (blowupHomeomorph c hr), ?_, fun x ↦ hV.2.2.2 _⟩
  intro x hx
  exact hV.2.2.1 (tsupport_comp_subset_preimage V (continuous_const.add (continuous_id.const_smul r)) hx)

theorem admissible_comp_blowdown {n : ℕ} {U : Set (Euc n)} {V : Euc n → Euc n}
    {c : Euc n} {r : ℝ} (hV : PerimeterAdmissible (blownUpSet U c r) V)
    (hr : 0 < r) : PerimeterAdmissible U (fun y ↦ V (r⁻¹ • (y-c))) := by
  refine ⟨hV.1.comp ((contDiff_id.sub contDiff_const).const_smul r⁻¹),
    ?_, ?_, fun x ↦ hV.2.2.2 _⟩
  · simpa only [Function.comp_def, blowupHomeomorph_symm_apply] using
      hV.2.1.comp_homeomorph (blowupHomeomorph c hr).symm
  · intro y hy
    have hh := hV.2.2.1 (tsupport_comp_subset_preimage V
      ((continuous_id.sub continuous_const).const_smul r⁻¹) hy)
    change c + r • (r⁻¹ • (y-c)) ∈ U at hh
    simpa [smul_inv_smul₀ hr.ne'] using hh

theorem divergence_comp_blowup {n : ℕ} {V : Euc n → Euc n}
    (hV : Differentiable ℝ V) (c : Euc n) (r : ℝ) (y : Euc n) :
    divergence (fun z ↦ V (c+r • z)) y = r * divergence V (c+r • y) := by
  have hd := ((hV _).hasFDerivAt.comp y
    (((hasFDerivAt_id y).const_smul r).const_add c)).fderiv
  simp only [Function.comp_def, id_eq, Pi.smul_apply] at hd
  simp only [divergence, hd, ContinuousLinearMap.comp_apply,
    smul_apply, ContinuousLinearMap.id_apply, map_smul,
    inner_smul_right, ← Finset.mul_sum]

theorem integral_divergence_comp_blowup {n : ℕ} {E : Set (Euc n)}
    (hE : MeasurableSet E) {V : Euc n → Euc n} (hV : Differentiable ℝ V)
    (c : Euc n) {r : ℝ} (hr : 0 < r) :
    (∫ z in blownUpSet E c r, divergence (fun y ↦ V (c+r • y)) z) =
      (r * (r^n)⁻¹) * ∫ y in E, divergence V y := by
  simp_rw [divergence_comp_blowup hV]
  rw [integral_const_mul, integral_blownUpSet hE _ c hr]
  ring

theorem integral_divergence_comp_blowdown {n : ℕ} {E : Set (Euc n)}
    (hE : MeasurableSet E) {V : Euc n → Euc n} (hV : Differentiable ℝ V)
    (c : Euc n) {r : ℝ} (hr : 0 < r) :
    (∫ z in blownUpSet E c r, divergence V z) =
      (r * (r^n)⁻¹) * ∫ y in E, divergence (fun z ↦ V (r⁻¹ • (z-c))) y := by
  let W : Euc n → Euc n := fun y ↦ V (r⁻¹ • (y-c))
  have he (z : Euc n) : divergence W (c+r • z) = r⁻¹ * divergence V z := by
    dsimp [W]
    rw [divergence_comp_blowdown hV]
    simp [inv_smul_smul₀ hr.ne']
  have hh := integral_blownUpSet hE (divergence W) c hr
  simp_rw [he] at hh
  rw [integral_const_mul] at hh
  have heq := congrArg (fun a : ℝ ↦ r*a) hh
  simpa only [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul] using heq

theorem perimeter_blownUpSet_eq {n : ℕ} {E U : Set (Euc n)}
    (hE : MeasurableSet E) (c : Euc n) {r : ℝ} (hr : 0 < r) :
    perimeter (blownUpSet E c r) (blownUpSet U c r) =
      ENNReal.ofReal (r * (r^n)⁻¹) * perimeter E U := by
  have hp : 0 ≤ r * (r^n)⁻¹ := by positivity
  apply le_antisymm
  · rw [perimeter_eq_iSup_tests]
    refine iSup_le fun V ↦ iSup_le fun hV ↦ ?_
    rw [integral_divergence_comp_blowdown hE (hV.1.differentiable (by simp)) c hr,
      ENNReal.ofReal_mul hp]
    apply mul_le_mul' le_rfl
    rw [perimeter_eq_iSup_tests]
    exact le_iSup_of_le _ (le_iSup_of_le (admissible_comp_blowdown hV hr) le_rfl)
  · rw [perimeter_eq_iSup_tests E U]
    simp_rw [ENNReal.mul_iSup]
    refine iSup_le fun V ↦ iSup_le fun hV ↦ ?_
    rw [← ENNReal.ofReal_mul hp,
      ← integral_divergence_comp_blowup hE (hV.1.differentiable (by simp)) c hr,
      perimeter_eq_iSup_tests]
    exact le_iSup_of_le _ (le_iSup_of_le (admissible_comp_blowup hV c hr) le_rfl)

theorem blownUpSet_ball {n : ℕ} (c a : Euc n) {r : ℝ} (hr : 0 < r) (R : ℝ) :
    blownUpSet (Metric.ball (c+r • a) (r*R)) c r = Metric.ball a R := by
  ext x
  change dist (c+r • x) (c+r • a) < r*R ↔ dist x a < R
  rw [dist_add_left, dist_smul₀, Real.norm_of_nonneg hr.le, mul_lt_mul_iff_right₀ hr]

theorem locally_minimizing_blownUpSet {n : ℕ} {E : Set (Euc n)}
    (hmin : IsLocallyPerimeterMinimizing E) (c : Euc n) {r : ℝ} (hr : 0 < r) :
    IsLocallyPerimeterMinimizing (blownUpSet E c r) := by
  have hm := measurableSet_blownUpSet hmin.1 c r
  refine ⟨hm, ?_, ?_⟩
  · intro a R hR
    rw [← blownUpSet_ball c a hr R, perimeter_blownUpSet_eq hmin.1 c hr]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hmin.2.1 _ _ (mul_pos hr hR))
  · intro a R hR G hG hcG hsG
    let A := blowupHomeomorph c hr
    let H := A.symm ⁻¹' G
    have hH : MeasurableSet H := hG.preimage A.symm.continuous.measurable
    have hEA : A.symm ⁻¹' blownUpSet E c r = E := by
      ext y
      change A (A.symm y) ∈ E ↔ y ∈ E
      rw [A.apply_symm_apply]
    have hHA : blownUpSet H c r = G := by
      ext y
      change A.symm (A y) ∈ G ↔ y ∈ G
      rw [A.symm_apply_apply]
    have hdiff : symmDiff E H = A.symm ⁻¹' symmDiff (blownUpSet E c r) G := by
      rw [preimage_symmDiff, hEA]
    have hcl : closure (symmDiff E H) = A.symm ⁻¹' closure (symmDiff (blownUpSet E c r) G) := by
      rw [hdiff, ← A.symm.preimage_closure]
    have hcH : IsCompact (closure (symmDiff E H)) := by
      rw [hcl]
      exact A.symm.isCompact_preimage.mpr hcG
    have hsH : closure (symmDiff E H) ⊆ Metric.ball (c+r • a) (r*R) := by
      intro y hy
      rw [hcl] at hy
      have hh := hsG hy
      rw [← blownUpSet_ball c a hr R] at hh
      change A (A.symm y) ∈ Metric.ball (c+r • a) (r*R) at hh
      simpa only [A.apply_symm_apply] using hh
    have hcmp := hmin.2.2 (c+r • a) (r*R) (mul_pos hr hR) H hH hcH hsH
    calc
      perimeter (blownUpSet E c r) (Metric.ball a R) =
          ENNReal.ofReal (r * (r^n)⁻¹) * perimeter E (Metric.ball (c+r • a) (r*R)) := by
        rw [← blownUpSet_ball c a hr R, perimeter_blownUpSet_eq hmin.1 c hr]
      _ ≤ ENNReal.ofReal (r * (r^n)⁻¹) * perimeter H (Metric.ball (c+r • a) (r*R)) :=
        mul_le_mul' le_rfl hcmp
      _ = perimeter G (Metric.ball a R) := by
        rw [← perimeter_blownUpSet_eq hH c hr, hHA, blownUpSet_ball c a hr R]

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
open scoped ENNReal Topology
open scoped ENNReal Topology ContDiff
open scoped Topology ENNReal
namespace RPISingularHarnack

theorem exists_uniform_minimizing_exhaustion_cut {n : ℕ} (hn : 0 < n) (m : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ E : Set (Euc n), IsLocallyPerimeterMinimizing E →
      ∃ A : Set (Euc n), MeasurableSet A ∧ A ⊆ Metric.closedBall 0 ((m:ℝ)+2) ∧
        A ∩ Metric.closedBall 0 ((m:ℝ)+1) = E ∩ Metric.closedBall 0 ((m:ℝ)+1) ∧
        perimeter A univ ≤ C := by
  obtain ⟨L, hL, hbound⟩ := exists_smoothTransition_deriv_bound
  obtain ⟨C, hC, hgrowth⟩ := exists_locallyMinimizing_perimeter_growth_constant n hn
  let D : ℝ := volume.real (Metric.closedBall (0:Euc n) ((m:ℝ)+2)) + 1
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨ENNReal.ofReal (C*((m:ℝ)+3)^(n-1)) + ENNReal.ofReal (8*L*D), by finiteness, ?_⟩
  intro E hmin
  have hv : volume.real (E ∩ Metric.closedBall (0:Euc n) ((m:ℝ)+2)) <
      D * (((m:ℝ)+2)-((m:ℝ)+1)) := by
    have hh := measureReal_mono (μ := (volume : Measure (Euc n)))
      (s₁ := E ∩ Metric.closedBall 0 ((m:ℝ)+2)) inter_subset_right
      (isCompact_closedBall (0:Euc n) ((m:ℝ)+2)).measure_ne_top
    dsimp [D]
    linarith
  obtain ⟨r, hr, hc⟩ := exists_controlled_cut_radius E (0:Euc n)
    (by positivity : (0:ℝ) < (m:ℝ)+1) (by linarith : (m:ℝ)+1 < (m:ℝ)+2) hv
  refine ⟨E ∩ Metric.closedBall 0 r, hmin.1.inter measurableSet_closedBall,
    inter_subset_right.trans (Metric.closedBall_subset_closedBall hr.2.le), ?_, ?_⟩
  · rw [inter_assoc, inter_eq_right.mpr (Metric.closedBall_subset_closedBall hr.1)]
  · have hh := controlled_radius_perimeter_cut hmin.1 (0:Euc n)
      (by linarith [hr.1] : 0 < r) hr.2
      (Metric.closedBall_subset_ball (by linarith : (m:ℝ)+2 < (m:ℝ)+3))
      hc hD.le hL hbound (hmin.2.1 0 ((m:ℝ)+3) (by positivity)).ne
    exact (le_add_right le_rfl).trans (hh.trans
      (add_le_add (hgrowth E hmin 0 ((m:ℝ)+3) (by positivity)) le_rfl))

theorem exists_set_of_indicator_Lp {n : ℕ} (K : Set (Euc n)) (hK : IsCompact K)
    (g : Lp ℝ 1 (volume.comap (Subtype.val : K → Euc n)))
    (hg : ∀ᵐ x ∂(volume.comap (Subtype.val : K → Euc n)), g x = 0 ∨ g x = 1) :
    ∃ F : Set (Euc n), ∃ hF : MeasurableSet F, F ⊆ K ∧ compactIndicatorLp K hK F hF = g := by
  let A : Set K := {x | g x = 1}
  have hA : MeasurableSet A := measurableSet_eq_fun (Lp.stronglyMeasurable g).measurable measurable_const
  let F : Set (Euc n) := Subtype.val '' A
  have hF : MeasurableSet F :=
    (MeasurableEmbedding.subtype_coe hK.measurableSet).measurableSet_image.mpr hA
  refine ⟨F, hF, Subtype.coe_image_subset K A, ?_⟩
  apply Lp.ext
  filter_upwards [compactIndicatorLp_ae K hK F hF, hg] with x hx hx01
  rw [hx]
  by_cases hx1 : g x = 1
  · have hxF : (x:Euc n) ∈ F := ⟨x, hx1, rfl⟩
    simp only [indicator_of_mem hxF, hx1]
  · have hxF : (x:Euc n) ∉ F := by
      rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      subst y
      exact hx1 hy
    simp only [indicator_of_notMem hxF, hx01.resolve_right hx1]

theorem exists_simultaneous_indicator_L1_subsequence {n : ℕ}
    (K : ℕ → Set (Euc n)) (hK : ∀ m, IsCompact (K m))
    (C : ℕ → ℝ≥0∞) (hC : ∀ m, C m ≠ ⊤)
    (A : ℕ → ℕ → Set (Euc n)) (hA : ∀ m i, MeasurableSet (A m i))
    (hAK : ∀ m i, A m i ⊆ K m) (hP : ∀ m i, perimeter (A m i) univ ≤ C m) :
    ∃ F : ℕ → Set (Euc n), (∀ m, MeasurableSet (F m)) ∧ (∀ m, F m ⊆ K m) ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ m,
        Tendsto (fun i ↦ volume (symmDiff (A m (σ i)) (F m))) atTop (𝓝 0) := by
  let μ (m : ℕ) : Measure (K m) := volume.comap (Subtype.val : K m → Euc n)
  let S (m : ℕ) : Set (Lp ℝ 1 (μ m)) := range (fun H : {H : Set (Euc n) //
    MeasurableSet H ∧ H ⊆ K m ∧ perimeter H univ ≤ C m} ↦
      compactIndicatorLp (K m) (hK m) H H.property.1)
  let f (i : ℕ) (m : ℕ) : Lp ℝ 1 (μ m) := compactIndicatorLp (K m) (hK m) (A m i) (hA m i)
  have hc (m : ℕ) : IsCompact (closure (S m)) :=
    (bounded_perimeter_indicator_totallyBounded (K m) (hK m) (C m) (hC m)).closure.isCompact_of_isClosed
      isClosed_closure
  have hf (i : ℕ) : f i ∈ {x | ∀ m, x m ∈ closure (S m)} := by
    intro m
    exact subset_closure ⟨⟨A m i, hA m i, hAK m i, hP m i⟩, rfl⟩
  obtain ⟨g, hg, σ, hσ, ht⟩ := (isCompact_pi_infinite hc).isSeqCompact hf
  have hg01 (m : ℕ) : ∀ᵐ x ∂(μ m), g m x = 0 ∨ g m x = 1 := by
    have hclosed : IsClosed {u : Lp ℝ 1 (μ m) | ∀ᵐ x ∂(μ m), u x ∈ ({0,1}:Set ℝ)} :=
      isClosed_lp_ae_mem (μ m) _ (isClosed_singleton.union isClosed_singleton)
    have hs : S m ⊆ {u : Lp ℝ 1 (μ m) | ∀ᵐ x ∂(μ m), u x ∈ ({0,1}:Set ℝ)} := by
      rintro _ ⟨H, rfl⟩
      filter_upwards [compactIndicatorLp_ae (K m) (hK m) H H.property.1] with x hx
      rw [hx]
      by_cases hxH : (x:Euc n) ∈ (H:Set (Euc n)) <;> simp [hxH]
    simpa only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff] using
      closure_minimal hs hclosed (hg m)
  choose F hF hFK hFg using fun m ↦ exists_set_of_indicator_Lp (K m) (hK m) (g m) (hg01 m)
  refine ⟨F, hF, hFK, σ, hσ, ?_⟩
  intro m
  have htm := tendsto_pi_nhds.mp ht m
  have he : Tendsto (fun i ↦ edist (f (σ i) m) (g m)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, edist_self] using
      htm.edist (tendsto_const_nhds (x := g m))
  rw [← hFg m] at he
  simp only [f, compactIndicatorLp_edist (K m) (hK m) _ _ _ _ (hAK m _) (hFK m)] at he
  have hvol (i : ℕ) : (∫⁻ x, ‖(A m (σ i)).indicator (fun _ ↦ (1:ℝ)) x -
      (F m).indicator (fun _ ↦ (1:ℝ)) x‖ₑ) = volume (symmDiff (A m (σ i)) (F m)) := by
    simpa using lintegral_indicator_difference (U := univ) (hA m (σ i)) (hF m)
  simpa only [hvol] using he

theorem exists_global_set_of_local_L1_limits {n : ℕ}
    (E F : ℕ → Set (Euc n)) (hF : ∀ m, MeasurableSet (F m))
    (hconv : ∀ m, Tendsto (fun i ↦ volume (symmDiff (E i) (F m) ∩
      Metric.closedBall 0 ((m:ℝ)+1))) atTop (𝓝 0)) :
    ∃ G : Set (Euc n), MeasurableSet G ∧ ∀ (c : Euc n) (R : ℝ), 0 < R →
      Tendsto (fun i ↦ volume.real (symmDiff (E i) G ∩ Metric.closedBall c R)) atTop (𝓝 0) := by
  let B (m : ℕ) : Set (Euc n) := Metric.closedBall 0 ((m:ℝ)+1)
  have hBmono : Monotone B := fun j m hjm ↦
    Metric.closedBall_subset_closedBall (by exact_mod_cast Nat.add_le_add_right hjm 1)
  have hrestrict (j m : ℕ) (hjm : j ≤ m) :
      Tendsto (fun i ↦ volume (symmDiff (E i) (F m) ∩ B j)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hconv m)
      (fun _ ↦ bot_le) (fun i ↦ measure_mono (inter_subset_inter_right _ (hBmono hjm)))
  have hcompat (m l : ℕ) : (F m ∩ B (min m l) : Set (Euc n)) =ᵐ[volume] (F l ∩ B (min m l) : Set (Euc n)) := by
    apply measure_symmDiff_eq_zero_iff.mp
    apply le_antisymm _ bot_le
    have ht := (hrestrict (min m l) m (min_le_left _ _)).add
      (hrestrict (min m l) l (min_le_right _ _))
    simp only [zero_add] at ht
    apply ge_of_tendsto ht
    exact Eventually.of_forall fun i ↦ by
      simpa only [← inter_symmDiff_distrib_right, symmDiff_comm (F m) (E i)] using
        (measure_symmDiff_le (μ := (volume : Measure (Euc n)))
          (F m ∩ B (min m l)) (E i ∩ B (min m l)) (F l ∩ B (min m l)))
  let G : Set (Euc n) := ⋃ m, F m ∩ B m
  have hG : MeasurableSet G := MeasurableSet.iUnion fun m ↦
    (hF m).inter measurableSet_closedBall
  have hagree (m : ℕ) : (G ∩ B m : Set (Euc n)) =ᵐ[volume] (F m ∩ B m : Set (Euc n)) := by
    filter_upwards [ae_all_iff.mpr (fun l ↦ hcompat m l)] with x hx
    apply propext
    constructor
    · rintro ⟨hxG, hxm⟩
      obtain ⟨l, hxl, hxBl⟩ := mem_iUnion.mp hxG
      have hxB : x ∈ B (min m l) := by
        rcases le_total m l with h | h
        · simpa only [min_eq_left h] using hxm
        · simpa only [min_eq_right h] using hxBl
      have hh : x ∈ F m ∩ B (min m l) := (eq_iff_iff.mp (hx l)).mpr ⟨hxl, hxB⟩
      exact ⟨hh.1, hxm⟩
    · rintro ⟨hxm, hxB⟩
      exact ⟨mem_iUnion.mpr ⟨m, hxm, hxB⟩, hxB⟩
  have hconvG (m : ℕ) : Tendsto (fun i ↦ volume (symmDiff (E i) G ∩ B m)) atTop (𝓝 0) := by
    convert hconv m using 1
    funext i
    apply measure_congr
    filter_upwards [hagree m] with x hx
    have hh : (x ∈ G ∧ x ∈ B m) ↔ (x ∈ F m ∧ x ∈ B m) := eq_iff_iff.mp hx
    change (x ∈ symmDiff (E i) G ∩ B m) =
      (x ∈ symmDiff (E i) (F m) ∩ B m)
    apply propext
    simp only [mem_inter_iff, mem_symmDiff]
    tauto
  refine ⟨G, hG, ?_⟩
  intro c R hR
  obtain ⟨m, hm⟩ := exists_nat_gt (dist c 0 + R)
  have hs : Metric.closedBall c R ⊆ B m := by
    intro x hx
    apply Metric.mem_closedBall.mpr
    exact (dist_triangle x c 0).trans (by
      have hh := Metric.mem_closedBall.mp hx
      linarith)
  have ht : Tendsto (fun i ↦ volume (symmDiff (E i) G ∩ Metric.closedBall c R)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hconvG m)
      (fun _ ↦ bot_le) (fun i ↦ measure_mono (inter_subset_inter_right _ hs))
  simpa only [measureReal_def, ENNReal.toReal_zero, Function.comp_def] using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ht

theorem minimizing_global_compactness {n : ℕ} (hn : 0 < n)
    (E : ℕ → Set (Euc n)) (hE : ∀ i, IsLocallyPerimeterMinimizing (E i)) :
    ∃ F : Set (Euc n), IsLocallyPerimeterMinimizing F ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
        (∀ (c : Euc n) (R : ℝ), 0 < R →
          Tendsto (fun i ↦ volume.real (symmDiff (E (σ i)) F ∩ Metric.closedBall c R))
            atTop (𝓝 0)) ∧
        (∀ (c : Euc n) (r : ℝ), 0 < r → perimeterMeasure F (Metric.sphere c r) = 0 →
          Tendsto (fun i ↦ perimeter (E (σ i)) (Metric.ball c r)) atTop
            (𝓝 (perimeter F (Metric.ball c r)))) := by
  choose C hC hcut using exists_uniform_minimizing_exhaustion_cut hn
  choose A hA hAK hAE hP using fun m i ↦ hcut m (E i) (hE i)
  obtain ⟨F, hF, hFK, σ, hσ, ht⟩ := exists_simultaneous_indicator_L1_subsequence
    (fun m ↦ Metric.closedBall 0 ((m:ℝ)+2)) (fun m ↦ isCompact_closedBall _ _)
    C hC A hA hAK hP
  have hlocal (m : ℕ) : Tendsto (fun i ↦ volume (symmDiff (E (σ i)) (F m) ∩
      Metric.closedBall 0 ((m:ℝ)+1))) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (ht m)
      (fun _ ↦ bot_le) (fun i ↦ ?_)
    apply measure_mono
    intro x hx
    have hh : x ∈ E (σ i) ↔ x ∈ A m (σ i) := by
      have he := Set.ext_iff.mp (hAE m (σ i)) x
      simp only [mem_inter_iff] at he
      exact ⟨fun h ↦ (he.mpr ⟨h, hx.2⟩).1, fun h ↦ (he.mp ⟨h, hx.2⟩).1⟩
    simpa only [mem_symmDiff, hh] using hx.1
  obtain ⟨G, hG, hconv⟩ := exists_global_set_of_local_L1_limits (fun i ↦ E (σ i)) F hF hlocal
  refine ⟨G, locally_minimizing_of_local_L1_limit hn (fun i ↦ hE (σ i)) hG hconv,
    σ, hσ, hconv, ?_⟩
  intro c r hr hnull
  exact tendsto_minimizing_perimeter_ball_of_local_L1 hn (fun i ↦ hE (σ i)) hG hconv c hr hnull

end RPISingularHarnack

end

end OAI
