import OAI.Probability.FreeIsing.Trees.ConeSelectedFusion

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Problem367
open PathSideBranches

theorem condExp_regression_of_le
    {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {m₁ m₂ : MeasurableSpace Ω} (h₁₂ : m₁ ≤ m₂) (h₂ : m₂ ≤ m)
    {f g : Ω → ℝ} {theta : ℝ}
    (h : P[f | m₂] =ᵐ[P] fun z => theta * (P[g | m₂]) z) :
    P[f | m₁] =ᵐ[P] fun z => theta * (P[g | m₁]) z := by
  have hreg := condExp_congr_ae (m := m₁) h
  have hmul := condExp_smul (μ := P) theta (P[g | m₂]) m₁
  filter_upwards [hreg, hmul, condExp_condExp_of_le (f := f) h₁₂ h₂,
    condExp_condExp_of_le (f := g) h₁₂ h₂] with z hz hm hf hg
  simpa only [Pi.smul_apply, smul_eq_mul, hf, hg] using hz.trans hm

theorem HasFreeIsingLaw.selectedPosterior_parent_subset_cone
    {d : ℕ} {theta : ℝ} {A B : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (r : TreeVertex d) (hr : r.1 ≠ [])
    (T : Set (TreeVertex d)) (hT : T ⊆ cone r) :
    let P := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
    selectedPosterior P F (Subtype.val : T → TreeVertex d) (parentVertex r) =ᵐ[P]
      fun z => theta * selectedPosterior P F (Subtype.val : T → TreeVertex d) r z := by
  let := hμ.isProbabilityMeasure
  have hle : selectedObservationField F (Subtype.val : T → TreeVertex d) ≤
      selectedObservationField F (Subtype.val : cone r → TreeVertex d) := by
    apply selectedObservationField_le_of_range_subset F
    rintro u ⟨v, rfl⟩
    exact ⟨⟨v.1, hT v.2⟩, rfl⟩
  exact condExp_regression_of_le _ hle
    (selectedObservationField_le hF (Subtype.val : cone r → TreeVertex d))
    (hμ.selectedPosterior_parent_cone h0 h1 ν hF r hr)

theorem HasFreeIsingLaw.selected_gaussian_outside_subset_cone_fusion
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (r : TreeVertex d) (hr : r.1 ≠ [])
    (S T : Set (TreeVertex d)) (hS : S ⊆ (cone r)ᶜ) (hT : T ⊆ cone r)
    (hp : parentVertex r ∈ S) (hq : r ∈ T) :
    let P := μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)
    let F : IsingSpin → ℝ → ℝ := fun s z => (t : ℝ) * spinSign s + z
    selectedPosterior P F (Subtype.val : (S ∪ T : Set (TreeVertex d)) → TreeVertex d) (parentVertex r) =ᵐ[P]
      fun z => binaryFusion
        (selectedPosterior P F (Subtype.val : S → TreeVertex d) (parentVertex r) z)
        (Real.tanh beta * selectedPosterior P F
          (Subtype.val : T → TreeVertex d) r z) := by
  let := hμ.isProbabilityMeasure
  let P := μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)
  let F : IsingSpin → ℝ → ℝ := fun s z => (t : ℝ) * spinSign s + z
  let X := fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
    fun i : S => F (z.1 i.1) (z.2 i.1)
  let Y := fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
    fun i : T => F (z.1 i.1) (z.2 i.1)
  have hF : Measurable (Function.uncurry F) :=
    ((PlantedInformation.measurable_spinSign.comp measurable_fst).const_mul
      (t : ℝ)).add measurable_snd
  have hX : Measurable X := by
    apply Measurable.of_eval
    intro i
    exact hF.comp (show Measurable (fun z :
      (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
        (z.1 i.1, z.2 i.1)) from by fun_prop)
  have hY : Measurable Y := by
    apply Measurable.of_eval
    intro i
    exact hF.comp (show Measurable (fun z :
      (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
        (z.1 i.1, z.2 i.1)) from by fun_prop)
  have hXout : Measurable[noisyRegionSigma (A := ℝ) (cone r)ᶜ] X :=
    (comap_measurable X).mono
      ((selectedObservationField_le_noisyRegionSigma hF S).trans
        (noisyRegionSigma_mono hS)) le_rfl
  have hYin : Measurable[noisyRegionSigma (A := ℝ) (cone r)] Y :=
    (comap_measurable Y).mono
      ((selectedObservationField_le_noisyRegionSigma hF T).trans
        (noisyRegionSigma_mono hT)) le_rfl
  have hInd := hμ.condIndepFun_noisy_cone_observables
    (Real.neg_one_lt_tanh beta).le (Real.tanh_lt_one beta).le
    (gaussianReal 0 t) r hr X Y hXout hYin
  have hreg : selectedPosterior P F (Subtype.val : T → TreeVertex d)
      (parentVertex r) =ᵐ[P] fun z => Real.tanh beta *
        selectedPosterior P F (Subtype.val : T → TreeVertex d) r z :=
    hμ.selectedPosterior_parent_subset_cone
    (Real.neg_one_lt_tanh beta).le (Real.tanh_lt_one beta).le
    (gaussianReal 0 t) hF r hr T hT
  have hL : ∀ᵐ z ∂P,
      |selectedPosterior P F (Subtype.val : S → TreeVertex d) (parentVertex r) z| < 1 := by
    filter_upwards [hμ.selected_gaussian_posterior_field_bound hbeta t
      (Subtype.val : S → TreeVertex d) (parentVertex r) ⟨⟨_, hp⟩, rfl⟩] with z hz
    exact abs_lt.mpr hz.1
  have hQ : ∀ᵐ z ∂P,
      |selectedPosterior P F (Subtype.val : T → TreeVertex d) r z| < 1 := by
    filter_upwards [hμ.selected_gaussian_posterior_field_bound hbeta t
      (Subtype.val : T → TreeVertex d) r ⟨⟨r, hq⟩, rfl⟩] with z hz
    exact abs_lt.mpr hz.1
  have hR : ∀ᵐ z ∂P,
      |selectedPosterior P F (Subtype.val : T → TreeVertex d) (parentVertex r) z| < 1 := by
    filter_upwards [hreg, hQ] with z hz hq
    rw [hz, abs_mul]
    exact (mul_le_mul_of_nonneg_left hq.le (abs_nonneg (Real.tanh beta))).trans_lt
      (by simpa using Real.abs_tanh_lt_one beta)
  have h := condExp_spin_comap_sup_eq_binaryFusion
    ((measurable_pi_apply (parentVertex r)).comp measurable_fst) hX hY
    (hμ.planted_spin_event_mass (fun _ => gaussianReal 0 t) _) hInd hL hR
  dsimp only
  unfold selectedPosterior
  rw [selectedObservationField_region_union]
  filter_upwards [h, hreg] with z hz hregz
  exact hz.trans (congrArg (binaryFusion
    (selectedPosterior P F (Subtype.val : S → TreeVertex d) (parentVertex r) z)) hregz)

theorem HasFreeIsingLaw.selected_gaussian_outside_subset_cone_field
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (r : TreeVertex d) (hr : r.1 ≠ [])
    (S T : Set (TreeVertex d)) (hS : S ⊆ (cone r)ᶜ) (hT : T ⊆ cone r)
    (hp : parentVertex r ∈ S) (hq : r ∈ T) :
    let P := μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)
    let F : IsingSpin → ℝ → ℝ := fun s z => (t : ℝ) * spinSign s + z
    (fun z => Real.artanh (selectedPosterior P F
      (Subtype.val : (S ∪ T : Set (TreeVertex d)) → TreeVertex d) (parentVertex r) z)) =ᵐ[P]
      fun z => Real.artanh (selectedPosterior P F
        (Subtype.val : S → TreeVertex d) (parentVertex r) z) +
        statisticMessage (Real.tanh beta) (selectedPosterior P F
          (Subtype.val : T → TreeVertex d) r z) := by
  have h := hμ.selected_gaussian_outside_subset_cone_fusion hbeta t r hr S T hS hT hp hq
  have hL := hμ.selected_gaussian_posterior_field_bound hbeta t
    (Subtype.val : S → TreeVertex d) (parentVertex r) ⟨⟨_, hp⟩, rfl⟩
  have hQ := hμ.selected_gaussian_posterior_field_bound hbeta t
    (Subtype.val : T → TreeVertex d) r ⟨⟨r, hq⟩, rfl⟩
  filter_upwards [h, hL, hQ] with z hz hl hq
  rw [hz]
  exact artanh_binaryFusion (abs_lt.mpr hl.1)
    (binaryFusion_abs_mul_lt_one (Real.abs_tanh_lt_one beta) (abs_lt.mpr hq.1))

theorem HasFreeIsingLaw.selected_gaussian_subset_cone_field_difference
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (r : TreeVertex d) (hr : r.1 ≠ [])
    (S T U : Set (TreeVertex d)) (hS : S ⊆ (cone r)ᶜ)
    (hT : T ⊆ cone r) (hU : U ⊆ cone r)
    (hp : parentVertex r ∈ S) (ht : r ∈ T) (hu : r ∈ U) :
    let P := μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)
    let F : IsingSpin → ℝ → ℝ := fun s z => (t : ℝ) * spinSign s + z
    let field := fun (V : Set (TreeVertex d)) (u : TreeVertex d) z =>
      Real.artanh (selectedPosterior P F (Subtype.val : V → TreeVertex d) u z)
    ∀ᵐ z ∂P,
      |field (S ∪ T) (parentVertex r) z - field (S ∪ U) (parentVertex r) z| ≤
        Real.tanh beta * |field T r z - field U r z| ∧
      |field (S ∪ T) (parentVertex r) z - field (S ∪ U) (parentVertex r) z| ≤
        2 * beta := by
  have hFT := hμ.selected_gaussian_outside_subset_cone_field hbeta t r hr S T hS hT hp ht
  have hFU := hμ.selected_gaussian_outside_subset_cone_field hbeta t r hr S U hS hU hp hu
  have hQT := hμ.selected_gaussian_posterior_field_bound hbeta t
    (Subtype.val : T → TreeVertex d) r ⟨⟨r, ht⟩, rfl⟩
  have hQU := hμ.selected_gaussian_posterior_field_bound hbeta t
    (Subtype.val : U → TreeVertex d) r ⟨⟨r, hu⟩, rfl⟩
  have hθ0 : 0 ≤ Real.tanh beta := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hbeta) (Real.cosh_pos beta).le
  filter_upwards [hFT, hFU, hQT, hQU] with z hft hfu hqt hqu
  rw [hft, hfu, add_sub_add_left_eq_sub]
  constructor
  · have h := (lipschitzWith_cavityMessage hθ0 (Real.tanh_lt_one beta).le).dist_le_mul
      (Real.artanh (selectedPosterior
        (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t))
        (fun s z => (t : ℝ) * spinSign s + z) (Subtype.val : T → TreeVertex d) r z))
      (Real.artanh (selectedPosterior
        (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t))
        (fun s z => (t : ℝ) * spinSign s + z) (Subtype.val : U → TreeVertex d) r z))
    convert h using 1 <;>
      simp only [Real.dist_eq, cavityMessage, Real.tanh_artanh hqt.1,
        Real.tanh_artanh hqu.1, statisticMessage]
    rfl
  · have ht' := statisticMessage_abs_le hθ0 (Real.tanh_lt_one beta)
      (abs_lt.mpr hqt.1).le
    have hu' := statisticMessage_abs_le hθ0 (Real.tanh_lt_one beta)
      (abs_lt.mpr hqu.1).le
    rw [Real.artanh_tanh] at ht' hu'
    exact (abs_sub _ _).trans (by linarith)

end Problem367

end

end OAI
