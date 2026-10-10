import Mathlib

namespace OAI

open Set MeasureTheory

noncomputable section

namespace CylinderCovering.SimplexLayerCake

theorem integral_shadow_profile (L : ℝ) (hL : 0 < L) (n : ℕ) :
    (∫ s in (0 : ℝ)..L, (1 - s / L) ^ n) = L / (n + 1 : ℝ) := by
  have hLne : L ≠ 0 := ne_of_gt hL
  have h := intervalIntegral.integral_comp_sub_mul (a := (0 : ℝ)) (b := L)
    (c := L⁻¹) (fun x : ℝ => x ^ n) (inv_ne_zero hLne) 1
  simp only [inv_inv, mul_zero, sub_zero, inv_mul_cancel₀ hLne, sub_self,
    smul_eq_mul, integral_pow, one_pow, zero_pow (Nat.succ_ne_zero n),
    sub_zero] at h
  simpa only [div_eq_mul_inv, mul_comm, one_mul] using h

theorem integral_eq_area_mul_length_div
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (ℓ : α → ℝ)
    (A L : ℝ) (hL : 0 < L) (n : ℕ)
    (hℓ : Integrable ℓ μ) (hℓnonneg : 0 ≤ᵐ[μ] ℓ)
    (hℓbound : ℓ ≤ᵐ[μ] fun _ => L)
    (hprofile : ∀ s ∈ Ioo (0 : ℝ) L,
      μ.real {x | s ≤ ℓ x} = A * (1 - s / L) ^ n) :
    (∫ x, ℓ x ∂μ) = A * L / (n + 1 : ℝ) := by
  rw [hℓ.integral_eq_integral_Ioc_meas_le hℓnonneg hℓbound,
    integral_Ioc_eq_integral_Ioo]
  calc
    (∫ s in Ioo (0 : ℝ) L, μ.real {x | s ≤ ℓ x}) =
        ∫ s in Ioo (0 : ℝ) L, A * (1 - s / L) ^ n :=
      setIntegral_congr_fun measurableSet_Ioo hprofile
    _ = ∫ s in (0 : ℝ)..L, A * (1 - s / L) ^ n := by
      rw [intervalIntegral.integral_of_le hL.le, integral_Ioc_eq_integral_Ioo]
    _ = A * L / (n + 1 : ℝ) := by
      rw [intervalIntegral.integral_const_mul, integral_shadow_profile L hL n]
      ring

theorem prod_real_eq_integral_fiber
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite ν]
    {S : Set (α × β)} (hS : MeasurableSet S) (hSfinite : (μ.prod ν) S ≠ ⊤) :
    (μ.prod ν).real S = ∫ x, ν.real (Prod.mk x ⁻¹' S) ∂μ := by
  have hm := measurable_measure_prodMk_left (ν := ν) hS
  have hfinite : (∫⁻ x, ν (Prod.mk x ⁻¹' S) ∂μ) ≠ ⊤ := by
    rwa [← Measure.prod_apply hS]
  rw [Measure.real, Measure.prod_apply hS]
  exact (integral_toReal hm.aemeasurable (ae_lt_top hm hfinite)).symm

theorem integrable_fiber_measure
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite ν]
    {S : Set (α × β)} (hS : MeasurableSet S) (hSfinite : (μ.prod ν) S ≠ ⊤) :
    Integrable (fun x => ν.real (Prod.mk x ⁻¹' S)) μ := by
  have hm := measurable_measure_prodMk_left (ν := ν) hS
  have hfinite : (∫⁻ x, ν (Prod.mk x ⁻¹' S) ∂μ) ≠ ⊤ := by
    rwa [← Measure.prod_apply hS]
  exact (integrable_toReal_iff hm.aemeasurable
    ((ae_lt_top hm hfinite).mono fun _ h => h.ne)).mpr hfinite

theorem prod_real_eq_area_mul_length_div
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite ν]
    {S : Set (α × β)} (hS : MeasurableSet S) (hSfinite : (μ.prod ν) S ≠ ⊤)
    (A L : ℝ) (hL : 0 < L) (n : ℕ)
    (hbound : (fun x => ν.real (Prod.mk x ⁻¹' S)) ≤ᵐ[μ] fun _ => L)
    (hprofile : ∀ s ∈ Ioo (0 : ℝ) L,
      μ.real {x | s ≤ ν.real (Prod.mk x ⁻¹' S)} = A * (1 - s / L) ^ n) :
    (μ.prod ν).real S = A * L / (n + 1 : ℝ) := by
  rw [prod_real_eq_integral_fiber μ ν hS hSfinite]
  exact integral_eq_area_mul_length_div μ _ A L hL n
    (integrable_fiber_measure μ ν hS hSfinite)
    (.of_forall fun _ => ENNReal.toReal_nonneg) hbound hprofile

theorem compact_fiber {E : Type*} [NormedAddCommGroup E]
    {S : Set (E × ℝ)} (hS : IsCompact S) (x : E) :
    IsCompact (Prod.mk x ⁻¹' S) := by
  have hi : Isometry (Prod.mk x : ℝ → E × ℝ) := by
    apply isometry_iff_dist_eq.mpr
    intro a b
    simp
  exact hi.isClosedEmbedding.isCompact_preimage hS

theorem convex_fiber {E : Type*} [AddCommGroup E] [Module ℝ E]
    {S : Set (E × ℝ)} (hS : Convex ℝ S) (x : E) :
    Convex ℝ (Prod.mk x ⁻¹' S) :=
  hS.affine_preimage ((AffineMap.const ℝ ℝ x).prod (AffineMap.id ℝ ℝ))

theorem le_fiber_measure_iff_exists_segment
    {T : Set ℝ} (hT : IsCompact T) (hconv : Convex ℝ T)
    {s : ℝ} (hs : 0 < s) :
    s ≤ volume.real T ↔ ∃ t : ℝ, t ∈ T ∧ t + s ∈ T := by
  by_cases hne : T.Nonempty
  · let a := sInf T
    let b := sSup T
    have hI : T = Icc a b := eq_Icc_of_connected_compact (hconv.isConnected hne) hT
    have hab : a ≤ b := by
      have ha : a ∈ T := hT.sInf_mem hne
      rw [hI] at ha
      exact ha.2
    rw [hI, Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
    constructor
    · intro h
      refine ⟨a, ⟨le_rfl, hab⟩, ?_⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨t, ht, hts⟩
      linarith [ht.1, hts.2]
  · have hzero : T = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp [hzero, not_le.mpr hs]

theorem fiber_superlevel_eq_projected_overlap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set (E × ℝ)} (hS : IsCompact S) (hconv : Convex ℝ S)
    {s : ℝ} (hs : 0 < s) :
    {x | s ≤ volume.real (Prod.mk x ⁻¹' S)} =
      Prod.fst '' {z : E × ℝ | z ∈ S ∧ (z.1, z.2 + s) ∈ S} := by
  ext x
  change (s ≤ volume.real (Prod.mk x ⁻¹' S)) ↔ _
  rw [le_fiber_measure_iff_exists_segment (compact_fiber hS x) (convex_fiber hconv x) hs]
  constructor
  · rintro ⟨t, ht, hts⟩
    exact ⟨(x,t), ⟨ht,hts⟩, rfl⟩
  · rintro ⟨⟨y,t⟩, ⟨ht,hts⟩, hxy⟩
    change y = x at hxy
    subst y
    exact ⟨t,ht,hts⟩

theorem fiber_measure_le_of_chord_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set (E × ℝ)} (hS : IsCompact S) (hconv : Convex ℝ S)
    {L : ℝ} (hL : 0 ≤ L)
    (hchord : ∀ x : E, ∀ t r : ℝ, (x,t) ∈ S → (x,r) ∈ S → r - t ≤ L)
    (x : E) : volume.real (Prod.mk x ⁻¹' S) ≤ L := by
  by_cases hpos : 0 < volume.real (Prod.mk x ⁻¹' S)
  · obtain ⟨t, ht, htr⟩ :=
      (le_fiber_measure_iff_exists_segment (compact_fiber hS x)
        (convex_fiber hconv x) hpos).mp le_rfl
    have h := hchord x t (t + volume.real (Prod.mk x ⁻¹' S)) ht htr
    linarith
  · exact (le_of_not_gt hpos).trans hL

theorem compact_convex_prod_volume_of_overlap_profile
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) {S : Set (E × ℝ)}
    (hS : IsCompact S) (hconv : Convex ℝ S)
    (hSfinite : (μ.prod volume) S ≠ ⊤)
    (A L : ℝ) (hL : 0 < L) (n : ℕ)
    (hchord : ∀ x : E, ∀ t r : ℝ, (x,t) ∈ S → (x,r) ∈ S → r - t ≤ L)
    (hprofile : ∀ s ∈ Ioo (0 : ℝ) L,
      μ.real (Prod.fst '' {z : E × ℝ | z ∈ S ∧ (z.1, z.2 + s) ∈ S}) =
        A * (1 - s / L) ^ n) :
    (μ.prod volume).real S = A * L / (n + 1 : ℝ) := by
  apply prod_real_eq_area_mul_length_div μ volume hS.measurableSet hSfinite A L hL n
  · exact .of_forall (fiber_measure_le_of_chord_bound hS hconv hL.le hchord)
  · intro s hs
    rw [fiber_superlevel_eq_projected_overlap hS hconv hs.1]
    exact hprofile s hs

end CylinderCovering.SimplexLayerCake

end

end OAI
