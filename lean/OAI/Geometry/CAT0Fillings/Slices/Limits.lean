import Mathlib
import OAI.Geometry.CAT0Fillings.Slicing.Superlevels
import OAI.Geometry.CAT0Fillings.Currents.WeakMeasures

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Slicing
open Foundations MassMeasure BorelCoefficients BorelRestriction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X]

lemma restrictCurrent_mass_le {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) {E : Set X} (hE : MeasurableSet E) :
    mass (restrictCurrent hT E) ≤ mass T := by
  rw [restriction_mass hT hE, ← currentMassMeasure_total hT]
  exact measureReal_mono (subset_univ E)

lemma restrictCurrent_empty {k : ℕ} {T : Functional X k} (hT : IsMetricCurrent T) :
    restrictCurrent hT ∅ = 0 := by
  apply (restrictCurrent_isMetricCurrent hT MeasurableSet.empty).eq_zero_of_mass_eq_zero
  rw [restriction_mass hT MeasurableSet.empty]
  simp

lemma restrictCurrent_univ {k : ℕ} {T : Functional X k} (hT : IsMetricCurrent T) :
    restrictCurrent hT univ = T := by
  funext b π
  by_cases h : Admissible b π
  · rw [restrictCurrent_apply hT univ h, Set.indicator_univ]
    exact borelAction_eq _ hT (currentMassMeasure_controls hT) h
  · simp [restrictCurrent, h, hT.offDomain b π h]

lemma superlevelSlice_eq_zero_outside {k : ℕ} {T : Functional X (k+1)}
    (hT : IsMetricCurrent T) (hB : IsMetricCurrent (boundarySucc T))
    {u : X → ℝ} {R : ℝ} (hR : ∀ x, |u x| ≤ R) {t : ℝ}
    (ht : t ∉ Icc (-R) R) : superlevelSlice hT hB u t = 0 := by
  have ht' : t < -R ∨ R < t := by simpa only [mem_Icc, not_and_or, not_le] using ht
  unfold superlevelSlice
  rcases ht' with ht | ht
  · have he : {x | t < u x} = univ := by
      ext x
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      exact ht.trans_le (abs_le.mp (hR x)).1
    rw [he, restrictCurrent_univ, restrictCurrent_univ, sub_self]
  · have he : {x | t < u x} = ∅ := by
      ext x
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
      exact ((abs_le.mp (hR x)).2).trans ht.le
    rw [he, restrictCurrent_empty, restrictCurrent_empty]
    ext b π
    simp [boundarySucc]

lemma superlevelSlice_bound_uniform {k : ℕ} {T : Functional X (k+1)}
    (hT : IsMetricCurrent T) (hB : IsMetricCurrent (boundarySucc T))
    {u : X → ℝ} (hu : Continuous u) (t : ℝ)
    {b : X → ℝ} {Kb B : ℝ≥0} (hb : LipschitzWith Kb b) (hBnd : ∀ x, |b x| ≤ B)
    {π : Fin k → X → ℝ} (K : Fin k → ℝ≥0) (hK : ∀ i, LipschitzWith (K i) (π i)) :
    |superlevelSlice hT hB u t b π| ≤
       ((∏ i, (K i : ℝ)) * B) * mass (boundarySucc T) +
       ((Kb : ℝ) * ∏ i, (K i : ℝ)) * mass T := by
  let E := {x | t < u x}
  have hE : MeasurableSet E := measurableSet_lt measurable_const hu.measurable
  have hbl : BoundedLip b := ⟨⟨Kb, hb⟩, B, hBnd⟩
  have hadm : Admissible b π := ⟨hbl, fun i => ⟨K i, hK i⟩⟩
  have hp : ∀ i, LipschitzWith ((Matrix.vecCons Kb K) i) ((Matrix.vecCons b π) i) :=
    fun i => Fin.cases hb (fun j => hK j) i
  change |restrictCurrent hB E b π - boundarySucc (restrictCurrent hT E) b π| ≤ _
  apply (abs_sub _ _).trans
  apply add_le_add
  · exact ((restrictCurrent_isMetricCurrent hB hE).mass_bound_uniform hbl K hK hBnd).trans
      (mul_le_mul_of_nonneg_left (restrictCurrent_mass_le hB hE) (by positivity))
  · rw [boundarySucc, ite_eq_left hadm]
    have h := (restrictCurrent_isMetricCurrent hT hE).mass_bound_uniform (BoundedLip.const 1)
      (Matrix.vecCons Kb K) hp (M := 1) (fun _ => by simp)
    simp only [Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, mul_one] at h
    exact h.trans (mul_le_mul_of_nonneg_left (restrictCurrent_mass_le hT hE) (by positivity))

lemma superlevelSlice_integral [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
    (hT : IsIntegral (k+1) T) (hX : IsCAT0 X)
    {u : X → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u)
    {b : X → ℝ} {π : Fin k → X → ℝ} (h : Admissible b π) :
    Integrable (fun t : ℝ => superlevelSlice hT.1 hT.2.2.1 u t b π) ∧
      T b (Matrix.vecCons u π) = ∫ t : ℝ, superlevelSlice hT.1 hT.2.2.1 u t b π := by
  obtain ⟨S,G,hG,hG0,hS,hGI,hact,hweight⟩ := integerRectifiable_scalar_coarea hT.1 hT.2.1 hX hK
  have heq := ae_superlevelSlice_eq_coarea hT.1 hT.2.1 hT.2.2.1
    (boundedLip_of_lipschitz hK) (hS.mono fun t ht => ht.1) hact hweight
  have htest : (fun t : ℝ => S t b π) =ᵐ[volume]
      (fun t => superlevelSlice hT.1 hT.2.2.1 u t b π) :=
    heq.mono fun t ht => (congrFun (congrFun ht b) π).symm
  exact ⟨(hact b π h).1.congr htest, (hact b π h).2.trans (integral_congr_ae htest)⟩

theorem superlevelSlice_integral_of_bounded_weak_limit [Nonempty X]
    {k : ℕ} {Ts : ℕ → Functional X (k+1)} {T : Functional X (k+1)}
    (hTs : ∀ j, IsIntegral (k+1) (Ts j))
    (hT : IsMetricCurrent T) (hB : IsMetricCurrent (boundarySucc T))
    (M N : ℝ≥0) (hM : ∀ j, mass (Ts j) ≤ M)
    (hN : ∀ j, mass (boundarySucc (Ts j)) ≤ N)
    (hlim : ∀ b π, Tendsto (fun j => Ts j b π) atTop (𝓝 (T b π)))
    (hX : IsCAT0 X) {u : X → ℝ} {Ku : ℝ≥0} (hu : LipschitzWith Ku u)
    {b : X → ℝ} {π : Fin k → X → ℝ} (hab : Admissible b π) :
    Integrable (fun t : ℝ => superlevelSlice hT hB u t b π) ∧
      T b (Matrix.vecCons u π) = ∫ t : ℝ, superlevelSlice hT hB u t b π := by
  obtain ⟨ψ,hψ,μs,νs,μ,ν,hμs,hμ,hνs,hν,hμlim,hνlim⟩ :=
    exists_joint_weak_controlling_subsequence (fun j => (hTs j).1)
      (fun j => (hTs j).2.2.1) M N hM hN hlim (boundarySucc_weak_limit hlim)
  have hweak := ae_superlevelSlice_weak_tendsto (fun j => (hTs (ψ j)).1) hT
    (fun j => (hTs (ψ j)).2.2.1) hB μs νs μ ν hμs hμ hνs hν hμlim hνlim
    (fun b π => (hlim b π).comp hψ.tendsto_atTop) (boundedLip_of_lipschitz hu)
  let F (j : ℕ) (t : ℝ) := superlevelSlice (hTs (ψ j)).1 (hTs (ψ j)).2.2.1 u t b π
  let f (t : ℝ) := superlevelSlice hT hB u t b π
  have hact j := superlevelSlice_integral (hTs (ψ j)) hX hu hab
  have hFi (j : ℕ) : Integrable (F j) := (hact j).1
  have hconv : ∀ᵐ t : ℝ, Tendsto (fun j => F j t) atTop (𝓝 (f t)) :=
    hweak.mono fun t ht => ht b π
  obtain ⟨Kb,hKb⟩ := hab.1.1
  obtain ⟨B₀,hB₀⟩ := hab.1.2
  let B : ℝ≥0 := ⟨max B₀ 0, le_max_right _ _⟩
  have hB' (x : X) : |b x| ≤ B := (hB₀ x).trans (le_max_left _ _)
  choose K hK using hab.2
  obtain ⟨R,hR⟩ := (boundedLip_of_lipschitz hu).2
  let C : ℝ := ((∏ i, (K i : ℝ)) * B) * N +
    ((Kb : ℝ) * ∏ i, (K i : ℝ)) * M
  let bound : ℝ → ℝ := (Icc (-R) R).indicator (fun _ => C)
  have hboundi : Integrable bound :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const isCompact_Icc.measure_ne_top)
  have hbound (j : ℕ) (t : ℝ) : ‖F j t‖ ≤ bound t := by
    by_cases ht : t ∈ Icc (-R) R
    · simp only [bound, indicator_of_mem ht, Real.norm_eq_abs]
      exact (superlevelSlice_bound_uniform (hTs (ψ j)).1 (hTs (ψ j)).2.2.1
        hu.continuous t hKb hB' K hK).trans
        (add_le_add (mul_le_mul_of_nonneg_left (hN (ψ j)) (by positivity))
          (mul_le_mul_of_nonneg_left (hM (ψ j)) (by positivity)))
    · have hz := superlevelSlice_eq_zero_outside (hTs (ψ j)).1 (hTs (ψ j)).2.2.1 hR ht
      have he : F j t = 0 := congrFun (congrFun hz b) π
      simp [he, bound, ht]
  have hfi : Integrable f := hboundi.mono'
    (aestronglyMeasurable_of_tendsto_ae atTop (fun j => (hFi j).aestronglyMeasurable) hconv)
    (hconv.mono fun t ht => le_of_tendsto' ht.norm (fun j => hbound j t))
  have hlimI := tendsto_integral_of_dominated_convergence bound
    (fun j => (hFi j).aestronglyMeasurable) hboundi
    (fun j => Eventually.of_forall (hbound j)) hconv
  have heqI : (fun j => ∫ t : ℝ, F j t) = (fun j => Ts (ψ j) b (Matrix.vecCons u π)) :=
    funext fun j => (hact j).2.symm
  rw [heqI] at hlimI
  exact ⟨hfi, tendsto_nhds_unique ((hlim b (Matrix.vecCons u π)).comp hψ.tendsto_atTop) hlimI⟩

end CAT0Fillings.Slicing
end

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Slicing
open Foundations MassMeasure BorelCoefficients BorelRestriction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X]

lemma mass_le_liminf_upper {k : ℕ} {Ts : ℕ → Functional X k}
    {T : Functional X k} {G : ℕ → ℝ}
    (hTs : ∀ j, IsMetricCurrent (Ts j)) (hG : ∀ j, mass (Ts j) ≤ G j)
    (hlim : ∀ b π, Admissible b π → Tendsto (fun j => Ts j b π) atTop (𝓝 (T b π)))
    (hfin : liminf (fun j => ENNReal.ofReal (G j)) atTop ≠ ⊤) :
    mass T ≤ (liminf (fun j => ENNReal.ofReal (G j)) atTop).toReal := by
  by_contra h
  obtain ⟨r,hr₁,hr₂⟩ := exists_between (lt_of_not_ge h)
  have hr0 : 0 ≤ r := ENNReal.toReal_nonneg.trans hr₁.le
  have hlt : liminf (fun j => ENNReal.ofReal (G j)) atTop < ENNReal.ofReal r :=
    (ENNReal.lt_ofReal_iff_toReal_lt hfin).mpr hr₁
  obtain ⟨ψ,hψ,hψG⟩ := extraction_of_frequently_atTop
    (frequently_lt_of_liminf_lt (u := fun j => ENNReal.ofReal (G j)) (h := hlt))
  have hb : ∀ j, mass (Ts (ψ j)) ≤ (⟨r,hr0⟩ : ℝ≥0) := by
    intro j
    exact (hG (ψ j)).trans ((ENNReal.ofReal_le_ofReal_iff hr0).mp (hψG j).le)
  have hm := mass_le_of_bounded_weak_limit (⟨r,hr0⟩ : ℝ≥0)
    (fun j => hTs (ψ j)) hb (fun b π h => (hlim b π h).comp hψ.tendsto_atTop)
  exact (not_le_of_gt hr₂) hm

lemma exists_integrable_mass_upper_of_ae_weak_limit {A : Type*} [MeasurableSpace A]
    (μ : Measure A) {k : ℕ} {Ts : ℕ → A → Functional X k}
    {T : A → Functional X k} {G : ℕ → A → ℝ}
    (hTs : ∀ j, ∀ᵐ x ∂μ, IsMetricCurrent (Ts j x))
    (hG : ∀ j, Integrable (G j) μ) (hG0 : ∀ j, ∀ᵐ x ∂μ, 0 ≤ G j x)
    (hbound : ∀ j, ∀ᵐ x ∂μ, mass (Ts j x) ≤ G j x)
    (hlim : ∀ᵐ x ∂μ, ∀ b π, Admissible b π →
      Tendsto (fun j => Ts j x b π) atTop (𝓝 (T x b π)))
    (C : ℝ) (hC : ∀ j, (∫ x, G j x ∂μ) ≤ C) :
    ∃ g : A → ℝ, Integrable g μ ∧ (∀ x, 0 ≤ g x) ∧
      (∀ᵐ x ∂μ, mass (T x) ≤ g x) ∧ (∫ x, g x ∂μ) ≤ max C 0 := by
  let hm (j : ℕ) := (hG j).aemeasurable.ennreal_ofReal
  let f (j : ℕ) : A → ℝ≥0∞ := (hm j).mk _
  have hf (j : ℕ) : Measurable (f j) := (hm j).measurable_mk
  have heq (j : ℕ) : (fun x => ENNReal.ofReal (G j x)) =ᵐ[μ] f j := (hm j).ae_eq_mk
  let H : A → ℝ≥0∞ := fun x => liminf (fun j => f j x) atTop
  have hHm : Measurable H := Measurable.liminf hf
  have hI (j : ℕ) : (∫⁻ x, f j x ∂μ) ≤ ENNReal.ofReal C := by
    rw [←lintegral_congr_ae (heq j),←ofReal_integral_eq_lintegral_ofReal (hG j) (hG0 j)]
    exact ENNReal.ofReal_le_ofReal (hC j)
  have hHI : (∫⁻ x, H x ∂μ) ≤ ENNReal.ofReal C :=
    (lintegral_liminf_le hf).trans (liminf_le_of_frequently_le (Frequently.of_forall hI))
  have hHfin : (∫⁻ x, H x ∂μ) ≠ ⊤ := (hHI.trans_lt ENNReal.ofReal_lt_top).ne
  have hafin := ae_lt_top hHm hHfin
  refine ⟨fun x => (H x).toReal, ?_, fun x => ENNReal.toReal_nonneg, ?_, ?_⟩
  · exact integrable_toReal_of_lintegral_ne_top hHm.aemeasurable hHfin
  · filter_upwards [hafin,ae_all_iff.mpr heq,ae_all_iff.mpr hTs,
      ae_all_iff.mpr hbound,hlim] with x hx he ht hb hl
    have he' : (fun j => ENNReal.ofReal (G j x)) = (fun j => f j x) := funext he
    dsimp [H] at hx ⊢
    rw [←he'] at hx ⊢
    exact mass_le_liminf_upper ht hb hl hx.ne
  · rw [integral_toReal hHm.aemeasurable hafin]
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hHI
    simpa only [ENNReal.toReal_ofReal'] using this

theorem superlevelSlice_mass_bound_of_bounded_weak_limit [Nonempty X]
    {k : ℕ} {Ts : ℕ → Functional X (k+1)} {T : Functional X (k+1)}
    (hTs : ∀ j, IsIntegral (k+1) (Ts j))
    (hT : IsMetricCurrent T) (hB : IsMetricCurrent (boundarySucc T))
    (M N : ℝ≥0) (hM : ∀ j, mass (Ts j) ≤ M)
    (hN : ∀ j, mass (boundarySucc (Ts j)) ≤ N)
    (hlim : ∀ b π, Tendsto (fun j => Ts j b π) atTop (𝓝 (T b π)))
    (hX : IsCAT0 X) {u : X → ℝ} {Ku : ℝ≥0} (hu : LipschitzWith Ku u) :
    ∃ g : ℝ → ℝ, Integrable g ∧ (∀ t, 0 ≤ g t) ∧
      (∀ᵐ t : ℝ, mass (superlevelSlice hT hB u t) ≤ g t) ∧
      (∫ t : ℝ, g t) ≤ Ku * M := by
  obtain ⟨ψ,hψ,μs,νs,μ,ν,hμs,hμ,hνs,hν,hμlim,hνlim⟩ :=
    exists_joint_weak_controlling_subsequence (fun j => (hTs j).1)
      (fun j => (hTs j).2.2.1) M N hM hN hlim (boundarySucc_weak_limit hlim)
  have hweak := ae_superlevelSlice_weak_tendsto (fun j => (hTs (ψ j)).1) hT
    (fun j => (hTs (ψ j)).2.2.1) hB μs νs μ ν hμs hμ hνs hν hμlim hνlim
    (fun b π => (hlim b π).comp hψ.tendsto_atTop) (boundedLip_of_lipschitz hu)
  choose G hG hG0 hGI hS using fun j => superlevelSlice_coarea_bound (hTs (ψ j)) hX hu
  have hGI' (j : ℕ) : (∫ t : ℝ, G j t) ≤ (Ku : ℝ) * M :=
    (hGI j).trans (mul_le_mul_of_nonneg_left (hM (ψ j)) Ku.coe_nonneg)
  obtain ⟨g,hg,hg0,hgb,hgI⟩ := exists_integrable_mass_upper_of_ae_weak_limit volume
    (fun j => (hS j).mono fun t ht => ht.1) hG
    (fun j => Eventually.of_forall (hG0 j))
    (fun j => (hS j).mono fun t ht => ht.2.2)
    (hweak.mono fun t ht b π _ => ht b π) ((Ku : ℝ) * M) hGI'
  refine ⟨g,hg,hg0,hgb,?_⟩
  simpa only [max_eq_left (mul_nonneg Ku.coe_nonneg M.coe_nonneg)] using hgI

end CAT0Fillings.Slicing
end

end OAI
