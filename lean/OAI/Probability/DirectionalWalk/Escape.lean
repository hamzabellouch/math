import OAI.Probability.DirectionalWalk.Avoidance

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

def height {d : ℕ} (v : Fin d → ℝ) (x : Site d) : ℝ := ∑ i, (x i : ℝ) * v i

lemma height_zero {d : ℕ} (v : Fin d → ℝ) : height v 0 = 0 := by simp [height]

lemma height_add {d : ℕ} (v : Fin d → ℝ) (x y : Site d) :
    height v (x+y) = height v x + height v y := by
  simp only [height, Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]

lemma height_neg {d : ℕ} (v : Fin d → ℝ) (x : Site d) :
    height v (-x) = -height v x := by simp [height, Finset.sum_neg_distrib]

def neverBelow {d : ℕ} (v : Fin d → ℝ) (a : ℝ) : Set (Path d) :=
  {X | ∀ n, a ≤ height v (X n)}

def nonBacktracking {d : ℕ} (v : Fin d → ℝ) : Set (Path d) := neverBelow v 0

lemma measurableSet_neverBelow {d : ℕ} (v : Fin d → ℝ) (a : ℝ) :
    MeasurableSet (neverBelow v a) := by
  simp only [neverBelow, Set.ofPred_forall]
  exact MeasurableSet.iInter (fun n => measurableSet_le measurable_const
    ((measurable_of_countable (height v)).comp (measurable_pi_apply n)))

lemma measurableSet_nonBacktracking {d : ℕ} (v : Fin d → ℝ) :
    MeasurableSet (nonBacktracking v) := measurableSet_neverBelow v 0

lemma shiftPath_preimage_neverBelow {d : ℕ} (v : Fin d → ℝ) (z : Site d) :
    shiftPath z ⁻¹' neverBelow v (height v z) = nonBacktracking v := by
  ext X
  simp only [Set.mem_preimage, neverBelow, nonBacktracking, Set.mem_ofPred_eq,
    shiftPath, height_add, le_add_iff_nonneg_left]

lemma annealed_neverBelow_start {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (v : Fin d → ℝ) (x : Site d) :
    annealed μ x (neverBelow v (height v x)) = annealed μ 0 (nonBacktracking v) := by
  have h := congrArg (fun ξ : Measure (Path d) => ξ (neverBelow v (height v x)))
    (annealed_shift μ 0 x)
  rw [Measure.map_apply (measurable_shiftPath x) (measurableSet_neverBelow v _),
    shiftPath_preimage_neverBelow, zero_add] at h
  exact h.symm

lemma annealed_prefix_tail_null {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x : Site d) (n : ℕ) (γ : Path d) {E : Set (Path d)} (hE : MeasurableSet E)
    (hzero : annealed μ (γ n) E = 0) :
    annealed μ x (pathCylinder n γ ∩ tailPath n ⁻¹' E) = 0 := by
  have hae : ∀ᵐ ω ∂environmentLaw μ, quenchedKernel d (ω,γ n) E = 0 := by
    apply (lintegral_eq_zero_iff
      ((Kernel.measurable_coe _ hE).comp (measurable_id.prodMk measurable_const))).mp
    change (∫⁻ ω, quenchedKernel d (ω,γ n) E ∂environmentLaw μ) = 0
    rw [← annealed_apply μ (γ n) hE]
    exact hzero
  rw [annealed_apply μ x ((measurableSet_pathCylinder n γ).inter ((measurable_tailPath n) hE))]
  calc
    _ = ∫⁻ _ : Environment d, (0 : ℝ≥0∞) ∂environmentLaw μ := by
      apply lintegral_congr_ae
      filter_upwards [hae] with ω hω
      rw [quenched_prefix_tail_apply _ _ _ _ hE, hω, mul_zero]
    _ = 0 := lintegral_zero

def extendPrefix {d : ℕ} (n : ℕ) (a : Finset.Iic n → Site d) : Path d :=
  fun i => if hi : i ∈ Finset.Iic n then a ⟨i,hi⟩ else 0

lemma extendPrefix_apply {d : ℕ} (n : ℕ) (a : Finset.Iic n → Site d) {i : ℕ} (hi : i ≤ n) :
    extendPrefix n a i = a ⟨i, Finset.mem_Iic.mpr hi⟩ := by
  simp only [extendPrefix, dite_eq_left (Finset.mem_Iic.mpr hi)]

lemma restrict_extendPrefix {d : ℕ} (n : ℕ) (a : Finset.Iic n → Site d) :
    frestrictLe n (extendPrefix n a) = a := by
  funext i
  exact extendPrefix_apply n a (Finset.mem_Iic.mp i.property)

lemma set_eq_iUnion_prefix_inter {d : ℕ} (E : Set (Path d)) (n : ℕ) :
    E = ⋃ a : Finset.Iic n → Site d, E ∩ pathCylinder n (extendPrefix n a) := by
  ext X
  simp only [Set.mem_iUnion, Set.mem_inter_iff]
  constructor
  · intro hX
    refine ⟨frestrictLe n X, hX, fun i hi => ?_⟩
    rw [extendPrefix_apply n _ hi]
    rfl
  · rintro ⟨a,hX,_⟩
    exact hX

lemma measure_zero_of_prefix_inter {d : ℕ} (μ : Measure (Path d)) (n : ℕ)
    (E : Set (Path d)) (h : ∀ a : Finset.Iic n → Site d,
      μ (E ∩ pathCylinder n (extendPrefix n a)) = 0) : μ E = 0 := by
  rw [set_eq_iUnion_prefix_inter E n]
  exact measure_iUnion_null h

lemma annealed_tail_start_null {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (y x : Site d) (n : ℕ) {E : Set (Path d)} (hE : MeasurableSet E)
    (hzero : annealed μ x E = 0) :
    annealed μ y ({X | X n = x} ∩ tailPath n ⁻¹' E) = 0 := by
  classical
  apply measure_zero_of_prefix_inter _ n
  intro a
  let γ := extendPrefix n a
  by_cases hx : γ n = x
  · apply measure_mono_null _ (annealed_prefix_tail_null μ y n γ hE (by simpa [hx] using hzero))
    rintro X ⟨⟨_,hX⟩,hC⟩
    exact ⟨hC,hX⟩
  · have he : ({X : Path d | X n = x} ∩ tailPath n ⁻¹' E) ∩ pathCylinder n γ = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro X ⟨⟨hX,_⟩,hC⟩
      exact hx ((hC n le_rfl).symm.trans hX)
    rw [he, measure_empty]

lemma escape_subset_globalMinimum_suffix {d : ℕ} (v : Fin d → ℝ) :
    escape v ⊆ ⋃ n : ℕ, ⋃ x : Site d,
      {X | X n = x} ∩ tailPath n ⁻¹' neverBelow v (height v x) := by
  intro X hX
  have ht : Tendsto (fun n => height v (X n)) cofinite atTop := by
    simpa only [Nat.cofinite_eq_atTop, height] using (show Tendsto (fun n => ∑ i, (X n i : ℝ) * v i) atTop atTop from hX)
  obtain ⟨n,hn⟩ := ht.exists_forall_le
  apply Set.mem_iUnion.mpr
  refine ⟨n, Set.mem_iUnion.mpr ⟨X n, rfl, ?_⟩⟩
  intro k
  exact hn (n+k)

lemma positive_nonBacktracking {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (v : Fin d → ℝ) (hescape : 0 < annealed μ 0 (escape v)) :
    0 < annealed μ 0 (nonBacktracking v) := by
  by_contra h
  have hz : annealed μ 0 (nonBacktracking v) = 0 :=
    le_antisymm (le_of_not_gt h) (zero_le)
  have hnull : annealed μ 0 (⋃ n : ℕ, ⋃ x : Site d,
      {X | X n = x} ∩ tailPath n ⁻¹' neverBelow v (height v x)) = 0 := by
    apply measure_iUnion_null
    intro n
    apply measure_iUnion_null
    intro x
    apply annealed_tail_start_null μ 0 x n (measurableSet_neverBelow v _)
    rw [annealed_neverBelow_start, hz]
  exact (ne_of_gt hescape) (measure_mono_null (escape_subset_globalMinimum_suffix v) hnull)

lemma annealed_record_tail {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (v : Fin d → ℝ) (x : Site d) (n : ℕ) (γ : Path d)
    (hrec : ∀ i < n, height v (γ i) < height v (γ n))
    {E : Set (Path d)} (hE : MeasurableSet E)
    (hD : E ⊆ neverBelow v (height v (γ n))) :
    annealed μ x (pathCylinder n γ ∩ tailPath n ⁻¹' E) =
      annealed μ x (pathCylinder n γ) * annealed μ (γ n) E := by
  let K : Set (Site d) := {y | height v y < height v (γ n)}
  have hav : E ⊆ avoids K := by
    intro X hX i hi
    exact (not_lt_of_ge (hD hX i)) hi
  have hEq : E ∩ avoids K = E := Set.inter_eq_left.mpr hav
  simpa only [hEq] using annealed_fresh_prefix_tail μ K x n γ hrec hE

lemma annealed_record_relative_tail {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (v : Fin d → ℝ) (x : Site d) (n : ℕ) (γ : Path d)
    (hrec : ∀ i < n, height v (γ i) < height v (γ n))
    {E : Set (Path d)} (hE : MeasurableSet E) :
    annealed μ x (pathCylinder n γ ∩
      tailPath n ⁻¹' (shiftPath (-(γ n)) ⁻¹' (E ∩ nonBacktracking v))) =
      annealed μ x (pathCylinder n γ) * annealed μ 0 (E ∩ nonBacktracking v) := by
  have hF := hE.inter (measurableSet_nonBacktracking v)
  rw [annealed_record_tail μ v x n γ hrec ((measurable_shiftPath _) hF)]
  · congr 1
    have h := congrArg (fun ξ : Measure (Path d) =>
      ξ (shiftPath (-(γ n)) ⁻¹' (E ∩ nonBacktracking v))) (annealed_shift μ 0 (γ n))
    rw [Measure.map_apply (measurable_shiftPath _) ((measurable_shiftPath _) hF), zero_add] at h
    have heq : shiftPath (γ n) ⁻¹' (shiftPath (-(γ n)) ⁻¹' (E ∩ nonBacktracking v)) =
        E ∩ nonBacktracking v := by
      ext X
      simp only [Set.mem_preimage]
      have hs : shiftPath (-(γ n)) (shiftPath (γ n) X) = X := by
        funext i
        simp [shiftPath]
      rw [hs]
    rw [heq] at h
    exact h.symm
  · intro X hX i
    have hi := hX.2 i
    change 0 ≤ height v (X i + -(γ n)) at hi
    rw [height_add, height_neg] at hi
    linarith

def pathFiltration (d : ℕ) : Filtration ℕ (inferInstance : MeasurableSpace (Path d)) :=
  Filtration.piLE

lemma pathFiltration_eq {d : ℕ} (n : ℕ) : pathFiltration d n =
    MeasurableSpace.comap (frestrictLe n : Path d → _) inferInstance :=
  Filtration.piLE_eq_comap_frestrictLe n

lemma pathCylinder_eq_fiber {d : ℕ} (n : ℕ) (X : Path d) :
    pathCylinder n X = (frestrictLe n : Path d → (Finset.Iic n → Site d)) ⁻¹' {frestrictLe n X} := by
  ext Y
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro h
    funext i
    exact h i (Finset.mem_Iic.mp i.property)
  · intro h i hi
    exact congr_fun h ⟨i,Finset.mem_Iic.mpr hi⟩

lemma measurableSet_pathCylinder_filtration {d : ℕ} (n : ℕ) (X : Path d) :
    MeasurableSet[pathFiltration d n] (pathCylinder n X) := by
  rw [pathFiltration_eq, pathCylinder_eq_fiber]
  exact ⟨_, measurableSet_singleton _, rfl⟩

lemma pathFiltration_iSup (d : ℕ) : (⨆ n, pathFiltration d n) =
    (inferInstance : MeasurableSpace (Path d)) := by
  apply le_antisymm (iSup_le (pathFiltration d).le)
  have hi : @Measurable (Path d) (Path d) (⨆ n, pathFiltration d n) _ id := by
    apply @Measurable.of_eval (Path d) ℕ (fun _ => Site d) (⨆ n, pathFiltration d n) _
    intro n
    have hn : Measurable[pathFiltration d n] (fun X : Path d => X n) := by
      rw [pathFiltration_eq]
      exact (show Measurable (fun a : Finset.Iic n → Site d => a ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
        from measurable_pi_apply _).comp (Measurable.of_comap_le
          (f := (frestrictLe n : Path d → (Finset.Iic n → Site d))) le_rfl)
    exact hn.mono (le_iSup _ n) le_rfl
  simpa using hi.comap_le

lemma ae_pathCylinder_ne_zero {d : ℕ} (μ : Measure (Path d)) :
    ∀ᵐ X ∂μ, ∀ n, μ (pathCylinder n X) ≠ 0 := by
  have ha (n : ℕ) (a : Finset.Iic n → Site d) :
      ∀ᵐ X ∂μ, X ∈ pathCylinder n (extendPrefix n a) →
        μ (pathCylinder n (extendPrefix n a)) ≠ 0 := by
    by_cases hz : μ (pathCylinder n (extendPrefix n a)) = 0
    · have hh : ∀ᵐ X ∂μ, X ∉ pathCylinder n (extendPrefix n a) := by
        rw [ae_iff]
        simpa using hz
      filter_upwards [hh] with X hX using fun hx => (hX hx).elim
    · exact ae_of_all _ (fun _ _ => hz)
  filter_upwards [ae_all_iff.mpr (fun n => ae_all_iff.mpr (ha n))] with X hX
  intro n
  have heq : pathCylinder n (extendPrefix n (frestrictLe n X)) = pathCylinder n X := by
    rw [pathCylinder_eq_fiber, restrict_extendPrefix, ← pathCylinder_eq_fiber]
  have hmem : X ∈ pathCylinder n X := fun _ _ => rfl
  simpa only [heq] using hX n (frestrictLe n X) (heq.symm ▸ hmem)

lemma condExp_indicator_cylinder {d : ℕ} (μ : Measure (Path d)) [IsFiniteMeasure μ]
    {E : Set (Path d)} (hE : MeasurableSet E) (n : ℕ) (X : Path d) :
    μ.real (pathCylinder n X) * (μ[E.indicator (fun _ => (1 : ℝ)) | pathFiltration d n]) X =
      μ.real (E ∩ pathCylinder n X) := by
  let f := μ[E.indicator (fun _ => (1 : ℝ)) | pathFiltration d n]
  have hf : StronglyMeasurable[MeasurableSpace.comap (frestrictLe n) inferInstance] f := by
    rw [← pathFiltration_eq]
    exact stronglyMeasurable_condExp
  have hconst : ∫ Y in pathCylinder n X, f Y ∂μ =
      μ.real (pathCylinder n X) * f X := by
    calc
      _ = ∫ _ in pathCylinder n X, f X ∂μ := by
        apply setIntegral_congr_fun (measurableSet_pathCylinder n X)
        intro Y hY
        apply hf.factorsThrough
        simpa only [pathCylinder_eq_fiber, Set.mem_preimage, Set.mem_singleton_iff] using hY
      _ = _ := by rw [setIntegral_const, smul_eq_mul]
  rw [← hconst, setIntegral_condExp ((pathFiltration d).le n) (integrable_const 1 |>.indicator hE)
    (measurableSet_pathCylinder_filtration n X)]
  rw [setIntegral_indicator hE, setIntegral_const, smul_eq_mul, mul_one, Set.inter_comm]

lemma null_of_prefix_contraction {d : ℕ} (μ : Measure (Path d)) [IsFiniteMeasure μ]
    {E : Set (Path d)} (hE : MeasurableSet E) (c : ℝ) (hc : c < 1)
    (hcontract : ∀ X ∈ E, ∃ᶠ n in atTop,
      μ.real (E ∩ pathCylinder n X) ≤ c * μ.real (pathCylinder n X)) : μ E = 0 := by
  have hint : Integrable (E.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hE
  have hmeas : StronglyMeasurable[⨆ n, pathFiltration d n]
      (E.indicator (fun _ => (1 : ℝ))) := by
    rw [pathFiltration_iSup]
    exact stronglyMeasurable_const.indicator hE
  have ht := hint.tendsto_ae_condExp (ℱ := pathFiltration d) hmeas
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [ht, ae_pathCylinder_ne_zero μ] with X hX hpos
  intro hXE
  have htX : Tendsto (fun n => (μ[E.indicator (fun _ => (1 : ℝ)) | pathFiltration d n]) X)
      atTop (𝓝 (1 : ℝ)) := by simpa [hXE] using hX
  have hlow : ∃ᶠ n in atTop,
      (μ[E.indicator (fun _ => (1 : ℝ)) | pathFiltration d n]) X ≤ c := by
    apply (hcontract X hXE).mono
    intro n hn
    rw [← condExp_indicator_cylinder μ hE n X, mul_comm c] at hn
    exact (mul_le_mul_iff_right₀ (ENNReal.toReal_pos (hpos n) (measure_ne_top _ _))).mp hn
  have hhigh : ∀ᶠ n in atTop,
      c < (μ[E.indicator (fun _ => (1 : ℝ)) | pathFiltration d n]) X :=
    htX.eventually (lt_mem_nhds hc)
  exact (hlow.and_eventually hhigh).exists.elim (fun _ hh => (not_lt_of_ge hh.1) hh.2)

lemma real_contraction_of_disjoint_success {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {E C S : Set Ω}
    (hC : MeasurableSet C) (hS : MeasurableSet S)
    (hd : Disjoint (E ∩ C) (C ∩ S)) (q : ℝ)
    (hq : μ.real (C ∩ S) = q * μ.real C) :
    μ.real (E ∩ C) ≤ (1-q) * μ.real C := by
  have hu : (E ∩ C) ∪ (C ∩ S) ⊆ C := by
    rintro x (hx | hx)
    · exact hx.2
    · exact hx.1
  have hh := measureReal_mono (μ := μ) hu
  rw [measureReal_union hd (hC.inter hS), hq] at hh
  linarith

end DirectionalZeroOne

end OAI
