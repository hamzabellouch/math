import OAI.Probability.DirectionalWalk.Shifts

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

def avoidsThrough {d : ℕ} (K : Set (Site d)) (n : ℕ) : Set (Path d) :=
  {X | ∀ i ≤ n, X i ∉ K}

def avoids {d : ℕ} (K : Set (Site d)) : Set (Path d) := {X | ∀ i, X i ∉ K}

lemma measurableSet_avoidsThrough {d : ℕ} (K : Set (Site d)) (n : ℕ) :
    MeasurableSet (avoidsThrough K n) := by
  simp only [avoidsThrough, Set.ofPred_forall]
  exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun _ =>
    (show Measurable (fun X : Path d => X i) from measurable_pi_apply i)
      (Set.to_countable K).measurableSet.compl))

lemma measurableSet_avoids {d : ℕ} (K : Set (Site d)) : MeasurableSet (avoids K) := by
  simp only [avoids, Set.ofPred_forall]
  exact MeasurableSet.iInter (fun i =>
    (show Measurable (fun X : Path d => X i) from measurable_pi_apply i)
      (Set.to_countable K).measurableSet.compl)

lemma avoidsThrough_antitone {d : ℕ} (K : Set (Site d)) : Antitone (avoidsThrough K) := by
  intro n m hnm X hX i hi
  exact hX i (hi.trans hnm)

open Classical in
lemma cylinder_inter_avoidsThrough {d : ℕ} (K : Set (Site d)) (n : ℕ) (γ : Path d) :
    pathCylinder n γ ∩ avoidsThrough K n =
      if ∀ i ≤ n, γ i ∉ K then pathCylinder n γ else ∅ := by
  classical
  by_cases h : ∀ i ≤ n, γ i ∉ K
  · rw [ite_eq_left h]
    apply Set.inter_eq_left.mpr
    intro X hX i hi
    rw [hX i hi]
    exact h i hi
  · rw [ite_eq_right h]
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro X ⟨hX,hK⟩
    apply h
    intro i hi
    rw [← hX i hi]
    exact hK i hi

lemma pathWeight_congr_rows {d : ℕ} (ω ω' : Environment d) (n : ℕ) (γ : Path d)
    (h : ∀ i < n, ω (γ i) = ω' (γ i)) : pathWeight n γ ω = pathWeight n γ ω' := by
  apply Finset.prod_congr rfl
  intro i hi
  simp only [entryWeight, h i (Finset.mem_range.mp hi)]

lemma quenched_avoid_prefixMap {d : ℕ} (K : Set (Site d)) (ω ω' : Environment d)
    (h : ∀ y ∉ K, ω y = ω' y) (x : Site d) (n : ℕ) :
    ((quenchedKernel d (ω,x)).restrict (avoidsThrough K n)).map (frestrictLe n) =
      ((quenchedKernel d (ω',x)).restrict (avoidsThrough K n)).map (frestrictLe n) := by
  classical
  apply Measure.ext_of_singleton
  intro a
  let γ : Path d := fun i => if hi : i ∈ Finset.Iic n then a ⟨i,hi⟩ else 0
  have hγ : frestrictLe n γ = a := by
    funext i
    change (if hi : (i : ℕ) ∈ Finset.Iic n then a ⟨i,hi⟩ else 0) = a i
    rw [dite_eq_left i.property]
  rw [← hγ, Measure.map_apply (measurable_frestrictLe n) (measurableSet_singleton _),
    Measure.map_apply (measurable_frestrictLe n) (measurableSet_singleton _),
    prefix_preimage_singleton, Measure.restrict_apply (measurableSet_pathCylinder n γ),
    Measure.restrict_apply (measurableSet_pathCylinder n γ), cylinder_inter_avoidsThrough]
  by_cases hK : ∀ i ≤ n, γ i ∉ K
  · rw [ite_eq_left hK, quenchedKernel_cylinder, quenchedKernel_cylinder,
      pathWeight_congr_rows ω ω' n γ (fun i hi => h _ (hK i (le_of_lt hi)))]
  · rw [ite_eq_right hK]
    simp only [measure_empty]

lemma quenched_restrict_avoids_eq {d : ℕ} (K : Set (Site d)) (ω ω' : Environment d)
    (h : ∀ y ∉ K, ω y = ω' y) (x : Site d) :
    (quenchedKernel d (ω,x)).restrict (avoids K) =
      (quenchedKernel d (ω',x)).restrict (avoids K) := by
  apply pathMeasure_ext
  intro n γ
  rw [Measure.restrict_apply (measurableSet_pathCylinder n γ),
    Measure.restrict_apply (measurableSet_pathCylinder n γ)]
  let s : ℕ → Set (Path d) := fun m => pathCylinder n γ ∩ avoidsThrough K (n+m)
  have hsm : ∀ m, MeasurableSet (s m) := fun m =>
    (measurableSet_pathCylinder n γ).inter (measurableSet_avoidsThrough K (n+m))
  have hsa : Antitone s := by
    intro i j hij
    exact Set.inter_subset_inter_right _ (avoidsThrough_antitone K (Nat.add_le_add_left hij n))
  have hs : (⋂ m, s m) = pathCylinder n γ ∩ avoids K := by
    ext X
    simp only [Set.mem_iInter, Set.mem_inter_iff, s]
    constructor
    · intro hX
      refine ⟨(hX 0).1, fun i => ?_⟩
      exact (hX i).2 i (Nat.le_add_left i n)
    · rintro ⟨hX,hK⟩ m
      exact ⟨hX, fun i _ => hK i⟩
  have he : ∀ m, quenchedKernel d (ω,x) (s m) = quenchedKernel d (ω',x) (s m) := by
    intro m
    have hh := cylinder_measure_eq_of_prefixMap n
      (prefixMap_mono (Nat.le_add_right n m) (quenched_avoid_prefixMap K ω ω' h x (n+m))) γ
    simpa only [Measure.restrict_apply (measurableSet_pathCylinder n γ)] using hh
  have hω := tendsto_measure_iInter_atTop
    (fun m => (hsm m).nullMeasurableSet (μ := quenchedKernel d (ω,x))) hsa
    ⟨0, measure_ne_top _ _⟩
  have hω' := tendsto_measure_iInter_atTop
    (fun m => (hsm m).nullMeasurableSet (μ := quenchedKernel d (ω',x))) hsa
    ⟨0, measure_ne_top _ _⟩
  rw [hs] at hω hω'
  have heq : (quenchedKernel d (ω,x) ∘ s) = (quenchedKernel d (ω',x) ∘ s) := funext he
  rw [heq] at hω
  exact tendsto_nhds_unique hω hω'

noncomputable def maskEnvironment {d : ℕ} (K : Set (Site d)) (r : Row d)
    (ω : Environment d) : Environment d := by
  classical
  exact fun y => if y ∈ K then r else ω y

lemma measurable_maskEnvironment {d : ℕ} (K : Set (Site d)) (r : Row d) :
    @Measurable (Environment d) (Environment d) (rowSigma Kᶜ) _ (maskEnvironment K r) := by
  classical
  apply @Measurable.of_eval (Environment d) (Site d) (fun _ => Row d) (rowSigma Kᶜ) _
  intro y
  by_cases hy : y ∈ K
  · simpa only [maskEnvironment, ite_eq_left hy] using
      (measurable_const : @Measurable (Environment d) (Row d) (rowSigma Kᶜ) _ (fun _ => r))
  · simpa only [maskEnvironment, ite_eq_right hy] using
      (measurable_row (s := Kᶜ) (x := y) hy)

lemma measurable_quenched_avoids_on_rows {d : ℕ} (K : Set (Site d)) (r : Row d)
    (x : Site d) {E : Set (Path d)} (hE : MeasurableSet E) :
    @Measurable (Environment d) ℝ≥0∞ (rowSigma Kᶜ) _
      (fun ω => quenchedKernel d (ω,x) (E ∩ avoids K)) := by
  have hmeas := (Kernel.measurable_coe (quenchedKernel d) (hE.inter (measurableSet_avoids K))).comp
    ((measurable_maskEnvironment K r).prodMk measurable_const (g := fun _ => x))
  suffices heq : (fun ω => quenchedKernel d (ω,x) (E ∩ avoids K)) =
      (fun ω => quenchedKernel d (maskEnvironment K r ω,x) (E ∩ avoids K)) by
    rw [heq]
    exact hmeas
  funext ω
  have he := congrArg (fun ξ : Measure (Path d) => ξ E)
    (quenched_restrict_avoids_eq K (maskEnvironment K r ω) ω
      (fun y hy => by simp [maskEnvironment, hy]) x)
  simpa only [Measure.restrict_apply hE] using he.symm

lemma measurable_entryWeight_on_rows {d : ℕ} (K : Set (Site d)) (x y : Site d) (hx : x ∈ K) :
    @Measurable (Environment d) ℝ≥0∞ (rowSigma K) _ (fun ω => entryWeight ω x y) := by
  apply Finset.measurable_sum
  intro e he
  split_ifs
  · exact ((measurable_pi_apply e).comp
      (measurable_subtype_coe.comp (measurable_row hx))).ennreal_ofReal
  · exact measurable_const

lemma measurable_pathWeight_on_rows {d : ℕ} (K : Set (Site d)) (n : ℕ) (γ : Path d)
    (hK : ∀ i < n, γ i ∈ K) :
    @Measurable (Environment d) ℝ≥0∞ (rowSigma K) _ (pathWeight n γ) := by
  apply Finset.measurable_prod
  intro i hi
  exact measurable_entryWeight_on_rows K _ _ (hK i (Finset.mem_range.mp hi))

lemma path_departure_transfer {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (K : Set (Site d)) (n : ℕ) (γ : Path d) (hK : ∀ i < n, γ i ∈ K)
    (f : Environment d → ℝ≥0∞)
    (hf : @Measurable (Environment d) ℝ≥0∞ (rowSigma Kᶜ) _ f) :
    (∫⁻ ω, pathWeight n γ ω * f ω ∂environmentLaw μ) =
      (∫⁻ ω, pathWeight n γ ω ∂environmentLaw μ) * ∫⁻ ω, f ω ∂environmentLaw μ := by
  exact lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    (rowSigma_le _) (rowSigma_le _)
    (independent_rowSigma μ disjoint_compl_right)
    (measurable_pathWeight_on_rows K n γ hK) hf

lemma quenched_prefix_tail_apply {d : ℕ} (ω : Environment d) (x : Site d) (n : ℕ)
    (γ : Path d) {E : Set (Path d)} (hE : MeasurableSet E) :
    quenchedKernel d (ω,x) (pathCylinder n γ ∩ tailPath n ⁻¹' E) =
      (if x = γ 0 then pathWeight n γ ω else 0) * quenchedKernel d (ω,γ n) E := by
  have h := congrArg (fun ξ : Measure (Path d) => ξ E) (quenched_prefix_tail ω x n γ)
  rw [Measure.map_apply (measurable_tailPath n) hE,
    Measure.restrict_apply ((measurable_tailPath n) hE), Set.inter_comm,
    Measure.smul_apply, smul_eq_mul] at h
  exact h

lemma annealed_fresh_prefix_tail {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (K : Set (Site d)) (x : Site d) (n : ℕ) (γ : Path d) (hK : ∀ i < n, γ i ∈ K)
    {E : Set (Path d)} (hE : MeasurableSet E) :
    annealed μ x (pathCylinder n γ ∩ tailPath n ⁻¹' (E ∩ avoids K)) =
      annealed μ x (pathCylinder n γ) * annealed μ (γ n) (E ∩ avoids K) := by
  classical
  have hF : MeasurableSet (E ∩ avoids K) := hE.inter (measurableSet_avoids K)
  rw [annealed_apply μ x ((measurableSet_pathCylinder n γ).inter ((measurable_tailPath n) hF))]
  simp_rw [quenched_prefix_tail_apply _ _ _ _ hF]
  rw [annealed_cylinder]
  by_cases hx : x = γ 0
  · simp only [ite_eq_left hx]
    let r : Row d := Classical.choice (nonempty_of_isProbabilityMeasure μ)
    rw [path_departure_transfer μ K n γ hK _ (measurable_quenched_avoids_on_rows K r _ hE),
      ← annealed_apply μ (γ n) hF]
  · simp only [ite_eq_right hx, zero_mul, lintegral_zero]

lemma path_weights_disjoint {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (n m : ℕ) (γ δ : Path d) (h : ∀ i < n, ∀ j < m, γ i ≠ δ j) :
    (∫⁻ ω, pathWeight n γ ω * pathWeight m δ ω ∂environmentLaw μ) =
      (∫⁻ ω, pathWeight n γ ω ∂environmentLaw μ) *
        (∫⁻ ω, pathWeight m δ ω ∂environmentLaw μ) := by
  let K : Set (Site d) := {y | ∃ i < n, γ i = y}
  apply path_departure_transfer μ K n γ (fun i hi => ⟨i,hi,rfl⟩)
  apply measurable_pathWeight_on_rows
  intro j hj
  rintro ⟨i,hi,hij⟩
  exact h i hi j hj hij

end DirectionalZeroOne

end OAI
