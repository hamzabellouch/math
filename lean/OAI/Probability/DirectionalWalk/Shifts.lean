import OAI.Probability.DirectionalWalk.CylinderLaw

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

def shiftEnvironment {d : ℕ} (z : Site d) (ω : Environment d) : Environment d :=
  fun x => ω (x+z)

def shiftPath {d : ℕ} (z : Site d) (X : Path d) : Path d := fun n => X n + z

lemma measurable_shiftEnvironment {d : ℕ} (z : Site d) :
    Measurable (shiftEnvironment z) := Measurable.of_eval (fun x => measurable_pi_apply (x+z))

lemma measurable_shiftPath {d : ℕ} (z : Site d) : Measurable (shiftPath z) := by
  apply Measurable.of_eval
  intro n
  exact (show Measurable (fun X : Path d => X n) from measurable_pi_apply n).add_const z

lemma environmentLaw_shift {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (z : Site d) : (environmentLaw μ).map (shiftEnvironment z) = environmentLaw μ := by
  let e := MeasurableEquiv.piCongrLeft (fun _ : Site d => Row d) (Equiv.addRight z)
  have h : (environmentLaw μ).map e = environmentLaw μ :=
    Measure.infinitePi_map_piCongrLeft (fun _ : Site d => μ) (Equiv.addRight z)
  have hh := congrArg (fun ξ : Measure (Environment d) => ξ.map e.symm) h
  have heq : (e.symm : Environment d → Environment d) = shiftEnvironment z := by
    funext ω x
    rfl
  rw [e.map_symm_map, heq] at hh
  exact hh.symm

lemma entryWeight_shift {d : ℕ} (z : Site d) (ω : Environment d) (x y : Site d) :
    entryWeight (shiftEnvironment z ω) x y = entryWeight ω (x+z) (y+z) := by
  simp only [entryWeight, shiftEnvironment]
  apply Finset.sum_congr rfl
  intro e he
  have h : x + z + stepVector e = y + z ↔ x + stepVector e = y := by
    rw [add_right_comm, add_left_inj]
  simp only [h]

lemma pathWeight_shift {d : ℕ} (z : Site d) (ω : Environment d) (n : ℕ) (γ : Path d) :
    pathWeight n γ (shiftEnvironment z ω) = pathWeight n (shiftPath z γ) ω := by
  simp only [pathWeight, shiftPath, entryWeight_shift]

lemma pathWeight_integral_shift {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (z : Site d) (n : ℕ) (γ : Path d) :
    (∫⁻ ω, pathWeight n (shiftPath z γ) ω ∂environmentLaw μ) =
      ∫⁻ ω, pathWeight n γ ω ∂environmentLaw μ := by
  calc
    _ = ∫⁻ ω, pathWeight n γ (shiftEnvironment z ω) ∂environmentLaw μ :=
      lintegral_congr (fun ω => (pathWeight_shift z ω n γ).symm)
    _ = ∫⁻ ω, pathWeight n γ ω ∂(environmentLaw μ).map (shiftEnvironment z) :=
      (lintegral_map (measurable_pathWeight n γ) (measurable_shiftEnvironment z)).symm
    _ = _ := by rw [environmentLaw_shift]

lemma shiftPath_preimage_cylinder {d : ℕ} (z : Site d) (n : ℕ) (γ : Path d) :
    shiftPath z ⁻¹' pathCylinder n γ = pathCylinder n (shiftPath (-z) γ) := by
  ext X
  simp only [Set.mem_preimage, pathCylinder, shiftPath, Set.mem_ofPred_eq]
  simp only [eq_add_neg_iff_add_eq]

lemma annealed_shift {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x z : Site d) : (annealed μ x).map (shiftPath z) = annealed μ (x+z) := by
  apply pathMeasure_ext
  intro n γ
  rw [Measure.map_apply (measurable_shiftPath z) (measurableSet_pathCylinder n γ),
    shiftPath_preimage_cylinder, annealed_cylinder, annealed_cylinder,
    pathWeight_integral_shift]
  simp only [shiftPath, eq_add_neg_iff_add_eq]

def tailPath {d : ℕ} (n : ℕ) (X : Path d) : Path d := fun k => X (n+k)

lemma measurable_tailPath {d : ℕ} (n : ℕ) : Measurable (@tailPath d n) :=
  Measurable.of_eval (fun k => measurable_pi_apply (n+k))

def concatPath {d : ℕ} (n : ℕ) (γ δ : Path d) : Path d :=
  fun k => if k < n then γ k else δ (k-n)

lemma concatPath_before {d : ℕ} (n : ℕ) (γ δ : Path d) (h : γ n = δ 0)
    {i : ℕ} (hi : i ≤ n) : concatPath n γ δ i = γ i := by
  rcases hi.eq_or_lt with rfl | hi
  · simp [concatPath, h]
  · simp [concatPath, hi]

lemma concatPath_after {d : ℕ} (n : ℕ) (γ δ : Path d) (i : ℕ) :
    concatPath n γ δ (n+i) = δ i := by simp [concatPath]

lemma pathWeight_concat {d : ℕ} (n m : ℕ) (γ δ : Path d) (h : γ n = δ 0)
    (ω : Environment d) :
    pathWeight (n+m) (concatPath n γ δ) ω = pathWeight n γ ω * pathWeight m δ ω := by
  unfold pathWeight
  rw [Finset.prod_range_add]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    rw [concatPath_before n γ δ h (Nat.le_of_lt (Finset.mem_range.mp hi)),
      concatPath_before n γ δ h (Finset.mem_range.mp hi)]
  · apply Finset.prod_congr rfl
    intro i hi
    simp only [concatPath_after, Nat.add_assoc]

lemma prefix_tail_inter {d : ℕ} (n m : ℕ) (γ δ : Path d) :
    pathCylinder n γ ∩ tailPath n ⁻¹' pathCylinder m δ =
      if γ n = δ 0 then pathCylinder (n+m) (concatPath n γ δ) else ∅ := by
  classical
  by_cases h : γ n = δ 0
  · rw [ite_eq_left h]
    ext X
    constructor
    · rintro ⟨hγ,hδ⟩ i hi
      by_cases hin : i < n
      · simpa [concatPath, hin] using hγ i (le_of_lt hin)
      · have hh := hδ (i-n) (by omega)
        simpa [tailPath, concatPath, hin, Nat.add_sub_of_le (Nat.le_of_not_gt hin)] using hh
    · intro hh
      constructor
      · intro i hi
        rw [hh i (by omega), concatPath_before n γ δ h hi]
      · intro i hi
        change X (n+i) = δ i
        rw [hh (n+i) (by omega), concatPath_after]
  · rw [ite_eq_right h]
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro X ⟨hγ,hδ⟩
    have h1 := hγ n le_rfl
    have h2 := hδ 0 (Nat.zero_le m)
    exact h (h1.symm.trans (by simpa [tailPath] using h2))

lemma quenched_prefix_tail {d : ℕ} (ω : Environment d) (x : Site d) (n : ℕ) (γ : Path d) :
    ((quenchedKernel d (ω,x)).restrict (pathCylinder n γ)).map (tailPath n) =
      (if x = γ 0 then pathWeight n γ ω else 0) • quenchedKernel d (ω,γ n) := by
  classical
  apply pathMeasure_ext
  intro m δ
  rw [Measure.map_apply (measurable_tailPath n) (measurableSet_pathCylinder m δ),
    Measure.restrict_apply ((measurable_tailPath n) (measurableSet_pathCylinder m δ)),
    Set.inter_comm, prefix_tail_inter, Measure.smul_apply, smul_eq_mul]
  by_cases h : γ n = δ 0
  · rw [ite_eq_left h, quenchedKernel_cylinder, quenchedKernel_cylinder, ite_eq_left h,
      concatPath_before n γ δ h (Nat.zero_le n), pathWeight_concat n m γ δ h]
    split_ifs <;> simp
  · rw [ite_eq_right h, measure_empty, quenchedKernel_cylinder, ite_eq_right h, mul_zero]

lemma prefix_preimage_singleton {d : ℕ} (n : ℕ) (γ : Path d) :
    (frestrictLe n : Path d → (Finset.Iic n → Site d)) ⁻¹' {frestrictLe n γ} =
      pathCylinder n γ := by
  ext X
  simp only [Set.mem_preimage, Set.mem_singleton_iff, pathCylinder, Set.mem_ofPred_eq]
  constructor
  · intro h i hi
    exact congr_fun h ⟨i, Finset.mem_Iic.mpr hi⟩
  · intro h
    funext i
    exact h i (Finset.mem_Iic.mp i.property)

lemma cylinder_measure_eq_of_prefixMap {d : ℕ} {μ ν : Measure (Path d)} (n : ℕ)
    (h : μ.map (frestrictLe n) = ν.map (frestrictLe n)) (γ : Path d) :
    μ (pathCylinder n γ) = ν (pathCylinder n γ) := by
  have hh := congrArg (fun ξ : Measure (Finset.Iic n → Site d) => ξ {frestrictLe n γ}) h
  simpa only [Measure.map_apply (measurable_frestrictLe n) (measurableSet_singleton _),
    prefix_preimage_singleton] using hh

lemma prefixMap_mono {d : ℕ} {μ ν : Measure (Path d)} {n m : ℕ} (hnm : n ≤ m)
    (h : μ.map (frestrictLe m) = ν.map (frestrictLe m)) :
    μ.map (frestrictLe n) = ν.map (frestrictLe n) := by
  have hh := congrArg (fun ξ : Measure (Finset.Iic m → Site d) =>
    ξ.map (frestrictLe₂ (π := fun _ : ℕ => Site d) hnm)) h
  simpa only [Measure.map_map (measurable_frestrictLe₂ hnm) (measurable_frestrictLe m),
    frestrictLe₂_comp_frestrictLe] using hh

end DirectionalZeroOne

end OAI
