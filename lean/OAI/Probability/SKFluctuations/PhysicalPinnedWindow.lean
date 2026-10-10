import Mathlib
import OAI.Probability.SKFluctuations.RawLossLogarithms

namespace OAI

/-! Physical Pinned Window. -/

noncomputable section


namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal ENNReal BigOperators

 theorem terminalScore_spin_zero (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {P : Type} (x : P → FeatureIndex n → ℝ)
    (p : P × ForwardPath (FeatureIndex n → ℝ) (Spin n) steps.length) :
    terminalScore (actualSpinPath n steps x) (steps.length+1) 0 p =
      physicalSpinL n steps (x p.1) (ForwardPath.spin steps.length p.2) := by
  rw [terminalScore, actualSpinPath_terminal, actualSpinPath_zero]
  simp only [physicalSpinL, PiLp.inner_apply, EuclideanSpace.real_norm_sq_eq,
    RCLike.inner_apply, conj_trivial]

 theorem terminalScore_spin_succ (n : ℕ) (st : GaussianStep (FeatureIndex n))
    (tail : List (GaussianStep (FeatureIndex n))) {P : Type}
    (x : P → FeatureIndex n → ℝ) (j : ℕ)
    (p : P × ForwardPath (FeatureIndex n → ℝ) (Spin n) (st::tail).length) :
    terminalScore (actualSpinPath n (st::tail) x) ((st::tail).length+1) (j+1) p =
      terminalScore (actualSpinPath n tail (fun q : P × (FeatureIndex n → ℝ) => x q.1+q.2))
        (tail.length+1) j ((p.1,p.2.1),p.2.2) := rfl

 theorem physicalPinnedPair_fst_eq_window (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps)
    (k : Fin (steps.length+1) → ℝ) {P : Type} (x : P → FeatureIndex n → ℝ)
    (p : P × ForwardPath (FeatureIndex n → ℝ) (Spin n) steps.length) :
    (physicalPinnedPair (uniformWeight n) (finiteFeature n) (spinSource n)
      steps a k (x p.1) p.2).1 =
    terminalWindow (actualSpinPath n steps x) (steps.length+1) Finset.univ Fin.val
      (fun j => pathMassDifferences steps a j * k j) p := by
  induction steps generalizing a P with
  | nil =>
    change (1-a)*(k 0 * driverObservable (uniformWeight n) (finiteFeature n) []
      (.id ℝ _) (spinSource n) p.2 (x p.1)) = _
    simp only [terminalWindow, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    change _ = ∑ j : Fin 1, ((1-a)*k j) *
      terminalScore (actualSpinPath n [] x) 1 j.val p
    rw [Fin.sum_univ_one]
    erw [driverObservable_spin,terminalScore_spin_zero]
    change (1-a)*(k 0 * physicalSpinL n [] (x p.1) p.2) =
      ((1-a)*k 0)*physicalSpinL n [] (x p.1) p.2
    ring
  | cons st tail ih =>
    rcases st with ⟨m,q⟩
    have ht := ih ha.2.2.2 (Fin.tail k)
      (fun z : P × (FeatureIndex n → ℝ) => x z.1+z.2) ((p.1,p.2.1),p.2.2)
    change (m-a)*(physicalNodePair (uniformWeight n) (finiteFeature n) (spinSource n)
        ((m,q)::tail) (k 0) (x p.1) (ForwardPath.spin tail.length p.2.2)).1 +
      (physicalPinnedPair (uniformWeight n) (finiteFeature n) (spinSource n)
        tail m (Fin.tail k) (x p.1+p.2.1) p.2.2).1 = _
    rw [ht]
    simp only [terminalWindow, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    conv_rhs => erw [Fin.sum_univ_succ]
    simp only [physicalNodePair,driverObservable_spin,pathMassDifferences,
      Fin.cons_zero,Fin.cons_succ,Fin.val_zero,Fin.val_succ,terminalScore_spin_zero,
      terminalScore_spin_succ,Fin.tail]
    congr 1
    change (m-a)*(k 0 * physicalSpinL n ((m,q)::tail) (x p.1)
      (ForwardPath.spin tail.length p.2.2)) =
      ((m-a)*k 0)*physicalSpinL n ((m,q)::tail) (x p.1)
        (ForwardPath.spin tail.length p.2.2)
    ring

 theorem actualSpinPath_rooted_martingale (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps)
    (q₀ : FeatureIndex n → ℝ≥0) :
    Martingale (actualSpinPath n steps id)
      (forwardFiltration (FeatureIndex n → ℝ) (FeatureIndex n → ℝ) (Spin n) steps.length)
      (rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps) := by
  simpa only [Kernel.comap_id, rootedHierarchyPathLaw] using
    actualSpinPath_martingale n steps ha (Measure.pi (fun i => gaussianReal 0 (q₀ i)))
      id measurable_id

 

 theorem physicalPinnedPair_sqnorm_le (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q₀ : FeatureIndex n → ℝ≥0) (k : Fin (steps.length+1) → ℝ)
    (hk : ∀ j, 0 ≤ k j) (hnorm : ∑ j, pathMassDifferences steps 0 j*k j = 1)
    {i : ℕ} (hi : ∀ j, pathMassDifferences steps 0 j*k j ≠ 0 → i ≤ j.val) :
    let μ := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps
    let 𝒢 := forwardFiltration (FeatureIndex n → ℝ) (FeatureIndex n → ℝ) (Spin n) steps.length
    (fun p => ‖actualSpinPath n steps id i p‖^2) ≤ᵐ[μ]
      fun p => 2*μ[(fun z => (physicalPinnedPair (uniformWeight n) (finiteFeature n)
        (spinSource n) steps 0 k z.1 z.2).1) | 𝒢 i] p := by
  dsimp only
  let := rootedHierarchyPathLaw_probability (uniformWeight_pos n) (finiteFeature n) q₀ steps ha
  let J : Finset (Fin (steps.length+1)) := Finset.univ.filter (fun j =>
    pathMassDifferences steps 0 j*k j ≠ 0)
  have hsum : ∑ j ∈ J, pathMassDifferences steps 0 j*k j = 1 := by
    rw [Finset.sum_filter_ne_zero]
    exact hnorm
  have hw : (fun z => (physicalPinnedPair (uniformWeight n) (finiteFeature n)
      (spinSource n) steps 0 k z.1 z.2).1) =
      terminalWindow (actualSpinPath n steps id) (steps.length+1) J Fin.val
        (fun j => pathMassDifferences steps 0 j*k j) := by
    funext z
    change (physicalPinnedPair (uniformWeight n) (finiteFeature n) (spinSource n)
      steps 0 k (id z.1) z.2).1 = _
    rw [physicalPinnedPair_fst_eq_window n steps ha k id z]
    simp only [terminalWindow,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    apply (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro j hj hj'
    have hz : pathMassDifferences steps 0 j*k j = 0 := by
      by_contra hz
      exact hj' (Finset.mem_filter.mpr ⟨hj,hz⟩)
    rw [hz,zero_mul]
  rw [hw]
  apply sqnorm_le_condExp_window (actualSpinPath_rooted_martingale n steps ha q₀)
    (R := 1) (fun j => Eventually.of_forall fun z => actualSpinPath_norm_le n steps ha id j z)
  · intro j _
    exact mul_nonneg (pathMassDifferences_nonneg steps ha j) (hk j)
  · exact hsum
  · intro j hj
    exact ⟨hi j (Finset.mem_filter.mp hj).2, j.isLt.le⟩

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal ENNReal BigOperators

 theorem physicalPinnedPair_fst_memLp (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q₀ : FeatureIndex n → ℝ≥0) (k : Fin (steps.length+1) → ℝ) (p : ℝ≥0∞) :
    MemLp (fun z => (physicalPinnedPair (uniformWeight n) (finiteFeature n)
      (spinSource n) steps 0 k z.1 z.2).1) p
      (rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps) := by
  let := rootedHierarchyPathLaw_probability (uniformWeight_pos n) (finiteFeature n) q₀ steps ha
  have he : (fun z => (physicalPinnedPair (uniformWeight n) (finiteFeature n)
      (spinSource n) steps 0 k z.1 z.2).1) =
      terminalWindow (actualSpinPath n steps id) (steps.length+1) Finset.univ Fin.val
      (fun j => pathMassDifferences steps 0 j*k j) := by
    funext z
    exact physicalPinnedPair_fst_eq_window n steps ha k id z
  rw [he]
  exact terminalWindow_memLp (actualSpinPath_rooted_martingale n steps ha q₀)
    (R := 1) (fun j => Eventually.of_forall fun z => actualSpinPath_norm_le n steps ha id j z)
    _ _ _ _ p

 theorem integral_physicalPinnedPair_fst (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q₀ : FeatureIndex n → ℝ≥0) (k : Fin (steps.length+1) → ℝ) :
    let μ := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps
    (∫ z, (physicalPinnedPair (uniformWeight n) (finiteFeature n)
      (spinSource n) steps 0 k z.1 z.2).1 ∂μ) =
      (1/2:ℝ)*∑ j : Fin (steps.length+1),
        (pathMassDifferences steps 0 j*k j)*∫ z, ‖actualSpinPath n steps id j.val z‖^2 ∂μ := by
  dsimp only
  let := rootedHierarchyPathLaw_probability (uniformWeight_pos n) (finiteFeature n) q₀ steps ha
  have hX := actualSpinPath_rooted_martingale n steps ha q₀
  have hR : ∀ j, ∀ᵐ z ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps,
      ‖actualSpinPath n steps id j z‖ ≤ 1 :=
    fun j => Eventually.of_forall fun z => actualSpinPath_norm_le n steps ha id j z
  have he : (fun z => (physicalPinnedPair (uniformWeight n) (finiteFeature n)
      (spinSource n) steps 0 k z.1 z.2).1) =
      terminalWindow (actualSpinPath n steps id) (steps.length+1) Finset.univ Fin.val
      (fun j => pathMassDifferences steps 0 j*k j) := by
    funext z
    exact physicalPinnedPair_fst_eq_window n steps ha k id z
  rw [he]
  unfold terminalWindow
  change (∫ z, (∑ j : Fin (steps.length+1),
    (pathMassDifferences steps 0 j*k j) •
      terminalScore (actualSpinPath n steps id) (steps.length+1) j.val) z
    ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps) = _
  simp only [Finset.sum_apply]
  rw [integral_finsetSum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Pi.smul_apply]
    rw [integral_smul,integral_terminalScore hX hR j.isLt.le]
    simp only [smul_eq_mul]
    ring
  · intro j _
    exact (terminalScore_integrable hX hR _ _).smul _

 theorem physical_window_square_moment_le (n d : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q₀ : FeatureIndex n → ℝ≥0) (e : Fin d ≃ Fin (steps.length+1) × FeatureIndex n)
    (k : Fin (steps.length+1) → ℝ) (hk : ∀ j, 0 ≤ k j)
    (hnorm : ∑ j, pathMassDifferences steps 0 j*k j = 1)
    {i : ℕ} (hi : ∀ j, pathMassDifferences steps 0 j*k j ≠ 0 → i ≤ j.val)
    {p : ℝ} (hp : 2 ≤ p) :
    let μ := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps
    let LW := Function.uncurry (physicalPinnedPair (uniformWeight n) (finiteFeature n)
      (spinSource n) steps 0 k)
    momentNorm μ (fun z => ‖actualSpinPath n steps id i z‖^2) p ≤
      2*(|∫ z, (LW z).1 ∂μ| +
        Real.sqrt ((1+p^2/3)*momentNorm μ (fun z => (LW z).2) (p/2))) := by
  dsimp only
  let μ := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps
  let L := fun z : (FeatureIndex n → ℝ) × ForwardPath (FeatureIndex n → ℝ) (Spin n) steps.length => (physicalPinnedPair (uniformWeight n) (finiteFeature n)
      (spinSource n) steps 0 k z.1 z.2).1
  let 𝒢 := forwardFiltration (FeatureIndex n → ℝ) (FeatureIndex n → ℝ) (Spin n) steps.length
  let := rootedHierarchyPathLaw_probability (uniformWeight_pos n) (finiteFeature n) q₀ steps ha
  have hL : MemLp L (ENNReal.ofReal p) μ := physicalPinnedPair_fst_memLp n steps ha q₀ k _
  have hp1 : 1 ≤ p := by linarith
  have hpe : 1 ≤ ENNReal.ofReal p := by exact_mod_cast ENNReal.ofReal_le_ofReal hp1
  have hh : momentNorm μ (fun z => ‖actualSpinPath n steps id i z‖^2) p ≤
      momentNorm μ ((2:ℝ) • μ[L | 𝒢 i]) p := by
    apply momentNorm_le_of_norm_le ((hL.condExp hpe).const_smul (2:ℝ))
    filter_upwards [physicalPinnedPair_sqnorm_le n steps ha q₀ k hk hnorm hi] with z hz
    change ‖‖actualSpinPath n steps id i z‖^2‖ ≤ ‖2*μ[L | 𝒢 i] z‖
    rw [Real.norm_of_nonneg (sq_nonneg _),Real.norm_of_nonneg ((sq_nonneg _).trans hz)]
    exact hz
  rw [momentNorm_smul,abs_of_pos (by norm_num : (0:ℝ)<2)] at hh
  have hc := physical_planted_centered_moment_le q₀ steps ha e k hp
  dsimp only at hc
  have hc' : momentNorm μ (fun z => L z-∫ z, L z ∂μ) p ≤
      Real.sqrt ((1+p^2/3)*momentNorm μ (fun z =>
      (physicalPinnedPair (uniformWeight n) (finiteFeature n) (spinSource n)
        steps 0 k z.1 z.2).2) (p/2)) := (le_abs_self _).trans (Real.abs_le_sqrt hc)
  calc
    _ ≤ 2*momentNorm μ μ[L | 𝒢 i] p := hh
    _ ≤ 2*momentNorm μ L p := mul_le_mul_of_nonneg_left
      (momentNorm_condExp_le L hp1 hL (𝒢 i)) (by norm_num)
    _ ≤ 2*(momentNorm μ (fun z => L z-∫ z, L z ∂μ) p + |∫ z, L z ∂μ|) :=
      mul_le_mul_of_nonneg_left (momentNorm_centering_le L hp1 hL _) (by norm_num)
    _ ≤ _ := by
      dsimp only [μ,L,Function.uncurry] at hc' ⊢
      linarith

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal ENNReal BigOperators

 theorem rootedHierarchyPathLaw_eq_physical (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (q₀ : FeatureIndex n → ℝ≥0) :
    rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps =
      physicalPathLaw (Measure.pi fun j => gaussianReal 0 (q₀ j)) n steps id measurable_id := by
  simp only [rootedHierarchyPathLaw,physicalPathLaw,ProbabilityTheory.Kernel.comap_id]

 theorem integral_physical_window_mean_le (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q₀ : FeatureIndex n → ℝ≥0) (J : Finset (Fin (steps.length+1)))
    (hv : 0 < physicalWindowMass steps 0 J) {M : ℝ}
    (hS : ∀ j ∈ J, (∫ z, ‖actualSpinPath n steps id j.val z‖^2
      ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps) ≤ M) :
    |∫ z, (physicalPinnedPair (uniformWeight n) (finiteFeature n) (spinSource n)
      steps 0 (physicalWindowWeight steps 0 J) z.1 z.2).1
      ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps| ≤ M/2 := by
  rw [integral_physicalPinnedPair_fst n steps ha q₀]
  have hpos j : 0 ≤ pathMassDifferences steps 0 j*physicalWindowWeight steps 0 J j :=
    mul_nonneg (pathMassDifferences_nonneg steps ha j) (physicalWindowWeight_nonneg steps ha J j)
  rw [abs_of_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg fun j _ =>
    mul_nonneg (hpos j) (integral_nonneg fun z => sq_nonneg _)))]
  have hsum : ∑ j, (pathMassDifferences steps 0 j*physicalWindowWeight steps 0 J j)*
      (∫ z, ‖actualSpinPath n steps id j.val z‖^2
        ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps) ≤ M := by
    calc
      _ ≤ ∑ j, (pathMassDifferences steps 0 j*physicalWindowWeight steps 0 J j)*M := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : j ∈ J
        · exact mul_le_mul_of_nonneg_left (hS j hj) (hpos j)
        · simp [physicalWindowWeight,hj]
      _ = M := by rw [← Finset.sum_mul,physicalWindowWeight_normalized steps 0 J hv,one_mul]
  linarith

 theorem physical_raw_window_bound (n l : ℕ) (hl : 0 < l)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q₀ : FeatureIndex n → ℝ≥0) (J : Finset (Fin (steps.length+1)))
    (hv : 0 < physicalWindowMass steps 0 J)
    (r : Fin (steps.length+2) → ℝ) (hr : Monotone r)
    (hc : ∀ j, physicalWindowCellMass steps 0 J j ≠ 0 → r j.castSucc < r j.succ)
    {i : ℕ} (hi : ∀ j ∈ J, i ≤ j.val) {M : ℝ}
    (hS : ∀ j ∈ J, (∫ z, ‖actualSpinPath n steps id j.val z‖^2
      ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps) ≤ M) :
    let μ := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps
    let v := physicalWindowMass steps 0 J
    let ζ := radiusCellMeasure (fun j => r j.castSucc) (fun j => r j.succ)
      (physicalWindowCellMass steps 0 J)
    ((∫ z, ‖actualSpinPath n steps id i z‖^(4*l) ∂μ)^(((4*l:ℕ):ℝ)⁻¹))^2 ≤
      M+2*Real.sqrt ((1+(2*(l:ℝ))^2/3)*(v⁻¹)^2*
        (∫ z, (physicalSusceptibilityMassIntegral n steps id ζ (radiusGridCut r) z)^l ∂μ)^((l:ℝ)⁻¹)) := by
  dsimp only
  let μ := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps
  let := rootedHierarchyPathLaw_probability (uniformWeight_pos n) (finiteFeature n) q₀ steps ha
  let k := physicalWindowWeight steps 0 J
  let d := Fintype.card (Fin (steps.length+1) × FeatureIndex n)
  let e : Fin d ≃ Fin (steps.length+1) × FeatureIndex n := (Fintype.equivFin _).symm
  have hi' j (hj : pathMassDifferences steps 0 j*k j ≠ 0) : i ≤ j.val := by
    apply hi j
    by_contra h
    exact hj (by simp [k,physicalWindowWeight,h])
  have hh := physical_window_square_moment_le n d steps ha q₀ e k
    (physicalWindowWeight_nonneg steps ha J) (physicalWindowWeight_normalized steps 0 J hv)
    hi' (p := (2*l:ℕ)) (by exact_mod_cast (show 2 ≤ 2*l by omega))
  dsimp only at hh
  rw [momentNorm_sqnorm_nat hl (physical_sqnorm_memLp n steps ha id measurable_id μ i _)] at hh
  simp only [Function.uncurry] at hh
  rw [show ((2*l:ℕ):ℝ)/2=(l:ℝ) by push_cast; ring] at hh
  dsimp only [k] at hh
  have henergy := physical_radius_window_energy_moment n l hl steps ha J r hr hc id measurable_id μ
  simp only [id_eq] at henergy
  rw [henergy] at hh
  have hmean := integral_physical_window_mean_le n steps ha q₀ J hv hS
  push_cast at hh ⊢
  calc
    _ ≤ 2*(|∫ z, (physicalPinnedPair (uniformWeight n) (finiteFeature n) (spinSource n)
      steps 0 (physicalWindowWeight steps 0 J) z.1 z.2).1 ∂μ|+
      Real.sqrt ((1+(2*(l:ℝ))^2/3)*((physicalWindowMass steps 0 J)⁻¹^2*
        (∫ z, (physicalSusceptibilityMassIntegral n steps id
          (radiusCellMeasure (fun j => r j.castSucc) (fun j => r j.succ)
            (physicalWindowCellMass steps 0 J)) (radiusGridCut r) z)^l ∂μ)^((l:ℝ)⁻¹)))) := hh
    _ ≤ _ := by rw [← mul_assoc]; linarith

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 theorem orderedOverlap_normalized (n : ℕ) (σ τ : Spin n) :
    orderedOverlap n σ τ=∑ i, normalizedSpin n σ i*normalizedSpin n τ i := by
  unfold orderedOverlap
  simp only [normalizedSpin,div_mul_div_comm,←pow_two,Real.sq_sqrt (Nat.cast_nonneg n)]
  rw [Finset.sum_div]

 theorem hierarchyPairMean_overlap_eq_norm (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps)
    (x : FeatureIndex n → ℝ) :
    hierarchyPairMean (uniformWeight n) (finiteFeature n) (orderedOverlap n) steps x=
      ‖WithLp.toLp 2 (fun i => gaussianHierarchyMean (uniformWeight n) (finiteFeature n)
        (fun σ => normalizedSpin n σ i) steps x)‖^2 := by
  change hierarchyPairMean _ _ (fun σ τ => orderedOverlap n σ τ) steps x = _
  simp_rw [orderedOverlap_normalized]
  rw [hierarchyPairMean_sum,EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs,sq_abs]
  simp_rw [hierarchyPairMean_product (uniformWeight_pos n) (finiteFeature n) _ _ steps ha]
  simp only [pow_two]

 theorem actualSpinPath_norm_sq_at_cut (n : ℕ) (pre tail : List (GaussianStep (FeatureIndex n)))
    {a : ℝ} (ha : OrderedSteps a (pre++tail))
    (p : (FeatureIndex n → ℝ) × ForwardPath (FeatureIndex n → ℝ) (Spin n) (pre++tail).length) :
    ‖actualSpinPath n (pre++tail) id pre.length p‖^2=
      hierarchyPairMean (uniformWeight n) (finiteFeature n) (orderedOverlap n) tail
        (actualCutField pre tail p.1 p.2) := by
  rw [hierarchyPairMean_overlap_eq_norm n tail (ha.suffix pre tail)]
  congr 2
  apply PiLp.ext
  intro i
  exact hierarchyMeanPath_at_cut _ _ _ pre tail id p

 theorem physicalSecondMoment_eq_stepPairDisorder (n : ℕ)
    (pre tail : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 (pre++tail))
    (q₀ : FeatureIndex n → ℝ≥0) :
    (∫ p, ‖actualSpinPath n (pre++tail) id pre.length p‖^2
      ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ (pre++tail))=
      stepPairDisorder (uniformWeight n) (finiteFeature n) q₀ pre tail (orderedOverlap n) 0 := by
  have htail := ha.suffix pre tail
  have hI := physicalCutNormPower_integrable n (pre++tail) ha
    (Measure.pi fun i => gaussianReal 0 (q₀ i)) id measurable_id pre.length 2
  rw [←rootedHierarchyPathLaw_eq_physical] at hI
  have := hierarchyPathKernel_markov (uniformWeight_pos n) (finiteFeature n) (pre++tail) ha
  rw [rootedHierarchyPathLaw,Measure.integral_compProd hI]
  simp_rw [actualSpinPath_norm_sq_at_cut n pre tail ha]
  simp_rw [integral_actualCutField_test (uniformWeight_pos n) (finiteFeature n) pre tail ha
    (hierarchyPairMean_smooth (uniformWeight_pos n) (finiteFeature n) (orderedOverlap n) tail htail 0)]
  unfold stepPairDisorder zeroContinuation stepPairMean
  simp only [zero_add]
  congr 1
  funext x
  congr 1
  funext y
  exact hierarchyPairMean_eq_nested (uniformWeight_pos n) (finiteFeature n) (orderedOverlap n) tail htail y

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 def physicalPathSecondMoment (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    (q₀ : FeatureIndex n → ℝ≥0) (j : ℕ) : ℝ :=
    ∫ p, ‖actualSpinPath n steps id j p‖^2
      ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps

 theorem physicalSecondMoment_eq_stepPairMoment (n : ℕ) (hn : 0<n)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q₀ : FeatureIndex n → ℝ≥0) (u : ℝ) :
    physicalPathSecondMoment n steps q₀ (splitClockSteps u steps).1.length=
      stepPairMoment (uniformWeight n) (finiteFeature n) q₀ steps ha.mem_pos (orderedOverlap n) u := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  rw [stepPairMoment_eq_split (uniformWeight_pos n) (finiteFeature n) q₀ steps ha]
  have ho : OrderedSteps 0 ((splitClockSteps u steps).1++(splitClockSteps u steps).2) := by
    simpa only [splitClockSteps_append] using ha
  have he := physicalSecondMoment_eq_stepPairDisorder n (splitClockSteps u steps).1
    (splitClockSteps u steps).2 ho q₀
  change physicalPathSecondMoment n ((splitClockSteps u steps).1++(splitClockSteps u steps).2)
    q₀ (splitClockSteps u steps).1.length = _ at he
  rw [splitClockSteps_append] at he
  exact he

 theorem physicalRetainedSecondMoment_tendsto (n : ℕ) (hn : 0<n)
    (b h : ℝ → ℝ≥0) (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (as : ℕ → List PositiveMass) (mesh : ℕ → ℝ)
    (ho : ∀ k, MassOrdered 0 (as k)) (hm : ∀ k, PartitionMesh (mesh k) 0 (as k))
    (he : ∀ k, partitionEnd 0 (as k)=1) (hmesh : Tendsto mesh atTop (𝓝 0))
    (u : PositiveMass) (hu : u.val≤1) (hnode : ∀ k, u ∈ as k) :
    let q := completedPathClock n b h
    Tendsto (fun k => let steps := sampleClockSteps q 0 (as k)
      physicalPathSecondMoment n steps (q 0) (splitClockSteps u.val steps).1.length)
      atTop (𝓝 (orderedPathS n b h u.val)) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  dsimp only
  simp_rw [physicalSecondMoment_eq_stepPairMoment n hn _ (sampleClockSteps_ordered _ _ (ho _))]
  change Tendsto _ _ (𝓝 (orderedPathPair n b h (orderedOverlap n) u.val))
  rw [orderedPathPair_eq_completed n hn b h hb hh _ ⟨u.property,hu⟩]
  exact retainedMoment_tendsto_all (uniformWeight_pos n) (finiteFeature n) (completedPathClock n b h)
    (completedPathClock_monotone n hb hh) as mesh ho hm he hmesh u hu hnode (orderedOverlap n)

end SKFluctuations

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

omit [Nonempty S] in
 theorem levelPairMean_prefix [Nonempty S] (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (P : S → S → ℝ) (pre tail : List (GaussianStep ι)) :
    levelPairMean w φ P (pre++tail) pre.length=
      prefixTest pre (gaussianHierarchy w φ tail) (hierarchyPairMean w φ P tail) := by
  induction pre with
  | nil => simp only [List.nil_append,List.length_nil,levelPairMean,prefixTest]
  | cons st pre ih =>
    rcases st with ⟨m,q⟩
    simp only [List.cons_append,List.length_cons,levelPairMean,prefixTest,
      prefixContinuation_hierarchy,ih]

 theorem stepPairMean_eq_levelPairMean {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (P : S → S → ℝ)
    (pre tail : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a tail) :
    stepPairMean w φ pre tail P=levelPairMean w φ P (pre++tail) pre.length := by
  rw [levelPairMean_prefix]
  unfold stepPairMean
  congr 1
  funext x
  exact (hierarchyPairMean_eq_nested hw φ P tail ha x).symm

end SKFluctuations.Hierarchy
namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 theorem physicalSecondMoment_eq_rootLevelPairMean (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q₀ : FeatureIndex n → ℝ≥0) (j : ℕ) (hj : j ≤ steps.length) :
    physicalPathSecondMoment n steps q₀ j=
      rootLevelPairMean (uniformWeight n) (finiteFeature n) q₀ (orderedOverlap n) steps j := by
  have hsplit : steps.take j++steps.drop j=steps := List.take_append_drop ..
  have ho : OrderedSteps 0 (steps.take j++steps.drop j) := by rwa [hsplit]
  have he := physicalSecondMoment_eq_stepPairDisorder n (steps.take j) (steps.drop j) ho q₀
  change physicalPathSecondMoment n (steps.take j++steps.drop j) q₀ (steps.take j).length = _ at he
  unfold stepPairDisorder at he
  rw [stepPairMean_eq_levelPairMean (uniformWeight_pos n) (finiteFeature n)
    (orderedOverlap n) _ _ (ho.suffix _ _)] at he
  simpa only [hsplit,List.length_take,min_eq_left hj,rootLevelPairMean] using he

 theorem physicalPathSecondMoment_mono (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q₀ : FeatureIndex n → ℝ≥0) {i j : ℕ} (hij : i≤j) (hj : j ≤ steps.length) :
    physicalPathSecondMoment n steps q₀ i≤physicalPathSecondMoment n steps q₀ j := by
  rw [physicalSecondMoment_eq_rootLevelPairMean n steps ha q₀ i (hij.trans hj),
    physicalSecondMoment_eq_rootLevelPairMean n steps ha q₀ j hj]
  exact rootLevelPairMean_overlap_monotone n (uniformWeight_pos n) (finiteFeature n) q₀ steps ha hij

 theorem physicalRetainedSecondMoment_eventually_uniform (n : ℕ) (hn : 0<n)
    (b h : ℝ → ℝ≥0) (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (as : ℕ → List PositiveMass) (mesh : ℕ → ℝ)
    (ho : ∀ k, MassOrdered 0 (as k)) (hm : ∀ k, PartitionMesh (mesh k) 0 (as k))
    (he : ∀ k, partitionEnd 0 (as k)=1) (hmesh : Tendsto mesh atTop (𝓝 0))
    (u : PositiveMass) (hu : u.val≤1) (hnode : ∀ k, u ∈ as k)
    {C : ℝ} (hC : orderedPathS n b h u.val<C) :
    ∀ᶠ k in atTop, let q := completedPathClock n b h
      let steps := sampleClockSteps q 0 (as k)
      ∀ j ≤ (splitClockSteps u.val steps).1.length,
        physicalPathSecondMoment n steps (q 0) j<C := by
  have ht := physicalRetainedSecondMoment_tendsto n hn b h hb hh as mesh ho hm he hmesh u hu hnode
  have hbnd := ht.eventually (gt_mem_nhds hC)
  filter_upwards [hbnd] with k hk
  dsimp only at hk ⊢
  intro j hj
  refine lt_of_le_of_lt (physicalPathSecondMoment_mono n _ (sampleClockSteps_ordered _ _ (ho k)) _ hj ?_) hk
  have hl := congrArg List.length (splitClockSteps_append u.val (sampleClockSteps (completedPathClock n b h) 0 (as k)))
  rw [List.length_append] at hl
  omega

end SKFluctuations

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

 def retainMasses (us : List PositiveMass) (as : List PositiveMass) : List PositiveMass :=
   us.foldr insertMass as

 theorem retainMasses_ordered (us as : List PositiveMass)
    (hu : ∀ u ∈ us, u.val ≤ 1) (ha : MassOrdered 0 as) :
    MassOrdered 0 (retainMasses us as) := by
  induction us with
  | nil => exact ha
  | cons u us ih =>
    exact insertMass_ordered u (hu u List.mem_cons_self) _
      (ih (fun v hv => hu v (List.mem_cons_of_mem u hv)))

 theorem retainMasses_mesh (us as : List PositiveMass) {δ : ℝ}
    (hu : ∀ u ∈ us, u.val ≤ 1) (ha : MassOrdered 0 as) (hm : PartitionMesh δ 0 as) :
    PartitionMesh δ 0 (retainMasses us as) := by
  induction us with
  | nil => exact hm
  | cons u us ih =>
    have hus : ∀ v ∈ us, v.val ≤ 1 := fun v hv => hu v (List.mem_cons_of_mem u hv)
    exact splitMassPartition_mesh u (hu u List.mem_cons_self) _
      (retainMasses_ordered us as hus ha) u.property.le (ih hus)

 theorem retainMasses_end (us as : List PositiveMass)
    (hu : ∀ u ∈ us, u.val ≤ 1) (he : partitionEnd 0 as=1) :
    partitionEnd 0 (retainMasses us as)=1 := by
  induction us with
  | nil => exact he
  | cons u us ih =>
    exact insertMass_end u _ (hu u List.mem_cons_self)
      (ih (fun v hv => hu v (List.mem_cons_of_mem u hv)))

 theorem mem_retainMasses (us as : List PositiveMass) {u : PositiveMass} (hu : u ∈ us) :
    u ∈ retainMasses us as := by
  induction us with
  | nil => simp at hu
  | cons v vs ih =>
    rcases List.mem_cons.mp hu with rfl|hu
    · exact mem_insertMass_self u _
    · exact mem_insertMass_of_mem v (ih hu)

 def finiteCutMasses (us : List PositiveMass) (k : ℕ) : List PositiveMass :=
   retainMasses us (uniformMasses k)

 theorem finiteCutMasses_ordered (us : List PositiveMass)
    (hu : ∀ u ∈ us, u.val ≤ 1) (k : ℕ) : MassOrdered 0 (finiteCutMasses us k) :=
   retainMasses_ordered us _ hu (uniformMasses_ordered k)

 theorem finiteCutMasses_mesh (us : List PositiveMass)
    (hu : ∀ u ∈ us, u.val ≤ 1) (k : ℕ) :
    PartitionMesh (((k+1:ℕ):ℝ)⁻¹) 0 (finiteCutMasses us k) :=
   retainMasses_mesh us _ hu (uniformMasses_ordered k) (uniformMasses_mesh k)

 theorem finiteCutMasses_end (us : List PositiveMass)
    (hu : ∀ u ∈ us, u.val ≤ 1) (k : ℕ) : partitionEnd 0 (finiteCutMasses us k)=1 :=
   retainMasses_end us _ hu (uniformMasses_end k)

 theorem finiteCutMasses_nodes (us : List PositiveMass) (k : ℕ) {u : PositiveMass}
    (hu : u ∈ us) : u ∈ finiteCutMasses us k := mem_retainMasses us _ hu

end SKFluctuations.Hierarchy
namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal

 theorem finiteRetainedMeans_eventually (n : ℕ) (hn : 0<n)
    (b h : ℝ → ℝ≥0) (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (us : List PositiveMass) (hu : ∀ u ∈ us, u.val ≤ 1)
    (C : PositiveMass → ℝ) (hC : ∀ u ∈ us, orderedPathS n b h u.val<C u) :
    ∀ᶠ k : ℕ in atTop, ∀ u ∈ us,
      let steps := sampleClockSteps (completedPathClock n b h) 0 (finiteCutMasses us k)
      ∀ j ≤ (splitClockSteps u.val steps).1.length,
        physicalPathSecondMoment n steps ((completedPathClock n b h) 0) j ≤ C u := by
  have hu' (u : PositiveMass) (hui : u ∈ us) :=
    physicalRetainedSecondMoment_eventually_uniform n hn b h hb hh (finiteCutMasses us)
      (fun k => (((k+1:ℕ):ℝ)⁻¹))
      (finiteCutMasses_ordered us hu) (finiteCutMasses_mesh us hu)
      (finiteCutMasses_end us hu) uniformMasses_mesh_tendsto
      u (hu u hui) (fun k => finiteCutMasses_nodes us k hui) (hC u hui)
  have ha : ∀ᶠ k : ℕ in atTop, ∀ u ∈ (us.toFinset : Set PositiveMass),
      let steps := sampleClockSteps (completedPathClock n b h) 0 (finiteCutMasses us k)
      ∀ j ≤ (splitClockSteps u.val steps).1.length,
        physicalPathSecondMoment n steps ((completedPathClock n b h) 0) j < C u :=
    (eventually_all_finite us.toFinset.finite_toSet).mpr (by
      intro u hui
      exact hu' u (List.mem_toFinset.mp hui))
  filter_upwards [ha] with k hk
  intro u hui
  dsimp only
  intro j hj
  exact (hk u (List.mem_toFinset.mpr hui) j hj).le

end SKFluctuations

end

end OAI
