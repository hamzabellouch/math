import OAI.Analysis.BackwardIntertwiners.GlobalOperators

namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

open Topology MeasureTheory Set
open scoped ENNReal



lemma ergodic_late_intersection {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsFiniteMeasure μ] {θ : X → X} (hθ : Ergodic θ μ)
    {A B : Set X} (_ : MeasurableSet A) (hB : MeasurableSet B)
    (hA0 : μ A ≠ 0) (hB0 : μ B ≠ 0) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ μ (A ∩ (θ^[n]) ⁻¹' B) ≠ 0 := by
  let U : Set X := ⋃ n : ℕ, (θ^[n+N]) ⁻¹' B
  have hUmeas : MeasurableSet U := MeasurableSet.iUnion fun n =>
    hB.preimage (hθ.measurable.iterate (n+N))
  have hsub : θ ⁻¹' U ⊆ U := by
    intro x hx
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hx
    apply Set.mem_iUnion.mpr
    refine ⟨n+1, ?_⟩
    change θ^[n+1+N] x ∈ B
    have hi : n+1+N = (n+N)+1 := by omega
    rw [hi,Function.iterate_succ_apply]
    exact hn
  have hU0 : μ U ≠ 0 := by
    intro h
    have hs : (θ^[N]) ⁻¹' B ⊆ U := by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨0, by simpa using hx⟩
    have he := (hθ.toMeasurePreserving.iterate N).measure_preimage hB.nullMeasurableSet
    exact hB0 (le_antisymm (by rw [← he]; exact (measure_mono hs).trans (by rw [h])) bot_le)
  have hUfull : U =ᵐ[μ] Set.univ := by
    obtain he | he := hθ.ae_empty_or_univ_of_preimage_ae_le hUmeas.nullMeasurableSet
      (Filter.Eventually.of_forall hsub)
    · exact False.elim (hU0 (by rw [measure_congr he,measure_empty]))
    · exact he
  by_contra! hn
  have hzero : μ (A ∩ U) = 0 := by
    rw [show A ∩ U = ⋃ n : ℕ, A ∩ (θ^[n+N]) ⁻¹' B from Set.inter_iUnion _ _]
    exact measure_iUnion_null fun n => hn (n+N) (by omega)
  have he : (A ∩ U : Set X) =ᵐ[μ] A := by
    filter_upwards [hUfull] with x hx
    apply propext
    change (x ∈ A ∧ x ∈ U) ↔ x ∈ A
    have hxU : x ∈ U := (eq_iff_iff.mp hx).mpr (Set.mem_univ x)
    simp [hxU]
  exact hA0 ((measure_congr he).symm.trans hzero)

section Localization
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [finiteMeasure : IsFiniteMeasure μ]

omit finiteMeasure in
lemma measurable_global_coordinate [IsFiniteMeasure μ] (f : Lp Fiber 2 μ) (j : ℤ) : Measurable (fun x => f x j) :=
  ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 j).continuous.comp_stronglyMeasurable (Lp.stronglyMeasurable f)).measurable

omit finiteMeasure in
lemma exists_coordinate_support_nonnull [IsFiniteMeasure μ] {f : Lp Fiber 2 μ} (hf : f ≠ 0) :
    ∃ j : ℤ, μ {x | f x j ≠ 0} ≠ 0 := by
  by_contra! h
  apply hf
  rw [Lp.eq_zero_iff_ae_eq_zero]
  have ha : ∀ j : ℤ, ∀ᵐ x ∂μ, f x j = 0 := fun j => by
    exact ae_iff.mpr (h j)
  filter_upwards [ae_all_iff.mpr ha] with x hx
  ext j
  exact hx j




lemma scalar_invariant_pointwise_orthogonal {L : Submodule ℂ (Lp Fiber 2 μ)}
    (hL : ∀ g : Lp ℂ ∞ μ, ∀ f ∈ L, scalarMultiplier g f ∈ L)
    {f z : Lp Fiber 2 μ} (hf : f ∈ L) (hz : z ∈ L.orthogonal) :
    ∀ᵐ x ∂μ, inner ℂ (z x) (f x) = 0 := by
  apply (L2.integrable_inner z f).ae_eq_zero_of_forall_setIntegral_eq_zero
  intro s hs _
  let g : Lp ℂ ∞ μ := indicatorConstLp ∞ hs (measure_ne_top μ s) (1:ℂ)
  have hg : g =ᵐ[μ] s.indicator (fun _ => (1:ℂ)) := indicatorConstLp_coeFn
  rw [← integral_indicator hs]
  calc
    _ = ∫ x, inner ℂ (z x) (scalarMultiplier g f x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [scalarMultiplier_ae g f, hg] with x hx hgx
      rw [hx,hgx]
      by_cases hxs : x ∈ s
      · simp [Set.indicator_of_mem hxs]
      · simp [Set.indicator_of_notMem hxs]
    _ = inner ℂ z (scalarMultiplier g f) := (L2.inner_def _ _).symm
    _ = 0 := Submodule.inner_left_of_mem_orthogonal (hL g f hf) hz
end Localization

lemma fiber_cyclic_orthogonal_order {w : ℤ → ℝ} (hw : QuadraticWeights w)
    {T : Fiber →L[ℂ] Fiber}
    (hT : ∀ v j, T v j = (w j / w (j-1) : ℂ) * v (j-1))
    {v z : Fiber} (horth : ∀ r : ℕ, inner ℂ z ((T^r) v) = 0)
    {i j : ℤ} (hzi : z i ≠ 0) (hvj : v j ≠ 0) : i < j := by
  let b := fun k : ℤ => star (z k) * (w k:ℂ)
  let c := fun k : ℤ => v k / (w k:ℂ)
  have hwC (k : ℤ) : (w k:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hw.positive k))
  have hbi : b i ≠ 0 := mul_ne_zero (by simpa using hzi) (hwC i)
  have hcj : c j ≠ 0 := div_ne_zero hvj (hwC j)
  have hb (k : ℤ) : ‖b k‖ ≤ (‖z‖+1)*w k := by
    dsimp [b]
    rw [norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_of_nonneg (hw.positive k).le]
    apply mul_le_mul_of_nonneg_right _ (hw.positive k).le
    exact (lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) z k).trans (by linarith)
  have hc (k : ℤ) : ‖c k‖*w k ≤ ‖v‖+1 := by
    dsimp [c]
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (hw.positive k).le,
      div_mul_cancel₀ _ (ne_of_gt (hw.positive k))]
    exact (lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) v k).trans (by linarith)
  have hcor (r : ℕ) : (∑' k : ℤ, b k*c (k-r)) = 0 := by
    calc (∑' k : ℤ, b k*c (k-r)) = inner ℂ z ((T^r) v) := by
          rw [lp.inner_eq_tsum]
          apply tsum_congr
          intro k
          rw [RCLike.inner_apply, weighted_shift_pow hw.positive hT]
          dsimp [b, c]
          simp only [← Complex.star_def]
          ring
      _ = 0 := horth r
  exact (quadratic_support_separation w hw).strict_order ⟨i,hbi⟩ ⟨j,hcj⟩
    (by positivity : 0 < ‖z‖+1) (by positivity : 0 < ‖v‖+1) hb hc hcor hbi hcj


lemma explicitWeight_quadratic (x : Base) : QuadraticWeights (explicitWeight x) :=
  bilateralWeight_quadratic (plusResidue_bounds x) (minusResidue_bounds x)

lemma forwardFiber_weight_coordinates (x : Base) (v : Fiber) (j : ℤ) :
    forwardFiber x v j = (explicitWeight x j / explicitWeight x (j-1) : ℂ) * v (j-1) := by
  rw [forwardFiber_apply, ← explicitWeight_ratio x (j-1)]
  simp only [sub_add_cancel, Complex.ofReal_div]

lemma forwardFiber_lattice (x : Base) (L : Submodule ℂ Fiber) :
    (IsClosed (L : Set Fiber) ∧ OperatorInvariant L (forwardFiber x)) ↔
      L = ⊥ ∨ L = ⊤ ∨ ∃ h : ℤ, L = coordinateTail h := by
  constructor
  · rintro ⟨hcl, hinv⟩
    exact quadratic_fiber_tails _ (explicitWeight_quadratic x) _ (forwardFiber_weight_coordinates x) L hcl hinv
  · rintro (rfl | rfl | ⟨h,rfl⟩)
    · refine ⟨?_, ?_⟩
      · simpa only [Submodule.bot_coe] using (isClosed_singleton : IsClosed ({0} : Set Fiber))
      · intro v hv
        simpa only [Submodule.mem_bot, map_zero] using congrArg (forwardFiber x) (show v = 0 from hv)
    · exact ⟨isClosed_univ, fun _ _ => trivial⟩
    · exact ⟨coordinateTail_isClosed h, fun _ hv => forwardFiber_tail x h hv⟩

lemma inverseOdometer_ergodic : Ergodic inverseOdometer baseMeasure :=
  Ergodic.symm (e := odometerMeasurableEquiv) odometer_ergodic

lemma backwardOperator_power_nonzero (n : ℕ) (f : GlobalHilbert) (j : ℤ) :
    ∀ᵐ x ∂baseMeasure, f (inverseOdometer^[n] x) j ≠ 0 →
      ((backwardOperator^n) f) x (j-n) ≠ 0 := by
  induction n with
  | zero => filter_upwards [] with x; simp
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp]
    filter_upwards [backwardOperator_ae_inverse ((backwardOperator^n) f),
      inverseOdometer_preserving.quasiMeasurePreserving.tendsto_ae.eventually ih,
      inverseOdometer_preserving.quasiMeasurePreserving.tendsto_ae.eventually backwardCoeff_ae_pos]
      with x hx hi hp
    intro hn
    rw [hx, backwardFiber_apply]
    have he : j - (n+1:ℕ) + 1 = j - n := by omega
    rw [he]
    apply mul_ne_zero
    · exact_mod_cast (ne_of_gt (hp (j-n)))
    · apply hi
      simpa only [Function.iterate_succ_apply] using hn

lemma global_invariant_pow {T : GlobalHilbert →L[ℂ] GlobalHilbert}
    {L : Submodule ℂ GlobalHilbert} (hi : OperatorInvariant L T)
    {v : GlobalHilbert} (hv : v ∈ L) (n : ℕ) : (T^n) v ∈ L := by
  induction n with
  | zero => simpa using hv
  | succ n ih => simpa only [pow_succ', mul_apply_eq_comp] using hi _ ih

lemma invariant_pointwise_order {L : Submodule ℂ GlobalHilbert}
    (hS : OperatorInvariant L forwardOperator)
    (hM : ∀ g : Lp ℂ ∞ baseMeasure, OperatorInvariant L (scalarMultiplier g))
    {f z : GlobalHilbert} (hf : f ∈ L) (hz : z ∈ L.orthogonal) :
    ∀ᵐ x ∂baseMeasure, ∀ i j : ℤ, z x i ≠ 0 → f x j ≠ 0 → i < j := by
  have horth (r : ℕ) : ∀ᵐ x ∂baseMeasure, inner ℂ (z x) (((forwardOperator^r) f) x) = 0 :=
    scalar_invariant_pointwise_orthogonal hM (global_invariant_pow hS hf r) hz
  filter_upwards [ae_all_iff.mpr horth,
    ae_all_iff.mpr (fun r => forwardOperator_power_ae r f)] with x hx hxpow
  intro i j hzi hfj
  apply fiber_cyclic_orthogonal_order (explicitWeight_quadratic x) (forwardFiber_weight_coordinates x) ?_ hzi hfj
  intro r
  rw [← hxpow r]
  exact hx r




lemma forward_backward_scalar_transitive (L : Submodule ℂ GlobalHilbert)
    (hclosed : IsClosed (L : Set GlobalHilbert))
    (hS : OperatorInvariant L forwardOperator)
    (hV : OperatorInvariant L backwardOperator)
    (hM : ∀ g : Lp ℂ ∞ baseMeasure, OperatorInvariant L (scalarMultiplier g)) :
    L = ⊥ ∨ L = ⊤ := by
  by_contra! hproper
  have hOO : L.orthogonal.orthogonal = L := by
    rw [Submodule.orthogonal_orthogonal_eq_closure, hclosed.submodule_topologicalClosure_eq]
  have hnotOrth : L.orthogonal ≠ ⊥ := by
    intro hh
    rw [hh, Submodule.bot_orthogonal_eq_top] at hOO
    exact hproper.2 hOO.symm
  obtain ⟨f,hf,hf0⟩ := (Submodule.ne_bot_iff L).mp hproper.1
  obtain ⟨z,hz,hz0⟩ := (Submodule.ne_bot_iff L.orthogonal).mp hnotOrth
  obtain ⟨j,hA0⟩ := exists_coordinate_support_nonnull hf0
  obtain ⟨i,hB0⟩ := exists_coordinate_support_nonnull hz0
  let A : Set Base := {x | f x j ≠ 0}
  let B : Set Base := {x | z x i ≠ 0}
  have hA : MeasurableSet A := (measurableSet_eq_fun (measurable_global_coordinate f j) measurable_const).compl
  have hB : MeasurableSet B := (measurableSet_eq_fun (measurable_global_coordinate z i) measurable_const).compl
  obtain ⟨n,hn,hinter⟩ := ergodic_late_intersection inverseOdometer_ergodic hB hA hB0 hA0 (j-i).toNat
  have horder := invariant_pointwise_order hS hM (global_invariant_pow hV hf n) hz
  have hnull : ∀ᵐ x ∂baseMeasure, x ∉ B ∩ (inverseOdometer^[n]) ⁻¹' A := by
    filter_upwards [horder, backwardOperator_power_nonzero n f j] with x hx hp
    intro hmem
    have hzi : z x i ≠ 0 := hmem.1
    have hfj : f (inverseOdometer^[n] x) j ≠ 0 := hmem.2
    have hh := hx i (j-n) hzi (hp hfj)
    have hnat : (j-i) ≤ ((j-i).toNat : ℤ) := by omega
    have hnn : ((j-i).toNat : ℤ) ≤ (n:ℤ) := by exact_mod_cast hn
    omega
  apply hinter
  convert ae_iff.mp hnull using 1
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, not_not]

lemma generated_transitive : AlgebraTransitive (generatedAlgebra forwardOperator backwardOperator) := by
  intro L hclosed hInv
  apply forward_backward_scalar_transitive L hclosed
  · exact hInv _ (Algebra.subset_adjoin (Or.inl (Set.mem_insert _ _)))
  · exact hInv _ (Algebra.subset_adjoin (Or.inl (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
  · intro g
    exact hInv _ (Algebra.subset_adjoin (Or.inr ⟨g,rfl⟩))


def explicitDirectModel : DirectModelData :=
  ⟨forwardFiber, forwardOperator, backwardCoeff, backwardFiber, backwardOperator⟩

lemma explicitDirectModel_properties : DirectModelProperties explicitDirectModel where
  beta_measurable := measurable_explicitBeta
  beta_positive := explicitBeta_pos
  forward_coordinates := forwardFiber_apply
  forward_field := forwardOperator_ae
  fiber_lattice := forwardFiber_lattice
  S_nonzero := forwardOperator_ne_zero
  S_norm := forwardOperator_norm
  power_bound := fun n _ => forwardOperator_power_norm n
  V_contraction := backwardOperator_norm
  commute := forward_backward_commute
  backward_measurable := measurable_backwardCoeff
  backward_bounds := backwardCoeff_bounds
  backward_coordinates := backwardFiber_apply
  backward_field := backwardOperator_ae
  common_conull := by
    refine ⟨goodBase, measurableSet_goodBase, ?_, ?_, ?_⟩
    · exact ae_iff.mp ae_goodBase
    · ext x
      exact goodBase_odometer x
    · intro x hx
      exact ⟨backwardCoeff_pos hx, backwardFiber_tail_closure hx, backwardFiber_denseRange hx⟩
  transitive := generated_transitive

theorem direct_model : ∃ D : DirectModelData, DirectModelProperties D :=
  ⟨explicitDirectModel, explicitDirectModel_properties⟩

def rankOneCoordinate (i j : ℤ) : Fiber →L[ℂ] Fiber :=
  (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 i).comp (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 j)
@[simp] lemma rankOneCoordinate_apply (i j : ℤ) (v : Fiber) :
    rankOneCoordinate i j v = lp.single 2 i (v j) := rfl
lemma rankOneCoordinate_compact (i j : ℤ) : IsCompactOperator (rankOneCoordinate i j) :=
  (isCompactOperator_of_locallyCompactSpace_dom (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 j)).clm_comp
    (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 i)

def finiteShift (x : Base) (n : ℕ) : Fiber →L[ℂ] Fiber :=
  ∑ j ∈ Finset.Icc (-(n:ℤ)) n, (explicitBeta x j:ℂ) • rankOneCoordinate (j+1) j
lemma finiteShift_compact (x : Base) (n : ℕ) : IsCompactOperator (finiteShift x n) := by
  change finiteShift x n ∈ compactOperator (RingHom.id ℂ) Fiber Fiber
  exact Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ (rankOneCoordinate_compact (j+1) j)
lemma finiteShift_apply (x : Base) (n : ℕ) (v : Fiber) (j : ℤ) :
    finiteShift x n v (j+1) = if j ∈ Finset.Icc (-(n:ℤ)) n then (explicitBeta x j:ℂ) * v j else 0 := by
  classical
  simp only [finiteShift, sum_apply, smul_apply,
    lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, rankOneCoordinate_apply]
  by_cases hj : j ∈ Finset.Icc (-(n:ℤ)) n
  · rw [ite_eq_left hj, Finset.sum_eq_single_of_mem j hj]
    · simp only [lp.single_apply_self, smul_eq_mul]
    · intro k hk hkj
      rw [lp.single_apply_ne _ _ _ (by omega), smul_zero]
  · rw [ite_eq_right hj]
    apply Finset.sum_eq_zero
    intro k hk
    have hkj : j+1 ≠ k+1 := by
      intro hh
      have he : j=k := by omega
      subst k
      exact hj hk
    rw [lp.single_apply_ne _ _ _ hkj, smul_zero]
lemma explicitBeta_outside_bound (x : Base) (n : ℕ) (j : ℤ)
    (hj : j ∉ Finset.Icc (-(n:ℤ)) n) : explicitBeta x j ≤ Real.exp (-10*(n:ℝ)) := by
  apply Real.exp_le_exp.mpr
  change -explicitExponent x j ≤ -10*(n:ℝ)
  have hd := explicitExponent_distance x j
  have hh : (n:ℤ) ≤ coordinateDistance j := by
    simp only [Finset.mem_Icc, not_and_or, not_le] at hj
    rcases hj with hj | hj
    · exact (by omega : (n:ℤ) ≤ -j).trans (le_max_right _ _)
    · exact (by omega : (n:ℤ) ≤ j+1).trans (le_max_left _ _)
  have hR : (n:ℝ) ≤ (coordinateDistance j : ℝ) := by exact_mod_cast hh
  linarith
lemma finiteShift_error (x : Base) (n : ℕ) :
    ‖forwardFiber x - finiteShift x n‖ ≤ Real.exp (-10*(n:ℝ)) := by
  let C := Real.exp (-10*(n:ℝ))
  have hC : 0 ≤ C := (Real.exp_pos _).le
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro v
  calc
    _ ≤ ‖(C:ℂ) • v‖ := by
      let vr := fiberReindex (Equiv.addRight (1:ℤ)) ((forwardFiber x - finiteShift x n) v)
      rw [← (fiberReindex (Equiv.addRight (1:ℤ))).norm_map ((forwardFiber x - finiteShift x n) v)]
      apply lp.norm_mono (by norm_num : (2:ENNReal) ≠ 0)
      intro j
      change ‖(forwardFiber x - finiteShift x n) v (j+1)‖ ≤ ‖(C:ℂ) * v j‖
      rw [sub_apply, lp.coeFn_sub, Pi.sub_apply, forwardFiber_apply, add_sub_cancel_right, finiteShift_apply]
      by_cases hj : j ∈ Finset.Icc (-(n:ℤ)) n
      · rw [ite_eq_left hj, sub_self, norm_zero]
        exact norm_nonneg _
      · rw [ite_eq_right hj, sub_zero, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_of_nonneg (explicitBeta_pos x j).le, Real.norm_of_nonneg hC]
        exact mul_le_mul_of_nonneg_right (explicitBeta_outside_bound x n j hj) (norm_nonneg _)
    _ = C*‖v‖ := by rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hC]
lemma forwardFiber_compact (x : Base) : IsCompactOperator (forwardFiber x) := by
  apply isCompactOperator_of_tendsto (l:=atTop) (F:=finiteShift x) ?_ (Filter.Eventually.of_forall (finiteShift_compact x))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have he : Tendsto (fun n : ℕ => Real.exp (-10*(n:ℝ))) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact tendsto_const_nhds.neg_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
  apply squeeze_zero (fun _ => norm_nonneg _) ?_ he
  intro n
  rw [norm_sub_rev]
  exact finiteShift_error x n

abbrev ScalarHilbert := Lp ℂ 2 baseMeasure

def coordinateL2 (j : ℤ) : GlobalHilbert →L[ℂ] ScalarHilbert :=
  (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 j).compLpL 2 baseMeasure

def singleL2 (j : ℤ) : ScalarHilbert →L[ℂ] GlobalHilbert :=
  (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 j).compLpL 2 baseMeasure

lemma coordinateL2_ae (j : ℤ) (f : GlobalHilbert) :
    coordinateL2 j f =ᵐ[baseMeasure] fun x => f x j :=
  ContinuousLinearMap.coeFn_compLpL _ _
lemma singleL2_ae (j : ℤ) (f : ScalarHilbert) :
    singleL2 j f =ᵐ[baseMeasure] fun x => lp.single 2 j (f x) :=
  ContinuousLinearMap.coeFn_compLpL _ _
lemma coordinateL2_singleL2 (j : ℤ) (f : ScalarHilbert) :
    coordinateL2 j (singleL2 j f) = f := by
  apply Lp.ext
  filter_upwards [coordinateL2_ae j (singleL2 j f), singleL2_ae j f] with x h₁ h₂
  simp only [h₁, h₂, lp.single_apply_self]


end
end BackwardIntertwiners

end OAI
