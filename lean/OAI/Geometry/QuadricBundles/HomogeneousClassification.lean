import OAI.Geometry.QuadricBundles.MatrixDynamics

namespace OAI

noncomputable section

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Metric

end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology Metric

lemma invariant_mul_zpow {u : ℂ → ℝ} {a : ℂ} (ha : a ≠ 0)
    (hu : ∀ z : ℂ, z ≠ 0 → u (a * z) = u z) (n : ℤ) (z : ℂ) (hz : z ≠ 0) :
    u (a ^ n * z) = u z := by
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
    rw [zpow_add₀ ha, zpow_one, mul_comm (a ^ (k : ℤ)) a, mul_assoc,
      hu _ (mul_ne_zero (zpow_ne_zero _ ha) hz), ih]
  | pred k ih =>
    have hh := hu (a ^ (-(k : ℤ) - 1) * z) (mul_ne_zero (zpow_ne_zero _ ha) hz)
    have he : a * (a ^ (-(k : ℤ) - 1) * z) = a ^ (-(k : ℤ)) * z := by
      calc
        a * (a ^ (-(k : ℤ) - 1) * z) =
            (a ^ (1 : ℤ) * a ^ (-(k : ℤ) - 1)) * z := by rw [zpow_one, mul_assoc]
        _ = a ^ (1 + (-(k : ℤ) - 1)) * z := by rw [zpow_add₀ ha]
        _ = a ^ (-(k : ℤ)) * z := by congr 2; omega
    rw [he, ih] at hh
    exact hh.symm

lemma exists_rescale_mem_annulus {a : ℝ} (ha : 1 < a) {z : ℂ} (hz : z ≠ 0) :
    ∃ n : ℤ, 1 ≤ ‖(a : ℂ) ^ n * z‖ ∧ ‖(a : ℂ) ^ n * z‖ ≤ a := by
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  obtain ⟨k, hk1, hk2⟩ := exists_mem_Ico_zpow (norm_pos_iff.mpr hz) ha
  refine ⟨-k, ?_, ?_⟩
  all_goals rw [norm_mul, norm_zpow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos ha0, zpow_neg, inv_mul_eq_div]
  · exact (le_div_iff₀ (zpow_pos ha0 k)).mpr (by simpa using hk1)
  · apply (div_le_iff₀ (zpow_pos ha0 k)).mpr
    exact hk2.le.trans_eq (by rw [zpow_add₀ ha0.ne', zpow_one, mul_comm])

lemma complex_punctured_preconnected : IsPreconnected ({0}ᶜ : Set ℂ) := by
  apply (isConnected_compl_singleton_of_one_lt_rank (E := ℂ) ?_ 0).isPreconnected
  rw [← Module.finrank_eq_rank ℝ ℂ, Complex.finrank_real_complex]
  norm_num

end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology Metric

open MeasureTheory

theorem LocalDiskSubmeanOn.eq_const_of_dilation {u : ℂ → ℝ} {a : ℝ}
    (ha : 1 < a) (hu : LocalDiskSubmeanOn ({0}ᶜ : Set ℂ) u)
    (hinv : ∀ z : ℂ, z ≠ 0 → u ((a : ℂ) * z) = u z) :
    ∃ c : ℝ, ∀ z : ℂ, z ≠ 0 → u z = c := by
  let K : Set ℂ := {z | 1 ≤ ‖z‖ ∧ ‖z‖ ≤ a}
  have hkclosed : IsClosed K :=
    (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  have hkcompact : IsCompact K := (isCompact_closedBall (0 : ℂ) a).of_isClosed_subset
    hkclosed (fun z hz ↦ by simpa [mem_closedBall, dist_zero_right] using hz.2)
  have hk0 : K ⊆ ({0}ᶜ : Set ℂ) := by
    intro z hz
    simp only [mem_compl_iff, mem_singleton_iff]
    intro he
    simp only [K, he, norm_zero, Set.mem_ofPred_eq] at hz
    linarith [hz.1]
  have hkne : K.Nonempty := ⟨1, by simpa [K] using ha.le⟩
  obtain ⟨x, hx, hmax⟩ := (hu.1.mono hk0).exists_isMaxOn hkne hkcompact
  have hnonzero : (a : ℂ) ≠ 0 := by exact_mod_cast (lt_trans zero_lt_one ha).ne'
  have hmaxall : ∀ z ∈ ({0}ᶜ : Set ℂ), u z ≤ u x := by
    intro z hz
    have hz0 : z ≠ 0 := hz
    obtain ⟨k, hk⟩ := exists_rescale_mem_annulus ha hz0
    have hk' : (a : ℂ)^k * z ∈ K := hk
    rw [← invariant_mul_zpow hnonzero hinv k z hz0]
    exact hmax hk'
  exact ⟨u x, fun z hz ↦ hu.eq_const_of_max complex_punctured_preconnected (hk0 hx) hmaxall z hz⟩

end QuadricCounterexample

namespace QuadricCounterexample
open Set Matrix

structure HomogeneousLocalPshMetric24 (ψ : (Fin 2 → ℂ) → ℝ) : Prop where
  nonneg : ∀ v, 0 ≤ ψ v
  homogeneity : ∀ (c : ℂ) v, ψ (c • v) = ‖c‖ ^ 48 * ψ v
  upperSemicontinuous : UpperSemicontinuousOn ψ ({0}ᶜ : Set (Fin 2 → ℂ))
  disk : ∀ (U : Set ℂ), IsOpen U → ∀ (f : ℂ → Fin 2 → ℂ) (t : ℂ → ℂ),
    AnalyticOnNhd ℂ f U → AnalyticOnNhd ℂ t U → (∀ z ∈ U, f z ≠ 0) →
    LocalDiskSubmeanOn U (fun z ↦ ‖t z‖ ^ 2 * ψ (f z))

lemma HomogeneousLocalPshMetric24.zero {ψ : (Fin 2 → ℂ) → ℝ}
    (hψ : HomogeneousLocalPshMetric24 ψ) : ψ 0 = 0 := by
  simpa using hψ.homogeneity 0 0

lemma HomogeneousLocalPshMetric24.normalized_subharmonic {ψ : (Fin 2 → ℂ) → ℝ}
    (hψ : HomogeneousLocalPshMetric24 ψ) :
    LocalDiskSubmeanOn ({0}ᶜ : Set ℂ) (fun z ↦ ψ ![z,1] / ‖z‖ ^ 24) := by
  have hf : AnalyticOnNhd ℂ (fun z : ℂ ↦ ![z,1]) ({0}ᶜ : Set ℂ) := by
    apply analyticOnNhd_pi_iff.mpr
    intro i
    fin_cases i
    · exact analyticOnNhd_id
    · exact analyticOnNhd_const
  have ht : AnalyticOnNhd ℂ (fun z : ℂ ↦ z ^ (-12 : ℤ)) ({0}ᶜ : Set ℂ) :=
    analyticOnNhd_id.zpow (fun z hz ↦ hz)
  have hn : ∀ z ∈ ({0}ᶜ : Set ℂ), (![z,1] : Fin 2 → ℂ) ≠ 0 := by
    intro z _ he
    have hh := congrFun he 1
    norm_num at hh
  have hh := hψ.disk _ isOpen_compl_singleton _ _ hf ht hn
  convert hh using 1
  funext z
  simp only [_root_.zpow_neg]
  norm_num
  ring

theorem HomogeneousLocalPshMetric24.hyperbolic_classification
    {ψ : (Fin 2 → ℂ) → ℝ} (hψ : HomogeneousLocalPshMetric24 ψ)
    {a : ℝ} (ha : 1 < a)
    (hinv : ∀ v, ψ ![(a : ℂ) * v 0, (a : ℂ)⁻¹ * v 1] = ψ v) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ v, ψ v = c * (‖v 0‖ * ‖v 1‖) ^ 24 := by
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
  have hanorm : ‖(a : ℂ)‖ = a := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha0]
  have hpa : 1 < a ^ 48 := one_lt_pow₀ ha (by norm_num)
  have he1 : ψ ![1,0] = 0 := by
    have hs : ψ ![(a : ℂ),0] = a ^ 48 * ψ ![1,0] := by
      have hv : (a : ℂ) • (![1,0] : Fin 2 → ℂ) = ![(a : ℂ),0] := by
        ext i
        fin_cases i <;> simp
      rw [← hv, hψ.homogeneity, hanorm]
    have hi := hinv ![1,0]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one,
      mul_zero] at hi
    rw [hs] at hi
    nlinarith
  have he2 : ψ ![0,1] = 0 := by
    have hs : ψ ![0,(a : ℂ)] = a ^ 48 * ψ ![0,1] := by
      have hv : (a : ℂ) • (![0,1] : Fin 2 → ℂ) = ![0,(a : ℂ)] := by
        ext i
        fin_cases i <;> simp
      rw [← hv, hψ.homogeneity, hanorm]
    have hi := hinv ![0,(a : ℂ)]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero,
      inv_mul_cancel₀ haC] at hi
    rw [hs] at hi
    nlinarith
  have hscale (z : ℂ) : ψ ![(a : ℂ)^2*z,1] = a^48 * ψ ![z,1] := by
    have hv : (a : ℂ) • ![(a : ℂ)*z,(a : ℂ)⁻¹*1] = ![(a : ℂ)^2*z,1] := by
      ext i
      fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul, pow_two, mul_assoc, haC]
    rw [← hv, hψ.homogeneity, hanorm]
    exact congrArg (fun r : ℝ ↦ a ^ 48 * r) (hinv ![z,1])
  have hu : ∀ z : ℂ, z ≠ 0 →
      ψ ![((a^2 : ℝ) : ℂ)*z,1] / ‖((a^2 : ℝ) : ℂ)*z‖^24 =
        ψ ![z,1] / ‖z‖^24 := by
    intro z hz
    rw [Complex.ofReal_pow, hscale, norm_mul, norm_pow, hanorm, mul_pow, ← pow_mul]
    norm_num
    field_simp
  obtain ⟨c, hc⟩ := hψ.normalized_subharmonic.eq_const_of_dilation
    (show 1 < a^2 by nlinarith) hu
  have hc0 : 0 ≤ c := by
    rw [← hc 1 one_ne_zero]
    exact div_nonneg (hψ.nonneg _) (pow_nonneg (norm_nonneg _) _)
  refine ⟨c, hc0, ?_⟩
  intro v
  by_cases hv1 : v 1 = 0
  · have he : v = v 0 • ![1,0] := by
      ext i
      fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul, hv1]
    rw [he, hψ.homogeneity, he1]
    simp
  by_cases hv0 : v 0 = 0
  · have he : v = v 1 • ![0,1] := by
      ext i
      fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul, hv0]
    rw [he, hψ.homogeneity, he2]
    simp
  have he : v = v 1 • ![v 0 / v 1,1] := by
    ext i
    fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul, hv1, mul_div_cancel₀]
  have hh := (div_eq_iff (pow_ne_zero 24 (norm_ne_zero_iff.mpr (div_ne_zero hv0 hv1)))).mp
    (hc (v 0 / v 1) (div_ne_zero hv0 hv1))
  calc
    ψ v = ‖v 1‖^48 * ψ ![v 0/v 1,1] := by calc
      ψ v = ψ (v 1 • ![v 0/v 1,1]) := congrArg ψ he
      _ = _ := hψ.homogeneity _ _
    _ = c * (‖v 0‖ * ‖v 1‖)^24 := by
      rw [hh, norm_div, div_pow, mul_pow]
      field_simp

lemma HomogeneousLocalPshMetric24.pullback {ψ : (Fin 2 → ℂ) → ℝ}
    (hψ : HomogeneousLocalPshMetric24 ψ) (g : GL (Fin 2) ℂ) :
    HomogeneousLocalPshMetric24 (fun v ↦ ψ (g • v)) := by
  let L : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ) :=
    (Matrix.mulVecLin (g : Matrix (Fin 2) (Fin 2) ℂ)).toContinuousLinearMap
  have hL (v : Fin 2 → ℂ) : L v = g • v := rfl
  have hn (v : Fin 2 → ℂ) (hv : v ≠ 0) : g • v ≠ 0 := by
    intro he
    have hh := congrArg (fun w : Fin 2 → ℂ ↦ g⁻¹ • w) he
    rw [inv_smul_smul, smul_zero] at hh
    exact hv hh
  refine ⟨fun v ↦ hψ.nonneg _, ?_, ?_, ?_⟩
  · intro c v
    rw [smul_comm g c v, hψ.homogeneity]
  · exact hψ.upperSemicontinuous.comp L.continuous.continuousOn (fun v hv ↦ hn v hv)
  · intro U hU f t hf ht hfn
    exact hψ.disk U hU (fun z ↦ g • f z) t
      (((L.analyticOnNhd univ).comp hf (mapsTo_univ _ _))) ht
      (fun z hz ↦ hn _ (hfn z hz))

end QuadricCounterexample

namespace QuadricCounterexample
open Matrix OnePoint

lemma metric_zero_pair_preserved {φ : (Fin 2 → ℂ) → ℝ}
    (hz : ∀ v, φ v = 0 ↔ v 0 = 0 ∨ v 1 = 0)
    (g : GL (Fin 2) ℂ) (hinv : ∀ v, φ (g • v) = φ v) :
    ∀ x : OnePoint ℂ, x = ∞ ∨ x = (0 : ℂ) →
      g • x = ∞ ∨ g • x = (0 : ℂ) := by
  intro x hx
  rcases hx with rfl | rfl
  · have hzero : φ (g • (![1,0] : Fin 2 → ℂ)) = 0 := by
      rw [hinv]
      exact (hz _).mpr (Or.inr rfl)
    have hh := (hz _).mp hzero
    simp only [Matrix.GeneralLinearGroup.fin_two_smul, Matrix.cons_val_zero,
      Matrix.cons_val_one, mul_one, mul_zero, add_zero] at hh
    by_cases h10 : g 1 0 = 0
    · exact Or.inl (by simp [OnePoint.smul_infty_eq_ite, h10])
    · have h00 := hh.resolve_right h10
      exact Or.inr (by simp [OnePoint.smul_infty_eq_ite, h10, h00])
  · have hzero : φ (g • (![0,1] : Fin 2 → ℂ)) = 0 := by
      rw [hinv]
      exact (hz _).mpr (Or.inl rfl)
    have hh := (hz _).mp hzero
    simp only [Matrix.GeneralLinearGroup.fin_two_smul, Matrix.cons_val_zero,
      Matrix.cons_val_one, mul_one, mul_zero, zero_add] at hh
    by_cases h11 : g 1 1 = 0
    · exact Or.inl (by simp [OnePoint.smul_some_eq_ite, h11])
    · have h01 := hh.resolve_right h11
      exact Or.inr (by simp [OnePoint.smul_some_eq_ite, h11, h01])

lemma conjugate_pair_contradiction {φ : (Fin 2 → ℂ) → ℝ}
    (hz : ∀ v, φ v = 0 ↔ v 0 = 0 ∨ v 1 = 0)
    (P g h : GL (Fin 2) ℂ)
    (hgi : ∀ v, φ ((P⁻¹ * g * P) • v) = φ v)
    (hhi : ∀ v, φ ((P⁻¹ * h * P) • v) = φ v)
    (hg3 : ∀ x : OnePoint ℂ, g • (g • (g • x)) = x)
    (hh3 : ∀ x : OnePoint ℂ, h • (h • (h • x)) = x)
    (hnofix : ∀ x : OnePoint ℂ, ¬ (g • x = x ∧ h • x = x)) : False := by
  let g' := P⁻¹ * g * P
  let h' := P⁻¹ * h * P
  have hgp := metric_zero_pair_preserved hz g' hgi
  have hhp := metric_zero_pair_preserved hz h' hhi
  have hgcube (x : OnePoint ℂ) : g' • (g' • (g' • x)) = x := by
    simp only [g', mul_smul, smul_inv_smul]
    rw [hg3, inv_smul_smul]
  have hhcube (x : OnePoint ℂ) : h' • (h' • (h' • x)) = x := by
    simp only [h', mul_smul, smul_inv_smul]
    rw [hh3, inv_smul_smul]
  have hgp0 := hgp ∞ (Or.inl rfl)
  have hhp0 := hhp ∞ (Or.inl rfl)
  have hgf : g' • (∞ : OnePoint ℂ) = ∞ :=
    fixed_of_period_three_in_pair (hgcube ∞) (Or.inl rfl) hgp0 (hgp _ hgp0)
  have hhf : h' • (∞ : OnePoint ℂ) = ∞ :=
    fixed_of_period_three_in_pair (hhcube ∞) (Or.inl rfl) hhp0 (hhp _ hhp0)
  apply hnofix (P • (∞ : OnePoint ℂ))
  constructor
  · have he := congrArg (fun x : OnePoint ℂ ↦ P • x) hgf
    simpa only [g', mul_smul, smul_inv_smul] using he
  · have he := congrArg (fun x : OnePoint ℂ ↦ P • x) hhf
    simpa only [h', mul_smul, smul_inv_smul] using he

lemma local_homogeneous_metric_zero_of_diagonal_product
    {ψ : (Fin 2 → ℂ) → ℝ} (hψ : HomogeneousLocalPshMetric24 ψ)
    (P g h : GL (Fin 2) ℂ) {a : ℝ} (ha : 1 < a)
    (hdiag : ∀ v, P • ![(a : ℂ)*v 0,(a : ℂ)⁻¹*v 1] = g • (h • (P • v)))
    (hgi : ∀ v, ψ (g • v) = ψ v) (hhi : ∀ v, ψ (h • v) = ψ v)
    (hg3 : ∀ x : OnePoint ℂ, g • (g • (g • x)) = x)
    (hh3 : ∀ x : OnePoint ℂ, h • (h • (h • x)) = x)
    (hnofix : ∀ x : OnePoint ℂ, ¬ (g • x = x ∧ h • x = x)) :
    ∀ v, ψ v = 0 := by
  let φ : (Fin 2 → ℂ) → ℝ := fun v ↦ ψ (P • v)
  have hφ := hψ.pullback P
  obtain ⟨c, _, hc⟩ := hφ.hyperbolic_classification ha (fun v ↦ by
    rw [hdiag, hgi, hhi])
  by_cases hcZ : c = 0
  · intro v
    have he := hc (P⁻¹ • v)
    simpa only [smul_inv_smul, hcZ, zero_mul] using he
  have hz : ∀ v, φ v = 0 ↔ v 0 = 0 ∨ v 1 = 0 := by
    intro v
    change ψ (P • v) = 0 ↔ _
    rw [hc]
    simp [hcZ, mul_eq_zero]
  apply (conjugate_pair_contradiction hz P g h ?_ ?_ hg3 hh3 hnofix).elim
  · intro v
    simp only [φ, mul_smul, smul_inv_smul, hgi]
  · intro v
    simp only [φ, mul_smul, smul_inv_smul, hhi]

lemma source_expanding_gt_one : 1 < expandingRoot (1 + Real.sqrt 2) := by
  apply (hyperbolic_roots ?_).1
  have hn := Real.sqrt_nonneg (2 : ℝ)
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith

lemma source_eigenbasis_diagonalizes_inv :
    (source_A * source_B) * (source_eigenbasis : Matrix (Fin 2) (Fin 2) ℂ) =
      (source_eigenbasis : Matrix (Fin 2) (Fin 2) ℂ) *
        diagonal ![(expandingRoot (1 + Real.sqrt 2) : ℂ),
          (expandingRoot (1 + Real.sqrt 2) : ℂ)⁻¹] := by
  have ht : 2 < 1 + Real.sqrt 2 := by
    have hn := Real.sqrt_nonneg (2 : ℝ)
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  have hcontract : (contractingRoot (1 + Real.sqrt 2) : ℂ) =
      (expandingRoot (1 + Real.sqrt 2) : ℂ)⁻¹ := by
    have hh : (expandingRoot (1 + Real.sqrt 2) : ℂ) *
        (contractingRoot (1 + Real.sqrt 2) : ℂ) = 1 := by
      exact_mod_cast (hyperbolic_roots ht).2.2.2.2
    exact eq_inv_of_mul_eq_one_left (by rwa [mul_comm])
  have hd := hyperbolicBasis_diagonalizes ht
    (show (source_A * source_B).trace = ((1 + Real.sqrt 2 : ℝ) : ℂ) by
      simpa only [Complex.ofReal_add, Complex.ofReal_one] using source_product_trace)
    (show (source_A * source_B).det = 1 by
      rw [Matrix.det_mul, source_A_det, source_B_det, one_mul])
  rw [hcontract] at hd
  exact hd

lemma source_eigenbasis_diagonal_action (v : Fin 2 → ℂ) :
    source_eigenbasis • ![(expandingRoot (1 + Real.sqrt 2) : ℂ)*v 0,
      (expandingRoot (1 + Real.sqrt 2) : ℂ)⁻¹*v 1] =
      source_A_gl • (source_B_gl • (source_eigenbasis • v)) := by
  let a : ℂ := expandingRoot (1 + Real.sqrt 2)
  have hv : ![a*v 0,a⁻¹*v 1] = diagonal ![a,a⁻¹] *ᵥ v := by
    ext i
    fin_cases i <;> simp [Matrix.mulVec_diagonal]
  change (source_eigenbasis : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ ![a*v 0,a⁻¹*v 1] =
    source_A *ᵥ (source_B *ᵥ ((source_eigenbasis : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v))
  rw [hv, mulVec_mulVec, ← source_eigenbasis_diagonalizes_inv,
    ← mulVec_mulVec, ← mulVec_mulVec]

theorem source_invariant_local_homogeneous_metric_zero
    {ψ : (Fin 2 → ℂ) → ℝ} (hψ : HomogeneousLocalPshMetric24 ψ)
    (hA : ∀ v, ψ (source_A_gl • v) = ψ v)
    (hB : ∀ v, ψ (source_B_gl • v) = ψ v) : ∀ v, ψ v = 0 :=
  local_homogeneous_metric_zero_of_diagonal_product hψ source_eigenbasis source_A_gl
    source_B_gl source_expanding_gt_one source_eigenbasis_diagonal_action hA hB
    (projective_cube_identity source_A_cube) (projective_cube_identity source_B_cube)
    source_no_common_fixed_point

end QuadricCounterexample

end

end OAI
