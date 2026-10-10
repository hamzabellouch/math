import Mathlib
import OAI.Analysis.Crouzeix.Amplification
import OAI.Analysis.Crouzeix.ContourExistence
import OAI.Analysis.Crouzeix.ConvexNeighborhood
import OAI.Analysis.Crouzeix.RationalContours

namespace OAI

/-! Polynomial Approximation. -/

noncomputable section

open scoped Topology

open Set Filter Metric MeasureTheory

namespace CrouzeixHilbert

theorem SmoothContour.integral_deriv_mul_eq_zero_of_holomorphic
    (Γ : SmoothContour) {U : Set ℂ} (hU : IsOpen U) (hc : Convex ℝ U)
    (hΓ : Γ.trace ⊆ U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) :
    (∫ t in (0 : ℝ)..1, deriv Γ.path t * f (Γ.path t)) = 0 := by
  obtain ⟨g, hg⟩ := hc.exists_forall_hasDerivWithinAt hf
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun t => g (Γ.path t)) (deriv Γ.path t * f (Γ.path t)) t := by
    have he := ((hg _ (hΓ ⟨t, ht, rfl⟩)).hasDerivAt
      (hU.mem_nhds (hΓ ⟨t, ht, rfl⟩))).hasFDerivAt.restrictScalars ℝ
    convert! he.comp_hasDerivAt t (Γ.smooth.differentiable (by norm_num) t).hasDerivAt using 1
  have hi : IntervalIntegrable (fun t => deriv Γ.path t * f (Γ.path t))
      volume (0 : ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    exact Γ.smooth.continuous_deriv_one.continuousOn.mul
      (hf.continuousOn.comp Γ.smooth.continuous.continuousOn
        (fun t ht => hΓ ⟨t, ht, rfl⟩))
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (by simpa only [uIcc_of_le zero_le_one] using ht)) hi
  simpa only [Γ.closed, sub_self] using he

theorem SmoothContour.cauchy_formula_convex (Γ : SmoothContour) {U : Set ℂ}
    (hU : IsOpen U) (hc : Convex ℝ U) (hΓ : Γ.trace ⊆ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) {z : ℂ}
    (hz : z ∈ U) (hzΓ : z ∉ Γ.trace) :
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      (∫ t in (0 : ℝ)..1, deriv Γ.path t * f (Γ.path t) / (Γ.path t - z)) =
      Γ.index z * f z := by
  have hd : DifferentiableOn ℂ (dslope f z) U :=
    (Complex.differentiableOn_dslope (hU.mem_nhds hz)).mpr hf
  have hi : IntervalIntegrable (fun t => deriv Γ.path t * dslope f z (Γ.path t))
      volume (0 : ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    exact Γ.smooth.continuous_deriv_one.continuousOn.mul
      (hd.continuousOn.comp Γ.smooth.continuous.continuousOn (fun t ht => hΓ ⟨t, ht, rfl⟩))
  have he : (∫ t in (0 : ℝ)..1, deriv Γ.path t * f (Γ.path t) / (Γ.path t - z)) =
      (∫ t in (0 : ℝ)..1, deriv Γ.path t * dslope f z (Γ.path t)) +
      (∫ t in (0 : ℝ)..1, deriv Γ.path t / (Γ.path t - z)) * f z := by
    rw [← intervalIntegral.integral_mul_const, ← intervalIntegral.integral_add hi
      ((Γ.intervalIntegrable_indexIntegrand hzΓ).mul_const (f z))]
    apply intervalIntegral.integral_congr
    intro t ht
    have hne : Γ.path t ≠ z := fun he => hzΓ ⟨t, by simpa using ht, he⟩
    dsimp only
    rw [dslope_of_ne _ hne]
    simp only [slope, vsub_eq_sub, smul_eq_mul]
    ring
  rw [he, Γ.integral_deriv_mul_eq_zero_of_holomorphic hU hc hΓ hd, zero_add]
  exact (mul_assoc _ _ _).symm

def compactCauchyKernel (K : Set ℂ) (w : ↥(Kᶜ)) : C(K, ℂ) :=
  ⟨fun z => ((w : ℂ) - z)⁻¹, (continuous_const.sub continuous_subtype_val).inv₀
    (by
      intro z he
      apply w.property
      rw [show (w : ℂ) = (z : ℂ) from sub_eq_zero.mp he]
      exact z.property)⟩

theorem continuous_compactCauchyKernel (K : Set ℂ) : Continuous (compactCauchyKernel K) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  apply ((continuous_subtype_val.comp continuous_fst).sub
    (continuous_subtype_val.comp continuous_snd)).inv₀
  intro wz he
  apply wz.1.property
  rw [show (wz.1 : ℂ) = (wz.2 : ℂ) from sub_eq_zero.mp he]
  exact wz.2.property

theorem compactCauchyKernel_mem_iff_resolvent {K : Set ℂ}
    (S : Subalgebra ℂ C(K, ℂ)) (x : S) (hx : ∀ z : K, (x : C(K, ℂ)) z = z)
    (w : ↥(Kᶜ)) : compactCauchyKernel K w ∈ S ↔ (w : ℂ) ∈ resolventSet ℂ x := by
  change _ ↔ IsUnit (algebraMap ℂ S (w : ℂ) - x)
  rw [isUnit_iff_exists_inv]
  constructor
  · intro hw
    refine ⟨⟨compactCauchyKernel K w, hw⟩, ?_⟩
    apply Subtype.ext
    apply ContinuousMap.ext
    intro z
    change ((w : ℂ) - (x : C(K, ℂ)) z) * ((w : ℂ) - z)⁻¹ = 1
    rw [hx]
    exact mul_inv_cancel₀ (fun he => w.property
      ((sub_eq_zero.mp he).symm ▸ z.property))
  · rintro ⟨y, hy⟩
    have he : compactCauchyKernel K w = (y : C(K, ℂ)) := by
      ext z
      have hp := congrArg (fun f : S => (f : C(K, ℂ)) z) hy
      change ((w : ℂ) - (x : C(K, ℂ)) z) * (y : C(K, ℂ)) z = 1 at hp
      rw [hx] at hp
      exact inv_eq_of_mul_eq_one_right hp
    rw [he]
    exact y.property

theorem coordinate_resolventSet_subset_compl {K : Set ℂ}
    (S : Subalgebra ℂ C(K, ℂ)) (x : S) (hx : ∀ z : K, (x : C(K, ℂ)) z = z) :
    resolventSet ℂ x ⊆ Kᶜ := by
  intro v hv hvin
  obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp hv
  have he := congrArg (fun f : S => (f : C(K, ℂ)) ⟨v, hvin⟩) hy
  change (v - (x : C(K, ℂ)) ⟨v, hvin⟩) * (y : C(K, ℂ)) ⟨v, hvin⟩ = 1 at he
  rw [hx, sub_self, zero_mul] at he
  exact zero_ne_one he

theorem compactCauchyKernel_mem_polynomialClosure {K : Set ℂ} [CompactSpace K]
    (hne : K.Nonempty) (hc : IsConnected Kᶜ) (w : ↥(Kᶜ)) :
    compactCauchyKernel K w ∈ (polynomialFunctions K).topologicalClosure := by
  have : Nonempty K := hne.to_subtype
  let S := (polynomialFunctions K).topologicalClosure
  have : IsClosed (S : Set C(K, ℂ)) := (polynomialFunctions K).isClosed_topologicalClosure
  have : CompleteSpace S := IsClosed.completeSpace_coe
  have : NormOneClass S := ⟨by change ‖(1 : C(K, ℂ))‖ = 1; exact norm_one⟩
  let x : S := ⟨Polynomial.X.toContinuousMapOn K,
    (polynomialFunctions K).le_topologicalClosure (by
      rw [← SetLike.mem_coe, polynomialFunctions_coe]
      exact ⟨Polynomial.X, rfl⟩)⟩
  have hx (z : K) : (x : C(K, ℂ)) z = z := by simp [x]
  have hiff := compactCauchyKernel_mem_iff_resolvent S x hx
  have hsub := coordinate_resolventSet_subset_compl S x hx
  have hcl : IsClopen {w : ↥(Kᶜ) | compactCauchyKernel K w ∈ S} := by
    refine ⟨(show IsClosed (S : Set C(K, ℂ)) from inferInstance).preimage
      (continuous_compactCauchyKernel K), ?_⟩
    have he : {w : ↥(Kᶜ) | compactCauchyKernel K w ∈ S} =
        Subtype.val ⁻¹' resolventSet ℂ x := by ext w; exact hiff w
    rw [he]
    exact (spectrum.isOpen_resolventSet x).preimage continuous_subtype_val
  have hgood : {w : ↥(Kᶜ) | compactCauchyKernel K w ∈ S}.Nonempty := by
    let v : ℂ := (‖x‖ + 1 : ℝ)
    have hv : v ∈ resolventSet ℂ x := by
      apply spectrum.mem_resolventSet_of_norm_lt
      simp only [v, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0 : ℝ) < ‖x‖ + 1)]
      linarith
    exact ⟨⟨v, hsub hv⟩, (hiff _).mpr hv⟩
  have : PreconnectedSpace ↥(Kᶜ) := isPreconnected_iff_preconnectedSpace.mp hc.isPreconnected
  have he := Set.mem_univ w
  rwa [← hcl.eq_univ hgood] at he

def compactCauchyKernelExtension (K : Set ℂ) (w : ℂ) : C(K, ℂ) := by
  classical
  exact if hw : w ∈ Kᶜ then compactCauchyKernel K ⟨w, hw⟩ else 0

@[simp]
theorem compactCauchyKernelExtension_apply {K : Set ℂ} {w : ℂ} (hw : w ∉ K) (z : K) :
    compactCauchyKernelExtension K w z = (w - z)⁻¹ := by
  classical
  unfold compactCauchyKernelExtension
  split
  · rfl
  · contradiction

theorem continuousOn_compactCauchyKernelExtension (K : Set ℂ) :
    ContinuousOn (compactCauchyKernelExtension K) Kᶜ := by
  rw [continuousOn_iff_continuous_domRestrict]
  convert! continuous_compactCauchyKernel K using 1
  ext w z
  exact compactCauchyKernelExtension_apply w.property z

theorem intervalIntegral_mem_closedSubalgebra {E : Type*} [NormedCommRing E]
    [NormedAlgebra ℂ E] [CompleteSpace E] (S : Subalgebra ℂ E)
    (hS : IsClosed (S : Set E)) {g : ℝ → E}
    (hg : IntervalIntegrable g volume 0 1)
    (hm : ∀ t ∈ Icc (0 : ℝ) 1, g t ∈ S) :
    (∫ t in (0 : ℝ)..1, g t) ∈ S := by
  have : IsProbabilityMeasure (volume.restrict (Ioc (0 : ℝ) 1)) := ⟨by simp⟩
  rw [intervalIntegral.integral_of_le zero_le_one]
  exact (S.toSubmodule.restrictScalars ℝ).convex.integral_mem hS
    ((ae_restrict_mem measurableSet_Ioc).mono (fun t ht => hm t (Ioc_subset_Icc_self ht))) hg.1

theorem holomorphic_mem_polynomialClosure_of_convex_neighborhood
    {K U : Set ℂ} [CompactSpace K] (hK : K.Nonempty) (hcomp : IsConnected Kᶜ)
    (hU : IsOpen U) (hUc : Convex ℝ U) (hKU : K ⊆ U)
    (Γ : CalculusContour K U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) :
    (⟨fun z : K => f z, hf.continuousOn.mono hKU |>.domRestrict⟩ : C(K, ℂ)) ∈
      (polynomialFunctions K).topologicalClosure := by
  let S := (polynomialFunctions K).topologicalClosure
  let g : ℝ → C(K, ℂ) := fun t =>
    (deriv Γ.path t * f (Γ.path t)) • compactCauchyKernelExtension K (Γ.path t)
  have hg : ContinuousOn g (Icc (0 : ℝ) 1) := by
    exact (Γ.smooth.continuous_deriv_one.continuousOn.mul
      (hf.continuousOn.comp Γ.smooth.continuous.continuousOn
        (fun t ht => (Γ.avoids t ht).1))).smul
      ((continuousOn_compactCauchyKernelExtension K).comp Γ.smooth.continuous.continuousOn
        (fun t ht => (Γ.avoids t ht).2))
  have hi : IntervalIntegrable g volume (0 : ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le zero_le_one] using hg
  have hm : ∀ t ∈ Icc (0 : ℝ) 1, g t ∈ S := by
    intro t ht
    apply S.smul_mem
    classical
    unfold compactCauchyKernelExtension
    split
    · exact compactCauchyKernel_mem_polynomialClosure hK hcomp _
    · rename_i he
      exact (he (Γ.avoids t ht).2).elim
  have he : (2 * (Real.pi : ℂ) * Complex.I)⁻¹ • (∫ t in (0 : ℝ)..1, g t) =
      (⟨fun z : K => f z, hf.continuousOn.mono hKU |>.domRestrict⟩ : C(K, ℂ)) := by
    ext z
    change (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      (ContinuousMap.evalCLM ℂ z (∫ t in (0 : ℝ)..1, g t)) = f z
    rw [← (ContinuousMap.evalCLM ℂ z).intervalIntegral_comp_comm hi]
    have he : (∫ t in (0 : ℝ)..1, ContinuousMap.evalCLM ℂ z (g t)) =
        (∫ t in (0 : ℝ)..1, deriv Γ.path t * f (Γ.path t) / (Γ.path t - z)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      change (deriv Γ.path t * f (Γ.path t)) * compactCauchyKernelExtension K (Γ.path t) z = _
      dsimp only
      rw [compactCauchyKernelExtension_apply (Γ.avoids t (by simpa using ht)).2, div_eq_mul_inv]
    rw [he, Γ.toSmoothContour.cauchy_formula_convex hU hUc
      (by rintro _ ⟨t, ht, rfl⟩; exact (Γ.avoids t ht).1) hf (hKU z.property) ?_, Γ.index_inside z z.property, one_mul]
    rintro ⟨t, ht, htΓ⟩
    exact (Γ.avoids t ht).2 (htΓ.symm ▸ z.property)
  rw [← he]
  exact S.smul_mem (intervalIntegral_mem_closedSubalgebra S
    (polynomialFunctions K).isClosed_topologicalClosure hi hm) _

theorem exists_polynomial_uniform_approx {K U : Set ℂ}
    (hK : IsCompact K) (hc : Convex ℝ K) (hU : IsOpen U) (hKU : K ⊆ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Polynomial ℂ, ∀ z ∈ K, ‖p.eval z - f z‖ < ε := by
  rcases K.eq_empty_or_nonempty with he | hne
  · exact ⟨0, by simp [he]⟩
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  let V := thickening δ K
  have hVo : IsOpen V := isOpen_thickening
  have hVc : Convex ℝ V := hc.thickening δ
  have hKV : K ⊆ V := self_subset_thickening hδ K
  have hVU : V ⊆ U := (thickening_subset_cthickening δ K).trans hδU
  obtain ⟨Γ⟩ := exists_calculusContour hK hc hne hVo hKV
  let g : C(K, ℂ) := ⟨fun z => f z, (hf.continuousOn.mono hKU).domRestrict⟩
  have hg : g ∈ (polynomialFunctions K).topologicalClosure :=
    holomorphic_mem_polynomialClosure_of_convex_neighborhood hne
      (isPathConnected_compl_of_bounded_convex hK.isBounded hc).isConnected
      hVo hVc hKV Γ (hf.mono hVU)
  change g ∈ closure (polynomialFunctions K : Set C(K, ℂ)) at hg
  obtain ⟨q, hq, hd⟩ := Metric.mem_closure_iff.mp hg ε hε
  rw [polynomialFunctions_coe] at hq
  obtain ⟨p, rfl⟩ := hq
  refine ⟨p, fun z hz => ?_⟩
  have hle := ContinuousMap.dist_apply_le_dist (f := g)
    (g := Polynomial.toContinuousMapOn p K) ⟨z, hz⟩
  rw [← dist_eq_norm, dist_comm]
  exact lt_of_le_of_lt hle hd

open scoped Matrix.Norms.L2Operator

theorem matrix_norm_le_entry_bound {m : ℕ} (B : Coeff m) {δ : ℝ}
    (hB : ∀ i j, ‖B i j‖ ≤ δ) :
    ‖B‖ ≤ δ * (∑ i : Fin m, ∑ j : Fin m, ‖(Matrix.single i j (1 : ℂ) : Coeff m)‖) := by
  have he : B = ∑ i, ∑ j, B i j • Matrix.single i j (1 : ℂ) := by
    simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using Matrix.matrix_eq_sum_single B
  calc
    ‖B‖ = ‖∑ i, ∑ j, B i j • Matrix.single i j (1 : ℂ)‖ := congrArg norm he
    _ ≤ ∑ i, ∑ j, ‖B i j • (Matrix.single i j (1 : ℂ) : Coeff m)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => norm_sum_le _ _))
    _ ≤ ∑ i, ∑ j, δ * ‖(Matrix.single i j (1 : ℂ) : Coeff m)‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (hB i j) (norm_nonneg _)
    _ = δ * (∑ i, ∑ j, ‖(Matrix.single i j (1 : ℂ) : Coeff m)‖) := by
      simp only [Finset.mul_sum]

theorem exists_matrixPolynomial_entries {m : ℕ}
    (p : Fin m → Fin m → Polynomial ℂ) :
    ∃ d : ℕ, ∃ B : Fin (d + 1) → Coeff m,
      ∀ z i j, matrixPolynomial B z i j = (p i j).eval z := by
  classical
  let d := Finset.univ.sup (fun i : Fin m => Finset.univ.sup (fun j : Fin m => (p i j).natDegree))
  refine ⟨d, fun k i j => (p i j).coeff k, ?_⟩
  intro z i j
  have hd : (p i j).natDegree < d + 1 := Nat.lt_succ_of_le (le_trans
    (Finset.le_sup (f := fun j : Fin m => (p i j).natDegree) (Finset.mem_univ j))
    (Finset.le_sup (f := fun i : Fin m => Finset.univ.sup (fun j : Fin m => (p i j).natDegree))
      (Finset.mem_univ i)))
  rw [Polynomial.eval_eq_sum_range' hd]
  simp only [matrixPolynomial, Matrix.sum_apply]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

theorem exists_matrixPolynomial_uniform_approx {m : ℕ} {K U : Set ℂ}
    (hK : IsCompact K) (hc : Convex ℝ K) (hU : IsOpen U) (hKU : K ⊆ U)
    {F : ℂ → Coeff m} (hF : EntrywiseHolomorphic U F) {ε : ℝ} (hε : 0 < ε) :
    ∃ d : ℕ, ∃ B : Fin (d + 1) → Coeff m, ∀ z ∈ K, ‖matrixPolynomial B z - F z‖ < ε := by
  classical
  let C : ℝ := ∑ i : Fin m, ∑ j : Fin m, ‖(Matrix.single i j (1 : ℂ) : Coeff m)‖
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have he : 0 < ε / (C + 1) := div_pos hε (by linarith)
  have hp := fun i j => exists_polynomial_uniform_approx hK hc hU hKU (hF i j) he
  choose p hp using hp
  obtain ⟨d, B, hB⟩ := exists_matrixPolynomial_entries p
  refine ⟨d, B, fun z hz => ?_⟩
  calc
    ‖matrixPolynomial B z - F z‖ ≤ (ε / (C + 1)) * C :=
      matrix_norm_le_entry_bound _ (fun i j => by
        simpa only [Matrix.sub_apply, hB] using (hp i j z hz).le)
    _ < (ε / (C + 1)) * (C + 1) := mul_lt_mul_of_pos_left (by linarith) he
    _ = ε := div_mul_cancel₀ _ (by linarith)

theorem exists_matrixPolynomial_tendstoUniformlyOn {m : ℕ} {K U : Set ℂ}
    (hK : IsCompact K) (hc : Convex ℝ K) (hU : IsOpen U) (hKU : K ⊆ U)
    {F : ℂ → Coeff m} (hF : EntrywiseHolomorphic U F) :
    ∃ degrees : ℕ → ℕ, ∃ B : (n : ℕ) → Fin (degrees n + 1) → Coeff m,
      TendstoUniformlyOn (fun n => matrixPolynomial (B n)) F atTop K := by
  have he (n : ℕ) : (0 : ℝ) < 1 / (n + 1) := by positivity
  choose degrees B hB using fun n => exists_matrixPolynomial_uniform_approx hK hc hU hKU hF (he n)
  refine ⟨degrees, B, Metric.tendstoUniformlyOn_iff.mpr (fun ε hε => ?_)⟩
  have ht : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn z hz
  rw [dist_comm, dist_eq_norm]
  exact (hB n z hz).trans hn

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem exists_contour_bound_of_polynomial_bound [CompleteSpace H] [Nontrivial H]
    (A : Operator H) {m : ℕ} {U : Set ℂ} (F : ℂ → Coeff m)
    (hU : IsOpen U) (hKU : numericalClosure A ⊆ U) (hF : EntrywiseHolomorphic U F)
    (hpoly : ∀ (d : ℕ) (B : Fin (d + 1) → Coeff m),
      ‖polynomialEval A B‖ ≤ 2 * supNorm (numericalRange A) (matrixPolynomial B)) :
    ∃ Γ : CalculusContour (numericalClosure A) U,
      ‖matrixContourEval A Γ.toSmoothContour F‖ ≤ 2 * supNorm (numericalClosure A) F := by
  obtain ⟨ε, _hε, hL, hLc, hKL, hLU, _hcomp⟩ := exists_compact_convex_neighborhood A hU hKU
  obtain ⟨Γ⟩ := exists_calculusContour (isCompact_numericalClosure A)
    (convex_numericalClosure A) (numericalClosure_nonempty A) isOpen_interior hKL
  let Δ : CalculusContour (numericalClosure A) U :=
    { toSmoothContour := Γ.toSmoothContour
      avoids := fun t ht => ⟨hLU (interior_subset (Γ.avoids t ht).1), (Γ.avoids t ht).2⟩
      index_inside := Γ.index_inside
      index_outside := fun z hz => Γ.index_outside z (fun he => hz (hLU (interior_subset he))) }
  obtain ⟨degrees, B, happ⟩ := exists_matrixPolynomial_tendstoUniformlyOn hL hLc hU hLU hF
  refine ⟨Δ, contour_bound_of_uniform_polynomials A Δ F (hF.continuousOn.mono hKU)
    hpoly degrees B (happ.mono ?_)⟩
  rintro z (hz | ⟨t, ht, rfl⟩)
  · exact interior_subset (hKL hz)
  · exact interior_subset (Γ.avoids t ht).1

theorem holomorphicEval_eq_contourEval_of_independent (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) (f : ℂ → ℂ)
    (hind : ∀ Δ : CalculusContour (numericalClosure A) U,
      contourEval A Δ.toSmoothContour f = contourEval A Γ.toSmoothContour f) :
    holomorphicEval A U f = contourEval A Γ.toSmoothContour f := by
  classical
  rw [holomorphicEval, dite_eq_left (show Nonempty (CalculusContour (numericalClosure A) U) from ⟨Γ⟩)]
  exact hind _

theorem nonzeroConclusion_of_finite_bound_and_contour_independence
    [CompleteSpace H] [Nontrivial H] (A : Operator H)
    (hfin : FiniteMatrixPolynomialBound)
    (hind : ∀ (U : Set ℂ), IsOpen U → numericalClosure A ⊆ U →
      ∀ (f : ℂ → ℂ), DifferentiableOn ℂ f U →
      ∀ Γ Δ : CalculusContour (numericalClosure A) U,
        contourEval A Γ.toSmoothContour f = contourEval A Δ.toSmoothContour f) :
    NonzeroConclusion A := by
  have hhol (m : ℕ) (hm : 0 < m) (U : Set ℂ) (F : ℂ → Coeff m)
      (hU : IsOpen U) (hKU : numericalClosure A ⊆ U) (hF : EntrywiseHolomorphic U F) :
      Nonempty (CalculusContour (numericalClosure A) U) ∧
      (∀ Γ : CalculusContour (numericalClosure A) U, ∀ i j,
        holomorphicEval A U (fun z => F z i j) =
          contourEval A Γ.toSmoothContour (fun z => F z i j)) ∧
      ‖matrixHolomorphicEval A U F‖ ≤ 2 * supNorm (numericalClosure A) F ∧
      ∃ z ∈ numericalClosure A, supNorm (numericalClosure A) F = ‖F z‖ := by
    obtain ⟨Γ, hb⟩ := exists_contour_bound_of_polynomial_bound A F hU hKU hF
      (fun _ B => polynomial_bound_of_finite_matrix_bound hfin A hm B)
    have hsame (Δ : CalculusContour (numericalClosure A) U) (i j : Fin m) :
        holomorphicEval A U (fun z => F z i j) =
          contourEval A Δ.toSmoothContour (fun z => F z i j) :=
      holomorphicEval_eq_contourEval_of_independent A Δ _
        (fun Γ => hind U hU hKU _ (hF i j) Γ Δ)
    refine ⟨⟨Γ⟩, hsame, ?_, holomorphic_sup_attained A hKU hF⟩
    have he : matrixHolomorphicEval A U F = matrixContourEval A Γ.toSmoothContour F := by
      simp only [matrixHolomorphicEval, matrixContourEval, hsame Γ]
    rwa [he]
  refine ⟨isCompact_numericalClosure A, convex_numericalClosure A,
    spectrum_subset_numericalClosure A, ?_, hhol, ?_⟩
  · intro m hm d B
    exact ⟨polynomial_bound_of_finite_matrix_bound hfin A hm B, polynomial_sup_eq_max A B⟩
  · intro m hm R hR
    exact rational_conclusion_of_holomorphic_bound A
      (fun U F hU hKU hF => ⟨(hhol m hm U F hU hKU hF).1, (hhol m hm U F hU hKU hF).2.2.1⟩)
      R hR

end CrouzeixHilbert

end

end OAI
