import OAI.Geometry.RuledCovering.Hyperbolic

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma IsParallelogram.isCompact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Set E} (hP : IsParallelogram P) : IsCompact P := by
  obtain ⟨c, u, v, _, rfl⟩ := hP
  have hc : IsCompact ((fun z : ℝ × ℝ => c + z.1 • u + z.2 • v) ''
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) :=
    (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  convert hc using 1
  ext x
  constructor
  · rintro ⟨s, hs, t, ht, rfl⟩
    exact ⟨(s,t), ⟨hs,ht⟩, rfl⟩
  · rintro ⟨⟨s,t⟩, ⟨hs,ht⟩, rfl⟩
    exact ⟨s,hs,t,ht,rfl⟩

lemma Cylinder.enlarge_open {C : Cylinder} (hC : C.parallelogram) {eps : ℝ} (heps : 0 < eps) :
    ∃ D : Cylinder, D.openBounded ∧ C.carrier ⊆ D.carrier ∧ D.area < C.area + eps := by
  obtain ⟨O, hOo, hOb, hCO, _, _, hOI⟩ := exists_nice_outer_integral
    hC.isCompact isOpen_univ (subset_univ _) (continuous_const : Continuous (fun _ => (1 : ℝ)))
    (fun _ => zero_le_one) heps
  refine ⟨⟨C.axis, C.unit_axis, O⟩, ⟨hOo,hOb,hOo.measurableSet⟩, ?_, ?_⟩
  · rintro x ⟨b,hb,t,hx⟩
    exact ⟨b,hCO hb,t,hx⟩
  · change volume.real O < volume.real C.base + eps
    simpa only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul, mul_one] using hOI

/-- Compact parallelogram covers admit bounded open perpendicular bases with any
additional positive error. No portion of the closed ruled family is discarded. -/
lemma HasFiniteCover.open_enlarge {S : Set Space} {A eps : ℝ}
    (hc : HasFiniteCover Cylinder.parallelogram S A) (heps : 0 < eps) :
    HasFiniteCover Cylinder.openBounded S (A+eps) := by
  classical
  obtain ⟨n,C,hC,hcov,hcost⟩ := hc
  have hd : 0 < eps / (n+1 : ℝ) := div_pos heps (by positivity)
  choose D hD hCD harea using fun i => Cylinder.enlarge_open (hC i) hd
  refine ⟨n,D,hD,?_,?_⟩
  · intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp (hcov hx)
    exact mem_iUnion.mpr ⟨i,hCD i hi⟩
  · change (∑ i, (D i).area) ≤ A+eps
    calc
      _ ≤ ∑ i, ((C i).area + eps/(n+1 : ℝ)) := Finset.sum_le_sum (fun i _ => (harea i).le)
      _ = familyArea C + n * (eps/(n+1 : ℝ)) := by simp [familyArea, Finset.sum_add_distrib]
      _ ≤ A + eps := by
        have hn : 0 < (n+1 : ℝ) := by positivity
        have hne : (n : ℝ) * (eps/(n+1 : ℝ)) ≤ eps := by
          rw [← mul_div_assoc, div_le_iff₀ hn]
          nlinarith
        exact add_le_add hcost hne

/-- The product-cell endpoint follows from the stronger arbitrary-compact producer
and exact open-base enlargement. -/
theorem productCell : ProductCellStatement := by
  intro h M D v hh hM hD _ hv hH e he
  have hc := physical_hyperbolic_cover hh hM hD hv hH (half_pos he)
  have ho := hc.open_enlarge (half_pos he)
  convert ho using 1
  ring

lemma plane_charpoly (A : Plane →ₗ[ℝ] Plane) :
    A.charpoly = Polynomial.X ^ 2 -
      Polynomial.C (LinearMap.trace ℝ Plane A) * Polynomial.X + Polynomial.C (LinearMap.det A) := by
  rw [← LinearMap.charpoly_toMatrix A (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis,
    Matrix.charpoly_fin_two, LinearMap.det_toMatrix,
    ← LinearMap.trace_eq_matrix_trace]

lemma plane_hyperbolic_eigenvalues (A : Plane →ₗ[ℝ] Plane)
    (ht : LinearMap.trace ℝ Plane A = 0) (hd : LinearMap.det A < 0) :
    Module.End.HasEigenvalue A (Real.sqrt (-LinearMap.det A)) ∧
    Module.End.HasEigenvalue A (-Real.sqrt (-LinearMap.det A)) := by
  have hs : Real.sqrt (-LinearMap.det A) ^ 2 = -LinearMap.det A :=
    Real.sq_sqrt (by linarith)
  constructor <;> rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Polynomial.IsRoot,
    plane_charpoly, ht] <;> simp [hs]

lemma eigenvalue_le_norm (A : Plane →L[ℝ] Plane) {lam : ℝ} (hlam : 0 ≤ lam)
    (h : Module.End.HasEigenvalue A.toLinearMap lam) : lam ≤ ‖A‖ := by
  obtain ⟨u, hu⟩ := h.exists_hasEigenvector
  have hue : A u = lam • u := hu.apply_eq_smul
  have hn := A.le_opNorm u
  rw [hue, norm_smul, Real.norm_eq_abs, abs_of_nonneg hlam] at hn
  exact le_of_mul_le_mul_right hn (norm_pos_iff.mpr hu.2)

lemma eigenvalue_smul (A : Plane →ₗ[ℝ] Plane) {lam : ℝ}
    (hlam : Module.End.HasEigenvalue A lam) (k : ℝ) :
    Module.End.HasEigenvalue (k • A) (k * lam) := by
  obtain ⟨u, hu⟩ := hlam.exists_hasEigenvector
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := u)
  constructor
  · rw [Module.End.mem_eigenspace_iff]
    change k • A u = (k*lam) • u
    rw [hu.apply_eq_smul, mul_smul]
  · exact hu.2

/-- The orthogonal-grid endpoint needs no new cover construction: its norm bound
implies precisely the two-eigenvalue condition of the general theorem. -/
theorem orthogonalGrid : OrthogonalGridStatement := by
  intro D v kappa hD _ hv hk hH e he
  have hhyp : ∀ p ∈ D, HyperbolicAt 1 v p := by
    intro p hp
    obtain ⟨ht,hd,hn⟩ := hH p hp
    obtain ⟨hplus,hminus⟩ := plane_hyperbolic_eigenvalues (fderiv ℝ v p).toLinearMap ht hd
    have hlam : 0 < Real.sqrt (-LinearMap.det (fderiv ℝ v p).toLinearMap) :=
      Real.sqrt_pos.mpr (neg_pos.mpr hd)
    refine ⟨_, by simpa using hlam, ?_, hplus, hminus⟩
    simpa only [one_mul] using ((eigenvalue_le_norm _ hlam.le hplus).trans hn).trans_lt hk
  have hc := physical_hyperbolic_cover (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2))
    (by norm_num : (0:ℝ)<1) hD hv hhyp he
  simpa only [physicalWeight, Real.sq_sqrt (by norm_num : (0:ℝ)≤2)] using hc

lemma OpenRectangleC2.smoothNear {D : Set Plane} {v : Plane → Plane}
    (hv : OpenRectangleC2 D v) : SmoothNear 1 D v := by
  obtain ⟨a,b,_,hD,hv⟩ := hv
  refine ⟨{p | ∀ i, p i ∈ Ioo (a i) (b i)}, ?_,hD,hv.of_le (by norm_num)⟩
  have he : {p : Plane | ∀ i, p i ∈ Ioo (a i) (b i)} =
      ⋂ i : Fin 2, (fun p : Plane => p i) ⁻¹' Ioo (a i) (b i) := by ext p; simp
  rw [he]
  exact isOpen_iInter_of_finite (fun i => isOpen_Ioo.preimage (by fun_prop))

/-- The logarithmic-cell endpoint follows with its exact velocity scaling and
orthonormal-coordinate weight, while its boundary hypothesis remains local. -/
theorem logarithmic : LogarithmicStatement := by
  intro X k D v hX hk hD _ hv hH e he
  obtain ⟨U,hU,hDU,hv1⟩ := hv.smoothNear
  have hw : SmoothNear 1 D (fun p => k • v p) :=
    ⟨U,hU,hDU,hv1.const_smul k⟩
  have hhyp : ∀ p ∈ D, HyperbolicAt X (fun p => k • v p) p := by
    intro p hp
    obtain ⟨ht,hd,hsmall⟩ := hH p hp
    obtain ⟨hplus,hminus⟩ := plane_hyperbolic_eigenvalues (fderiv ℝ v p).toLinearMap ht hd
    have hlam : 0 < Real.sqrt (-LinearMap.det (fderiv ℝ v p).toLinearMap) :=
      Real.sqrt_pos.mpr (neg_pos.mpr hd)
    have hder := ((hv1.contDiffAt (hU.mem_nhds (hDU hp))).differentiableAt
      (by norm_num)).hasFDerivAt.const_smul k
    have hf : fderiv ℝ (fun p => k • v p) p = k • fderiv ℝ v p := hder.fderiv
    refine ⟨k*Real.sqrt (-LinearMap.det (fderiv ℝ v p).toLinearMap), by positivity,
      by nlinarith, ?_, ?_⟩
    · rw [hf]
      exact eigenvalue_smul _ hplus k
    · rw [hf]
      change Module.End.HasEigenvalue (k • (fderiv ℝ v p).toLinearMap) (- (k * _))
      rw [← mul_neg]
      exact eigenvalue_smul _ hminus k
  have hc := physical_hyperbolic_cover (by norm_num : (0:ℝ)<1) hX hD hw hhyp (half_pos he)
  have ho := hc.open_enlarge (half_pos he)
  convert ho using 1
  rw [one_mul]
  have hint : (∫ p in D, physicalWeight 1 (k • v p)) =
      ∫ p in D, 1 / Real.sqrt (1 + k ^ 2 * ‖v p‖ ^ 2) := by
    apply integral_congr_ae
    filter_upwards [] with p
    rw [physicalWeight_one, weight, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [hint]
  ring

end RuledApproximation

end

end OAI
