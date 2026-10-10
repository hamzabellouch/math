import OAI.Geometry.Arnold.Descent

namespace OAI

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped Topology
open Function

namespace ArnoldCounterexample.CriticalBound
open ArnoldCounterexample.Quadric

lemma unit_phase (z : UnitQuadric) (a : ℂ) (ha : Complex.normSq a = 1) :
    IsUnitQuadric (a • (z : CV)) := by
  constructor
  · rw [normSquared_smul, ha, z.property.1, mul_one]
  · rw [quadricPolynomial_smul, z.property.2, mul_zero]

lemma project_phase (z : UnitQuadric) (a : ℂ) (ha : Complex.normSq a = 1) :
    project ⟨a • (z : CV), unit_phase z a ha⟩ = project z := by
  apply Subtype.ext
  exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨a, rfl⟩

lemma project_eq_phase (z w : UnitQuadric) (heq : project w = project z) :
    ∃ a : ℂ, Complex.normSq a = 1 ∧ (w : CV) = a • (z : CV) := by
  have hp := congrArg Subtype.val heq
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp hp
  have hn := w.property.1
  rw [← ha, normSquared_smul, z.property.1, mul_one] at hn
  exact ⟨a, hn, ha.symm⟩

lemma extension_phase {h : Q3 → ℝ} {G : CV → ℝ}
    (hGagree : ∀ z : UnitQuadric, G z = h (project z))
    (z : UnitQuadric) (a : ℂ) (ha : Complex.normSq a = 1) :
    G (a • (z : CV)) = G z := by
  rw [hGagree ⟨a • (z : CV), unit_phase z a ha⟩, project_phase z a ha, hGagree z]

/-- Every local lift has the same horizontal derivative as a global extension;
this follows from the explicit curves in the actual quadric. -/
lemma local_lift_derivative_eq {h : Q3 → ℝ} {G : CV → ℝ}
    (hG : ContDiff ℝ ∞ G) (hGagree : ∀ z : UnitQuadric, G z = h (project z))
    (z : UnitQuadric) (U : Set CV) (g : CV → ℝ)
    (hg : LocalFunctionLift h z U g) (v : CV) (hv : Horizontal z v) :
    fderiv ℝ g z v = fderiv ℝ G z v := by
  obtain ⟨hU, hzU, hgs, hagree⟩ := hg
  have hc := tangentCurve_hasDerivAt_zero z v hv
  have hd := (hgs.contDiffAt (hU.mem_nhds hzU)).differentiableAt (by simp)
  have hd' : HasFDerivAt g (fderiv ℝ g z) (tangentCurve z v hv 0 : CV) := by
    simpa only [tangentCurve_zero] using hd.hasFDerivAt
  have hcomp := hd'.comp_hasDerivAt 0 hc
  have hglobal := (hG.differentiable (by simp) (tangentCurve z v hv 0 : CV)).hasFDerivAt.comp_hasDerivAt 0 hc
  have hmem : ∀ᶠ t in nhds (0 : ℝ), (tangentCurve z v hv t : CV) ∈ U :=
    hc.continuousAt.eventually (by convert! hU.mem_nhds hzU using 1; simp)
  have heq : (fun t ↦ g (tangentCurve z v hv t)) =ᶠ[nhds (0 : ℝ)]
      (fun t ↦ G (tangentCurve z v hv t)) := by
    filter_upwards [hmem] with t ht
    rw [hagree _ ht, hGagree]
  have hsame := hcomp.congr_of_eventuallyEq heq.symm
  simpa only [tangentCurve_zero] using hsame.unique hglobal

lemma stationary_isCritical {h : Q3 → ℝ} {G : CV → ℝ}
    (hG : ContDiff ℝ ∞ G) (hGagree : ∀ z : UnitQuadric, G z = h (project z))
    (z : UnitQuadric) (hz : gradientSquare G z = 0) :
    IsCritical h (project z) := by
  intro w hw U g hg v hv
  obtain ⟨a, ha, hwa⟩ := project_eq_phase z w hw
  have hzero : gradientSquare G w = 0 := by
    rw [hwa, gradientSquare_phase G hG (extension_phase hGagree) z a ha, hz]
  rw [local_lift_derivative_eq hG hGagree w U g hg v hv]
  exact horizontal_derivative_of_rotation_zero G w
    ((gradientSquare_eq_zero_iff G w).mp hzero) v hv

end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample.CriticalBound
open ArnoldCounterexample.Quadric ArnoldCounterexample.Descent

/-- Smooth phase-equivariant, strictly descending discrete deformation of the
literal quadric. This supplies the deformation step for arbitrary smooth functions,
including highly degenerate ones, without assuming an ODE existence theorem. -/
theorem exists_smooth_descent {h : Q3 → ℝ} {G : CV → ℝ}
    (hG : ContDiff ℝ ∞ G) (hGagree : ∀ z : UnitQuadric, G z = h (project z)) :
    ∃ D : CV → CV, ContDiff ℝ ∞ D ∧
      (∀ z : UnitQuadric, IsUnitQuadric (D z)) ∧
      (∀ z : UnitQuadric, ∀ a : ℂ, Complex.normSq a = 1 → D (a • (z : CV)) = a • D z) ∧
      (∀ z : UnitQuadric, G (D z) ≤ G z) ∧
      (∀ z : UnitQuadric, G (D z) = G z → IsCritical h (project z)) := by
  obtain ⟨c, _hc, hstep⟩ := adaptive_step isCompact_unitQuadric
    (fun p ↦ G (gradientCurve G p)) (hG.comp (gradientCurve_contDiff G hG))
    (gradientSquare G) (gradientSquare_contDiff G hG).continuous
    (fun z _ ↦ gradientSquare_nonneg G z)
    (fun z _ ↦ gradientCurve_lyapunov_derivative G hG z)
  let D : CV → CV := fun z ↦ gradientCurve G (c * gradientSquare G z, z)
  have hD : ContDiff ℝ ∞ D := (gradientCurve_contDiff G hG).comp
    ((contDiff_const.mul (gradientSquare_contDiff G hG)).prodMk contDiff_id)
  refine ⟨D, hD, fun z ↦ gradientCurve_preserves G _ z, ?_, ?_, ?_⟩
  · intro z a ha
    dsimp only [D]
    rw [gradientSquare_phase G hG (extension_phase hGagree) z a ha,
      gradientCurve_phase G hG (extension_phase hGagree) _ z a ha]
  · intro z
    simpa only [gradientCurve_zero] using (hstep z z.property).2.2.1
  · intro z heq
    apply stationary_isCritical hG hGagree z
    by_contra hz
    have hlt := (hstep z z.property).2.2.2 hz
    have hlt' : G (D z) < G z := by simpa only [gradientCurve_zero] using hlt
    exact (ne_of_lt hlt') heq

end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample.CriticalBound
open ArnoldCounterexample.Quadric ArnoldCounterexample.Forms ArnoldCounterexample.Descent

lemma critical_chart (h : SmoothFunction) (hf : (criticalSet h).Finite) :
    ∃ ℓ : CV →L[ℂ] ℂ, ∀ z : UnitQuadric, IsCritical h.toFun (project z) → ℓ z ≠ 0 := by
  classical
  let : Fintype (criticalSet h) := hf.fintype
  choose r hr using fun q : criticalSet h ↦ project_surjective q.val
  obtain ⟨ℓ, hℓ⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℂ)
    (fun q : criticalSet h ↦ (r q : CV)) (fun q ↦ unitQuadric_ne_zero (r q))
  refine ⟨ℓ.toContinuousLinearMap, ?_⟩
  intro z hz
  let q : criticalSet h := ⟨project z, hz⟩
  obtain ⟨a, ha, hza⟩ := project_eq_phase (r q) z (hr q).symm
  have ha0 : a ≠ 0 := fun hn ↦ by simp [hn] at ha
  change ℓ (z : CV) ≠ 0
  rw [hza, map_smul, smul_eq_mul]
  exact mul_ne_zero ha0 (hℓ q)

lemma contDiff_iterate {D : CV → CV} (hD : ContDiff ℝ ∞ D) (n : ℕ) :
    ContDiff ℝ ∞ (D^[n]) := by
  induction n with
  | zero => simpa using (contDiff_id : ContDiff ℝ ∞ (id : CV → CV))
  | succ n hn => simpa only [Function.iterate_succ] using hn.comp hD

lemma iterate_preserves {D : CV → CV}
    (hD : ∀ z : UnitQuadric, IsUnitQuadric (D z)) (n : ℕ) (z : UnitQuadric) :
    IsUnitQuadric (D^[n] z) := by
  induction n with
  | zero => exact z.property
  | succ n hn => simpa only [Function.iterate_succ_apply'] using hD ⟨_, hn⟩

lemma iterate_phase {D : CV → CV}
    (hD : ∀ z : UnitQuadric, IsUnitQuadric (D z))
    (heq : ∀ z : UnitQuadric, ∀ a : ℂ, Complex.normSq a = 1 → D (a • (z : CV)) = a • D z)
    (n : ℕ) (z : UnitQuadric) (a : ℂ) (ha : Complex.normSq a = 1) :
    D^[n] (a • (z : CV)) = a • (D^[n] z) := by
  induction n with
  | zero => rfl
  | succ n hn =>
    simpa only [Function.iterate_succ_apply', hn] using heq ⟨D^[n] z, iterate_preserves hD n z⟩ a ha

/-- Three or fewer critical points yield three nonvanishing-coordinate descent
charts, on the literal quadric, with no Morse or nondegeneracy hypotheses. -/
theorem cover_map (h : SmoothFunction) (hsmall : (criticalSet h).encard ≤ 3) :
    ∃ F : CV → CSpace 3, ContDiff ℝ ∞ F ∧
      (∀ z : UnitQuadric, F z ≠ 0) ∧
      (∀ z : UnitQuadric, ∀ a : ℂ, Complex.normSq a = 1 → F (a • (z : CV)) = a • F z) := by
  classical
  have hf : (criticalSet h).Finite := Set.finite_of_encard_le_coe hsmall
  obtain ⟨G, hG, hagree⟩ := Extension.global_extension isCompact_unitQuadric
    (fun z : UnitQuadric ↦ h.toFun (project z)) h.smooth
  obtain ⟨D, hD, hDK, hDphase, hdec, hstationary⟩ := exists_smooth_descent hG hagree
  obtain ⟨ℓ, hℓ⟩ := critical_chart h hf
  let DK : UnitQuadric → UnitQuadric := fun z ↦ ⟨D z, hDK z⟩
  have hDKcont : Continuous DK := (hD.continuous.comp continuous_subtype_val).subtype_mk _
  let fK : UnitQuadric → ℝ := fun z ↦ G z
  let ℓK : UnitQuadric → ℂ := fun z ↦ ℓ z
  let s : Finset ℝ := hf.toFinset.image h.toFun
  obtain ⟨zmax, _, hzmax⟩ := isCompact_univ.exists_isMaxOn (Set.univ_nonempty :
    (Set.univ : Set UnitQuadric).Nonempty) (hG.continuous.comp continuous_subtype_val).continuousOn
  obtain ⟨T, hTcard, hT⟩ := critical_level_cover hDKcont
    (hG.continuous.comp continuous_subtype_val) (ℓ.continuous.comp continuous_subtype_val)
    hdec (fun z hz ↦ lt_of_le_of_ne (hdec z) (fun heq ↦ hℓ z (hstationary z heq) hz))
    s (G zmax) (fun z _ heq ↦ by
      apply Finset.mem_image.mpr
      exact ⟨project z, hf.mem_toFinset.mpr (hstationary z heq), (hagree z).symm⟩)
  have hcard : T.card ≤ 3 := by
    have hfcard : hf.toFinset.card ≤ 3 := by
      have hh := hsmall
      rw [hf.encard_eq_coe_toFinset_card] at hh
      exact_mod_cast hh
    exact hTcard.trans (Finset.card_image_le.trans hfcard)
  let e : T ↪ Fin 3 := T.equivFin.toEmbedding.trans (Fin.castLEEmb hcard)
  let F : CV → CSpace 3 := fun z ↦ Function.extend e (fun n : T ↦ ℓ (D^[n.val] z)) 0
  have hiterate (n : ℕ) (z : UnitQuadric) : ((DK^[n] z : UnitQuadric) : CV) = D^[n] z := by
    induction n with
    | zero => rfl
    | succ n hn => simp only [Function.iterate_succ_apply']; exact congrArg D hn
  refine ⟨F, contDiff_pi.mpr (fun i ↦ ?_), ?_, ?_⟩
  · by_cases hi : ∃ n : T, e n = i
    · obtain ⟨n, rfl⟩ := hi
      simp only [F, e.injective.extend_apply]
      exact (ℓ.restrictScalars ℝ).contDiff.comp (contDiff_iterate hD n.val)
    · simp only [F, Function.extend_apply' _ _ _ hi, Pi.zero_apply]
      exact contDiff_const
  · intro z hz
    obtain ⟨n, hn, hnz⟩ := hT z (hzmax (Set.mem_univ z))
    have hcoord := congrFun hz (e ⟨n, hn⟩)
    simp only [F, e.injective.extend_apply, Pi.zero_apply] at hcoord
    change ℓ ((DK^[n] z : UnitQuadric) : CV) ≠ 0 at hnz
    rw [hiterate] at hnz
    exact hnz hcoord
  · intro z a ha
    ext i
    by_cases hi : ∃ n : T, e n = i
    · obtain ⟨n, rfl⟩ := hi
      simp only [F, e.injective.extend_apply, Pi.smul_apply,
        iterate_phase hDK hDphase n.val z a ha, map_smul]
    · simp only [F, Function.extend_apply' _ _ _ hi, Pi.zero_apply, Pi.smul_apply, smul_zero]

/-- Normalization has a globally smooth ambient extension, even away from K.
The positive complement bump prevents spurious singularities off K. -/
theorem normalize_cover_map {F : CV → CSpace 3} (hF : ContDiff ℝ ∞ F)
    (hne : ∀ z : UnitQuadric, F z ≠ 0)
    (hphase : ∀ z : UnitQuadric, ∀ a : ℂ, Complex.normSq a = 1 → F (a • (z : CV)) = a • F z) :
    ∃ F' : CV → CSpace 3, ContDiff ℝ ∞ F' ∧
      (∀ z : UnitQuadric, normSq 3 (F' z) = 1) ∧
      (∀ z : UnitQuadric, ∀ a : ℂ, Complex.normSq a = 1 → F' (a • (z : CV)) = a • F' z) := by
  obtain ⟨δ, hδsupp, hδ, hδrange⟩ := isClosed_unitQuadric.isOpen_compl.exists_contDiff_support_eq (n := ⊤)
  have hδzero (z : UnitQuadric) : δ z = 0 := by
    by_contra hne
    have hz : ↑z ∈ Function.support δ := hne
    rw [hδsupp] at hz
    exact hz z.property
  let S : CV → ℝ := fun z ↦ normSq 3 (F z) + δ z
  have hS : ContDiff ℝ ∞ S := ((normSq_contDiff 3).comp hF).add hδ
  have hpos (z : CV) : 0 < S z := by
    by_cases hz : IsUnitQuadric z
    · have hn : normSq 3 (F z) ≠ 0 := fun hn ↦ hne ⟨z, hz⟩ ((normSq_eq_zero_iff _ _).mp hn)
      have hp := lt_of_le_of_ne (normSq_nonneg 3 (F z)) hn.symm
      change 0 < normSq 3 (F z) + δ z
      exact add_pos_of_pos_of_nonneg hp (hδrange ⟨z, rfl⟩).1
    · have hd : δ z ≠ 0 := by
        change z ∈ Function.support δ
        rw [hδsupp]
        exact hz
      exact add_pos_of_nonneg_of_pos (normSq_nonneg 3 (F z))
        (lt_of_le_of_ne (hδrange ⟨z, rfl⟩).1 hd.symm)
  let F' : CV → CSpace 3 := fun z ↦ (Real.sqrt (S z))⁻¹ • F z
  refine ⟨F', ((hS.sqrt (fun z ↦ (hpos z).ne')).inv (fun z ↦
    (Real.sqrt_pos.2 (hpos z)).ne')).smul hF, ?_, ?_⟩
  · intro z
    change normSq 3 ((Real.sqrt (S z))⁻¹ • F z) = 1
    have hss : S z = normSq 3 (F z) := by simp only [S, hδzero z, add_zero]
    change normSq 3 (((Real.sqrt (S z))⁻¹ : ℝ) • F z) = 1
    change normSq 3 ((((Real.sqrt (S z))⁻¹ : ℝ) : ℂ) • F z) = 1
    rw [normSq_smul, Complex.normSq_ofReal, ← pow_two,
      inv_pow, Real.sq_sqrt (hpos z).le, hss]
    exact inv_mul_cancel₀ (by simpa only [← hss] using (hpos z).ne')
  · intro z a ha
    have hs : S (a • (z : CV)) = S z := by
      simp only [S, hδzero ⟨_, unit_phase z a ha⟩, hδzero z, add_zero, hphase z a ha,
        normSq_smul, ha, one_mul]
    dsimp only [F']
    rw [hs, hphase z a ha]
    exact smul_comm _ _ _

end ArnoldCounterexample.CriticalBound

end

end OAI
