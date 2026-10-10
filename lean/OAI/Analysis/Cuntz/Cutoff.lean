import OAI.Analysis.Cuntz.State
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric

namespace OAI

noncomputable section

/-! Functional calculus cutoffs and perturbation comparison. -/

open scoped Matrix CStarAlgebra Topology

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

/-- The genuine continuous spectral cutoff (a-ε)₊. -/
def cuntzCutoff (a : A) (ε : ℝ) : A := cfc (fun t : ℝ => max (t-ε) 0) a

theorem cuntzCutoff_nonneg (a : A) (ε : ℝ) : 0 ≤ cuntzCutoff a ε :=
  cfc_nonneg fun _ _ => le_max_right _ _

theorem cuntzCutoff_le {a : A} (ha : 0 ≤ a) {ε : ℝ} (hε : 0 ≤ ε) :
    cuntzCutoff a ε ≤ a := by
  have h : cfc (fun t : ℝ => max (t-ε) 0) a ≤ cfc (fun t : ℝ => t) a :=
    cfc_mono fun t ht => max_le (sub_le_self t hε) (spectrum_nonneg_of_nonneg ha ht)
  simpa only [cuntzCutoff, cfc_id' ℝ a ha.isSelfAdjoint] using h

theorem cuntzCutoff_antitone (a : A) : Antitone (cuntzCutoff a) := by
  intro ε δ h
  exact cfc_mono fun _ _ => max_le_max_right 0 (sub_le_sub_left h _)

/-- Uniform norm control, with the actual C*-norm. -/
theorem norm_sub_cuntzCutoff_le {a : A} (ha : 0 ≤ a) {ε : ℝ} (hε : 0 ≤ ε) :
    ‖a - cuntzCutoff a ε‖ ≤ ε := by
  have he : cfc (fun t : ℝ => t - max (t-ε) 0) a = a - cuntzCutoff a ε := by
    rw [cfc_sub (fun t : ℝ => t) (fun t => max (t-ε) 0) a,
      cfc_id' ℝ a ha.isSelfAdjoint]
    rfl
  rw [← he]
  apply norm_cfc_le hε
  intro t ht
  have ht0 := spectrum_nonneg_of_nonneg ha ht
  rcases le_total ε t with h | h
  · rw [max_eq_left (sub_nonneg.mpr h), sub_sub_cancel, Real.norm_of_nonneg hε]
  · rw [max_eq_right (sub_nonpos.mpr h), sub_zero, Real.norm_of_nonneg ht0]
    exact h

/-- Norm comparison of positives is detected by all strictly positive
spectral cutoffs. This does not assume continuity of a dimension state. -/
theorem cuntzLE_iff_all_cutoffs {n m : ℕ}
    (a : CStarMatrix (Fin n) (Fin n) A) (ha : 0 ≤ a)
    (b : CStarMatrix (Fin m) (Fin m) A) :
    CuntzLE (CStarMatrix.ofMatrix.symm a) (CStarMatrix.ofMatrix.symm b) ↔
      ∀ ε : ℝ, 0 < ε → CuntzLE (CStarMatrix.ofMatrix.symm (cuntzCutoff a ε))
        (CStarMatrix.ofMatrix.symm b) := by
  constructor
  · intro h ε hε
    exact (cuntzLE_of_nonneg_le (cuntzCutoff_nonneg a ε) (cuntzCutoff_le ha hε.le)).trans h
  · intro h
    apply (CuntzLE.iff_approx _ _).mpr
    intro ε hε
    obtain ⟨v, hv⟩ := (CuntzLE.iff_approx _ _).mp (h (ε/2) (half_pos hε)) (ε/2) (half_pos hε)
    refine ⟨v, ?_⟩
    let q : CStarMatrix (Fin n) (Fin n) A := CStarMatrix.ofMatrix
      (v * CStarMatrix.ofMatrix.symm b * v.conjTranspose)
    change ‖a - q‖ < ε
    have hv' : ‖cuntzCutoff a (ε/2) - q‖ < ε/2 := hv
    calc
      ‖a - q‖ ≤ ‖a - cuntzCutoff a (ε/2)‖ + ‖cuntzCutoff a (ε/2) - q‖ := by
        simpa only [dist_eq_norm] using dist_triangle a (cuntzCutoff a (ε/2)) q
      _ ≤ ε/2 + ‖cuntzCutoff a (ε/2) - q‖ := by
        have hn := norm_sub_cuntzCutoff_le ha (half_pos hε).le
        linarith
      _ < ε := by linarith

/-- The cutoff remains an actual positive matrix of the same finite size. -/
def CuntzPositiveMatrix.cutoff (a : CuntzPositiveMatrix A) (ε : ℝ) : CuntzPositiveMatrix A :=
  ⟨a.size, CStarMatrix.ofMatrix.symm (cuntzCutoff (CStarMatrix.ofMatrix a.matrix) ε),
    cuntzCutoff_nonneg _ _⟩

theorem CuntzDimensionState.cutoff_value_antitone (d : CuntzDimensionState A)
    (a : CuntzPositiveMatrix A) : Antitone (fun ε => d.value (a.cutoff ε)) := by
  intro ε δ h
  exact d.value_mono (cuntzLE_of_nonneg_le (cuntzCutoff_nonneg _ _) (cuntzCutoff_antitone _ h))

theorem CuntzDimensionState.cutoff_value_le (d : CuntzDimensionState A)
    (a : CuntzPositiveMatrix A) {ε : ℝ} (hε : 0 ≤ ε) : d.value (a.cutoff ε) ≤ d.value a :=
  d.value_mono (cuntzLE_of_nonneg_le (cuntzCutoff_nonneg _ _) (cuntzCutoff_le a.nonneg hε))


/-- Positive scalar multiplication is implemented by scalar conjugation. -/
theorem cuntzLE_smul {n : ℕ} (a : CStarMatrix (Fin n) (Fin n) A)
    {r : ℝ} (hr : 0 ≤ r) :
    CuntzLE (CStarMatrix.ofMatrix.symm (r • a)) (CStarMatrix.ofMatrix.symm a) := by
  let v : CStarMatrix (Fin n) (Fin n) A := Real.sqrt r • 1
  have h : v * a * star v = r • a := by
    simp only [v, star_smul, star_trivial, star_one, smul_mul_assoc, one_mul,
      mul_smul_comm, mul_one, smul_smul, Real.mul_self_sqrt hr]
  have h' := CuntzLE.exact (CStarMatrix.ofMatrix.symm a) (CStarMatrix.ofMatrix.symm v)
  change CuntzLE (CStarMatrix.ofMatrix.symm (v * a * star v)) _ at h'
  rwa [h] at h'

theorem cuntzEquivalent_pos_smul {n : ℕ} (a : CStarMatrix (Fin n) (Fin n) A)
    {r : ℝ} (hr : 0 < r) :
    CuntzEquivalent (CStarMatrix.ofMatrix.symm (r • a)) (CStarMatrix.ofMatrix.symm a) := by
  refine ⟨cuntzLE_smul a hr.le, ?_⟩
  simpa only [smul_smul, inv_mul_cancel₀ hr.ne', one_smul] using
    cuntzLE_smul (r • a) (inv_nonneg.mpr hr.le)


/-- A cutoff square root localized above ε. The inequality is scalar
functional calculus in a single self-adjoint element. -/
theorem exists_cutoff_localizer {a : A} (ha : 0 ≤ a) (ε : ℝ) :
    ∃ x : A, star x = x ∧ x*x = cuntzCutoff a ε ∧
      ε • cuntzCutoff a ε ≤ x*a*x := by
  let f : ℝ → ℝ := fun t => Real.sqrt (max (t-ε) 0)
  let x := cfc f a
  have hx : star x = x := (cfc_nonneg (f := f) (a := a)
    (fun t _ => Real.sqrt_nonneg _) : 0 ≤ x).isSelfAdjoint.star_eq
  have hsq : x*x = cuntzCutoff a ε := by
    rw [← cfc_mul f f a]
    exact cfc_congr fun t _ => Real.mul_self_sqrt (le_max_right _ _)
  refine ⟨x, hx, hsq, ?_⟩
  have hid := cfc_id' ℝ a ha.isSelfAdjoint
  change ε • cfc (fun t : ℝ => max (t-ε) 0) a ≤ cfc f a * a * cfc f a
  have he : cfc (fun t => f t * t * f t) a = cfc f a * a * cfc f a := by
    rw [cfc_mul (fun t => f t * t) f a, cfc_mul f (fun t : ℝ => t) a, hid]
  rw [← he, ← cfc_const_mul ε (fun t : ℝ => max (t-ε) 0) a]
  refine cfc_mono (hf := by fun_prop) (hg := by dsimp [f]; fun_prop) ?_
  intro t ht
  have he : f t * t * f t = t * max (t-ε) 0 := by
    calc
      f t * t * f t = t * (f t * f t) := by ring
      _ = t * max (t-ε) 0 := by rw [show f t * f t = max (t-ε) 0 from Real.mul_self_sqrt (le_max_right _ _)]
  rw [he]
  rcases le_total t ε with h | h
  · rw [max_eq_right (sub_nonpos.mpr h)]; simp
  · exact mul_le_mul_of_nonneg_right h (le_max_right _ _)

/-- A strict norm perturbation gives cutoff Cuntz comparison.
No operator monotonicity of the positive-part function is used. -/
theorem cuntzLE_cutoff_of_norm_sub_lt {n : ℕ}
    {a b : CStarMatrix (Fin n) (Fin n) A} (ha : 0 ≤ a) (hb : IsSelfAdjoint b)
    {ε : ℝ} (h : ‖a-b‖ < ε) :
    CuntzLE (CStarMatrix.ofMatrix.symm (cuntzCutoff a ε))
      (CStarMatrix.ofMatrix.symm b) := by
  let δ := ‖a-b‖
  have hδ : 0 < ε-δ := sub_pos.mpr h
  have hab : a ≤ b + δ • 1 := by
    have he := (ha.isSelfAdjoint.sub hb).le_algebraMap_norm_self
    rw [Algebra.algebraMap_eq_smul_one] at he
    exact sub_le_iff_le_add'.mp he
  obtain ⟨x, hx, hsq, hloc⟩ := exists_cutoff_localizer ha ε
  have hc := star_left_conjugate_le_conjugate hab x
  simp only [hx, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, hsq] at hc
  have hbound : (ε-δ) • cuntzCutoff a ε ≤ x*b*x := by
    rw [sub_smul]
    exact sub_le_iff_le_add.mpr (hloc.trans hc)
  have hpos : 0 ≤ (ε-δ) • cuntzCutoff a ε := smul_nonneg hδ.le (cuntzCutoff_nonneg a ε)
  have hcmp := cuntzLE_of_nonneg_le hpos hbound
  have hsc := cuntzEquivalent_pos_smul (cuntzCutoff a ε) hδ
  have hex := CuntzLE.exact (CStarMatrix.ofMatrix.symm b) (CStarMatrix.ofMatrix.symm x)
  change CuntzLE (CStarMatrix.ofMatrix.symm (x*b*star x)) _ at hex
  rw [hx] at hex
  exact hsc.2.trans (hcmp.trans hex)


/-- Every positive cutoff of a Cuntz-smaller matrix is already below a
strictly positive cutoff of the larger matrix, including unequal sizes. -/
theorem CuntzLE.exists_cutoff {n m : ℕ}
    {a : CStarMatrix (Fin n) (Fin n) A} {b : CStarMatrix (Fin m) (Fin m) A}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : CuntzLE (CStarMatrix.ofMatrix.symm a) (CStarMatrix.ofMatrix.symm b))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ CuntzLE (CStarMatrix.ofMatrix.symm (cuntzCutoff a ε))
      (CStarMatrix.ofMatrix.symm (cuntzCutoff b δ)) := by
  obtain ⟨v, hv⟩ := (CuntzLE.iff_approx _ _).mp h (ε/2) (half_pos hε)
  let g : CStarMatrix (Fin m) (Fin m) A → CStarMatrix (Fin n) (Fin n) A :=
    fun y => CStarMatrix.ofMatrix (v * CStarMatrix.ofMatrix.symm y * v.conjTranspose)
  have hg : Continuous g :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  obtain ⟨η, hη, hclose⟩ := Metric.continuousAt_iff.mp hg.continuousAt (ε/2) (half_pos hε)
  let δ := η/2
  have hδ : 0 < δ := half_pos hη
  have hdist : dist (cuntzCutoff b δ) b < η := by
    rw [dist_eq_norm, norm_sub_rev]
    exact (norm_sub_cuntzCutoff_le hb hδ.le).trans_lt (half_lt_self hη)
  have hgb : ‖g (cuntzCutoff b δ) - g b‖ < ε/2 := by
    simpa only [dist_eq_norm] using hclose hdist
  have hab : ‖a - g (cuntzCutoff b δ)‖ < ε := by
    have hv' : ‖a - g b‖ < ε/2 := hv
    have ht : ‖a - g (cuntzCutoff b δ)‖ ≤ ‖a - g b‖ + ‖g b - g (cuntzCutoff b δ)‖ := by
      simpa only [dist_eq_norm] using dist_triangle a (g b) (g (cuntzCutoff b δ))
    rw [norm_sub_rev (g b)] at ht
    linarith
  have hsa : IsSelfAdjoint (g (cuntzCutoff b δ)) := by
    have hs : (CStarMatrix.ofMatrix.symm (cuntzCutoff b δ)).conjTranspose =
        CStarMatrix.ofMatrix.symm (cuntzCutoff b δ) :=
      (cuntzCutoff_nonneg b δ).isSelfAdjoint.star_eq
    change (v * CStarMatrix.ofMatrix.symm (cuntzCutoff b δ) * v.conjTranspose).conjTranspose =
      v * CStarMatrix.ofMatrix.symm (cuntzCutoff b δ) * v.conjTranspose
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hs, Matrix.mul_assoc]
  refine ⟨δ, hδ, (cuntzLE_cutoff_of_norm_sub_lt ha hsa hab).trans ?_⟩
  exact CuntzLE.exact _ v

/-- The cutoff quantifiers characterize the original norm-closure relation. -/
theorem cuntzLE_iff_cutoff_comparison (a b : CuntzPositiveMatrix A) :
    CuntzLE a.matrix b.matrix ↔ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      CuntzLE (a.cutoff ε).matrix (b.cutoff δ).matrix := by
  constructor
  · intro h ε hε
    exact h.exists_cutoff a.nonneg b.nonneg hε
  · intro h
    apply (cuntzLE_iff_all_cutoffs (CStarMatrix.ofMatrix a.matrix) a.nonneg
      (CStarMatrix.ofMatrix b.matrix)).mpr
    intro ε hε
    obtain ⟨δ, hδ, hc⟩ := h ε hε
    exact hc.trans (cuntzLE_of_nonneg_le (cuntzCutoff_nonneg _ _) (cuntzCutoff_le b.nonneg hδ.le))

end Kaplansky

end

end OAI
