import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Topology.Order.IntermediateValue

namespace OAI

/-!
# Positivity along an invertible self-adjoint path

The resolvent path in manuscript Lemma `q:noncommuting` starts at the
identity and is self-adjoint and invertible throughout a real interval.
Its positivity follows from continuity of the least Rayleigh quotient.
The argument is carried out in finite dimension.
-/

open Filter

namespace TwoPointCorrelations

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [Nontrivial E]

noncomputable def leastRayleigh (T : E →L[ℂ] E) : ℝ :=
  ⨅ x : {x : E // x ≠ 0}, T.rayleighQuotient x

omit [Nontrivial E] in
lemma rayleigh_bddBelow (T : E →L[ℂ] E) :
    BddBelow (Set.range fun x : {x : E // x ≠ 0} => T.rayleighQuotient x) := by
  refine ⟨-‖T‖, ?_⟩
  rintro y ⟨x, rfl⟩
  exact (abs_le.mp (T.rayleighQuotient_le_norm x)).1

omit [Nontrivial E] in
lemma leastRayleigh_le (T : E →L[ℂ] E) (x : E) (hx : x ≠ 0) :
    leastRayleigh T ≤ T.rayleighQuotient x :=
  ciInf_le (rayleigh_bddBelow T) ⟨x, hx⟩

lemma leastRayleigh_le_add_norm (T S : E →L[ℂ] E) :
    leastRayleigh T ≤ leastRayleigh S + ‖T - S‖ := by
  let : Nonempty {x : E // x ≠ 0} := ⟨⟨Classical.choose (exists_ne (0 : E)),
    Classical.choose_spec (exists_ne (0 : E))⟩⟩
  have hpoint (x : {x : E // x ≠ 0}) :
      leastRayleigh T - ‖T - S‖ ≤ S.rayleighQuotient x := by
    have ht := leastRayleigh_le T x x.property
    have hb := (abs_le.mp ((T - S).rayleighQuotient_le_norm x)).2
    have heq : (T - S).rayleighQuotient x =
        T.rayleighQuotient x - S.rayleighQuotient x := by
      simp [sub_eq_add_neg, ContinuousLinearMap.rayleighQuotient_add]
    rw [heq] at hb
    linarith
  have hi : leastRayleigh T - ‖T - S‖ ≤ leastRayleigh S := le_ciInf hpoint
  linarith

lemma leastRayleigh_lipschitz : LipschitzWith 1 (leastRayleigh (E := E)) := by
  apply LipschitzWith.of_dist_le_mul
  intro T S
  have hTS := leastRayleigh_le_add_norm T S
  have hST := leastRayleigh_le_add_norm S T
  rw [norm_sub_rev S T] at hST
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

@[simp] lemma leastRayleigh_id : leastRayleigh (ContinuousLinearMap.id ℂ E) = 1 := by
  let : Nonempty {x : E // x ≠ 0} := ⟨⟨Classical.choose (exists_ne (0 : E)),
    Classical.choose_spec (exists_ne (0 : E))⟩⟩
  have hpoint (x : {x : E // x ≠ 0}) :
      (ContinuousLinearMap.id ℂ E).rayleighQuotient x = 1 := by
    have hn : ‖(x : E)‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr x.property)
    simp only [ContinuousLinearMap.rayleighQuotient,
      ContinuousLinearMap.reApplyInnerSelf_apply, ContinuousLinearMap.id_apply,
      inner_self_eq_norm_sq_to_K]
    norm_cast
    exact div_self hn
  simp [leastRayleigh, hpoint]

lemma leastRayleigh_ne_zero [FiniteDimensional ℂ E] (T : E →L[ℂ] E)
    (hself : T.IsSymmetric) (hinj : Function.Injective T) : leastRayleigh T ≠ 0 := by
  intro hz
  have heig := hself.hasEigenvalue_iInf_of_finiteDimensional
  change Module.End.HasEigenvalue (T : E →ₗ[ℂ] E) (leastRayleigh T : ℂ) at heig
  rw [hz, Complex.ofReal_zero] at heig
  obtain ⟨x, hx, hxne⟩ := heig.exists_hasEigenvector
  rw [Module.End.mem_eigenspace_iff] at hx
  have hzero : T x = T 0 := by simpa using hx
  exact hxne (hinj hzero)

/-- A finite-dimensional continuous self-adjoint path that starts at the
identity and remains injective has strictly positive quadratic form. -/
theorem selfAdjoint_path_positive [FiniteDimensional ℂ E]
    (F : ℝ → E →L[ℂ] E) (a b : ℝ) (hab : a ≤ b)
    (hcont : ContinuousOn F (Set.Icc a b)) (hstart : F a = ContinuousLinearMap.id ℂ E)
    (hself : ∀ t ∈ Set.Icc a b, (F t).IsSymmetric)
    (hinj : ∀ t ∈ Set.Icc a b, Function.Injective (F t)) :
    ∀ x : E, x ≠ 0 → 0 < (inner ℂ (F b x) x).re := by
  have hc : ContinuousOn (fun t => leastRayleigh (F t)) (Set.Icc a b) :=
    leastRayleigh_lipschitz.continuous.comp_continuousOn hcont
  have hstart' : leastRayleigh (F a) = 1 := by rw [hstart, leastRayleigh_id]
  have hend : 0 < leastRayleigh (F b) := by
    by_contra! hn
    obtain ⟨t, ht, heq⟩ := intermediate_value_Icc' hab hc
      (show (0 : ℝ) ∈ Set.Icc (leastRayleigh (F b)) (leastRayleigh (F a)) by
        exact ⟨hn, by rw [hstart']; norm_num⟩)
    exact leastRayleigh_ne_zero (F t) (hself t ht) (hinj t ht) heq
  intro x hx
  have hr : 0 < (F b).rayleighQuotient x := hend.trans_le (leastRayleigh_le (F b) x hx)
  have hn : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  exact (div_pos_iff_of_pos_right hn).mp hr

end TwoPointCorrelations

end OAI
