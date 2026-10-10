import Mathlib

namespace OAI

noncomputable section

section
open Set Metric Filter TopologicalSpace MeasureTheory Function
open scoped Classical BigOperators Topology Cardinal ENNReal NNReal

namespace SeparableQuotient.Positive.Fields.ComplexTransfer
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]



def complexOfInvariant (R : Submodule ℝ V)
    (hI : ∀ x ∈ R, Complex.I • x ∈ R) : Submodule ℂ V where
  carrier := R
  zero_mem' := R.zero_mem
  add_mem' := R.add_mem
  smul_mem' z x hx := by
    rw [← Complex.re_add_im z, add_smul, mul_smul]
    have hre : (z.re : ℂ) • x = z.re • x := algebraMap_smul ℂ z.re x
    have him : (z.im : ℂ) • (Complex.I • x) = z.im • (Complex.I • x) :=
      algebraMap_smul ℂ z.im (Complex.I • x)
    rw [hre, him]
    exact R.add_mem (R.smul_mem z.re hx) (R.smul_mem z.im (hI x hx))

def complexSum (W : Submodule ℝ V) : W × W →L[ℝ] V :=
  W.subtypeL.comp (ContinuousLinearMap.fst ℝ W W) +
    Complex.I • W.subtypeL.comp (ContinuousLinearMap.snd ℝ W W)

@[simp] lemma complexSum_apply (W : Submodule ℝ V) (p : W × W) :
    complexSum W p = (p.1 : V) + Complex.I • (p.2 : V) := rfl

lemma complexSum_range_invariant (W : Submodule ℝ V) :
    ∀ x ∈ (complexSum W).range, Complex.I • x ∈ (complexSum W).range := by
  rintro _ ⟨⟨u, v⟩, rfl⟩
  refine ⟨(-v, u), ?_⟩
  simp [complexSum_apply, smul_add, smul_smul, Complex.I_mul_I, add_comm]




def SeparatedFromMultiplication (E W : Submodule ℝ V) (C : ℝ) : Prop :=
  ∀ w : W, ∀ e : E, ‖w‖ ≤ C * ‖Complex.I • (w : V) - (e : V)‖

lemma complexSum_bound (E W : Submodule ℝ V) (hWE : W ≤ E)
    {C : ℝ} (_hC : 0 ≤ C) (hsep : SeparatedFromMultiplication E W C)
    (p : W × W) : ‖p‖ ≤ (1 + C) * ‖complexSum W p‖ := by
  have hv : ‖p.2‖ ≤ C * ‖complexSum W p‖ := by
    simpa [complexSum_apply, sub_neg_eq_add, add_comm] using
      hsep p.2 ⟨-(p.1 : V), E.neg_mem (hWE p.1.property)⟩
  have hu : ‖p.1‖ ≤ (1 + C) * ‖complexSum W p‖ := by
    have hid : (p.1 : V) = complexSum W p - Complex.I • (p.2 : V) := by
      simp [complexSum_apply]
    calc
      ‖p.1‖ = ‖complexSum W p - Complex.I • (p.2 : V)‖ := congrArg norm hid
      _ ≤ ‖complexSum W p‖ + ‖Complex.I • (p.2 : V)‖ := norm_sub_le _ _
      _ = ‖complexSum W p‖ + ‖p.2‖ := by simp [norm_smul]
      _ ≤ ‖complexSum W p‖ + C * ‖complexSum W p‖ := add_le_add_right hv _
      _ = (1 + C) * ‖complexSum W p‖ := by ring
  rw [Prod.norm_def]
  exact max_le hu (hv.trans (by nlinarith [norm_nonneg (complexSum W p)]))



theorem complex_subspace_of_separated [CompleteSpace V]
    (E W : Submodule ℝ V) (hWE : W ≤ E)
    (hWclosed : IsClosed (W : Set V)) (hWinf : ¬ FiniteDimensional ℝ W)
    {C : ℝ} (hC : 0 ≤ C) (hsep : SeparatedFromMultiplication E W C) :
    ∃ H : Submodule ℂ V, IsClosed (H : Set V) ∧ ¬ FiniteDimensional ℂ H ∧
      ∃ P Q : H →L[ℝ] E, ∀ h : H,
        (h : V) = (P h : V) + Complex.I • (Q h : V) := by
  let : IsClosed (W : Set V) := hWclosed
  let B := complexSum W
  have hB : AntilipschitzWith ⟨1 + C, by positivity⟩ B :=
    B.antilipschitz_of_bound (complexSum_bound E W hWE hC hsep)
  have hBclosed : IsClosed (Set.range B) :=
    (hB.isClosedEmbedding B.uniformContinuous).isClosed_range
  let H := complexOfInvariant B.range (complexSum_range_invariant W)
  have hHclosed : IsClosed (H : Set V) := hBclosed
  let : IsClosed (H : Set V) := hHclosed
  let J : W × W →L[ℝ] H := B.codRestrict (H.restrictScalars ℝ)
    (fun p => ⟨p, rfl⟩)
  have hJinj : Function.Injective J := by
    intro p q heq
    exact hB.injective (congrArg Subtype.val heq)
  have hJsurj : Function.Surjective J := by
    intro h
    obtain ⟨p, hp⟩ := h.property
    exact ⟨p, Subtype.ext hp⟩
  let e : (W × W) ≃L[ℝ] H := ContinuousLinearEquiv.ofBijective J
    (LinearMap.ker_eq_bot.mpr hJinj) (LinearMap.range_eq_top.mpr hJsurj)
  have hHinf : ¬ FiniteDimensional ℂ H := by
    intro hd
    let := hd
    let : FiniteDimensional ℝ H := FiniteDimensional.trans ℝ ℂ H
    let j : W →ₗ[ℝ] H := e.toLinearMap.comp (LinearMap.inl ℝ W W)
    apply hWinf
    apply FiniteDimensional.of_injective (V₂ := H) j
    exact e.injective.comp (fun u v h => congrArg Prod.fst h)
  let L : W →L[ℝ] E := W.subtypeL.codRestrict E (fun w => hWE w.property)
  let P : H →L[ℝ] E := (L.comp (ContinuousLinearMap.fst ℝ W W)).comp e.symm.toContinuousLinearMap
  let Q : H →L[ℝ] E := (L.comp (ContinuousLinearMap.snd ℝ W W)).comp e.symm.toContinuousLinearMap
  refine ⟨H, hHclosed, hHinf, P, Q, fun h => ?_⟩
  exact (congrArg Subtype.val (e.apply_symm_apply h)).symm

end SeparableQuotient.Positive.Fields.ComplexTransfer

end

section
open Set Metric Filter TopologicalSpace MeasureTheory Function
open scoped Classical BigOperators Topology Cardinal ENNReal NNReal

namespace SeparableQuotient.Positive.Fields.ComplexTransfer
open Set
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]

def HasSeparatedInfiniteSubspace (E : Submodule ℝ V) : Prop :=
  ∃ W : Submodule ℝ V, W ≤ E ∧ IsClosed (W : Set V) ∧
    ¬ FiniteDimensional ℝ W ∧ ∃ C : ℝ, 0 ≤ C ∧ SeparatedFromMultiplication E W C




theorem exists_near_rotation_of_not_separated
    (E : Submodule ℝ V) (hE : ¬ HasSeparatedInfiniteSubspace E)
    (M : Submodule ℝ V) (hME : M ≤ E) (hMclosed : IsClosed (M : Set V))
    (hMinf : ¬ FiniteDimensional ℝ M) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : M, ‖f‖ = 1 ∧ ∃ g : E, ‖(g : V) - Complex.I • (f : V)‖ < ε := by
  have hnot : ¬ SeparatedFromMultiplication E M ε⁻¹ :=
    fun hh => hE ⟨M, hME, hMclosed, hMinf, ε⁻¹, inv_nonneg.mpr hε.le, hh⟩
  simp only [SeparatedFromMultiplication, not_forall, not_le] at hnot
  obtain ⟨f, g, hfg⟩ := hnot
  have hfpos : 0 < ‖f‖ := lt_of_le_of_lt (mul_nonneg (inv_nonneg.mpr hε.le)
    (norm_nonneg _)) hfg
  let u : M := ‖f‖⁻¹ • f
  let v : E := ‖f‖⁻¹ • g
  have hu : ‖u‖ = 1 := by
    change ‖‖f‖⁻¹ • f‖ = 1
    exact norm_smul_inv_norm (norm_pos_iff.mp hfpos)
  have herr : ‖(g : V) - Complex.I • (f : V)‖ < ε * ‖f‖ := by
    have hh := (mul_lt_mul_iff_of_pos_left hε).mpr hfg
    simpa only [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hε), one_mul, norm_sub_rev] using hh
  refine ⟨u, hu, v, ?_⟩
  have heq : (v : V) - Complex.I • (u : V) =
      ‖f‖⁻¹ • ((g : V) - Complex.I • (f : V)) := by
    simp only [u, v, Submodule.coe_smul, smul_sub]
    rw [smul_comm Complex.I (‖f‖⁻¹)]
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hfpos)]
  calc
    ‖f‖⁻¹ * ‖(g : V) - Complex.I • (f : V)‖ < ‖f‖⁻¹ * (ε * ‖f‖) :=
      (mul_lt_mul_iff_of_pos_left (inv_pos.mpr hfpos)).mpr herr
    _ = ε := by field_simp

end SeparableQuotient.Positive.Fields.ComplexTransfer

end

end

end OAI
