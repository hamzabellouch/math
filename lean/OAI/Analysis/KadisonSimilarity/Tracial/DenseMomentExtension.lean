import OAI.Analysis.KadisonSimilarity.Tracial.TraceDenseContractions
import OAI.Analysis.KadisonSimilarity.Tracial.IntegerMomentScaling
import OAI.Analysis.KadisonSimilarity.Tracial.TracialInputTransport

namespace OAI

/-! Extension of mixed moments from trace-dense contractions to all contractions. -/

noncomputable section
namespace KadisonSimilarity
open BoundedHochschild HochschildRigidity HochschildPatching HochschildUltrapower Filter Topology
open scoped ComplexOrder

variable {B C I : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  (τ : B →ₚ[ℂ] ℂ) (σ : C →ₚ[ℂ] ℂ) (hσ : σ 1 = 1)
  (trσ : ∀ a b, σ (a * b) = σ (b * a))
  (φ : B →⋆ₐ[ℂ] C) (hφ : ∀ b, σ (φ b) = τ b)

include hφ in
lemma gnsTendsto_tracePreserving {f : ℕ → B} {b : B}
    (h : GNSTendsto τ f atTop b) :
    GNSTendsto σ (fun j => φ (f j)) atTop (φ b) := by
  simpa only [GNSTendsto, ← map_sub φ, preGNS_norm_map_eq τ σ φ hφ] using h

include hσ in
lemma norm_centered_contraction (c : C) (hc : ‖c‖ ≤ 1) :
    ‖c - σ c • 1‖ ≤ 2 := by
  have h := norm_centered_half σ hσ c hc
  rw [norm_smul] at h
  norm_num at h
  linarith

include hσ trσ hφ in
/-- No norm separability is required. The approximating family is dense only
in the trace norm on the unit ball. -/
theorem integer_moments_of_trace_dense
    (d : ℕ → B) (hd : ∀ n, ‖d n‖ ≤ 1)
    (hdense : ∀ b : B, ‖b‖ ≤ 1 → ∃ j : ℕ → ℕ,
      GNSTendsto τ (fun k => d (j k)) atTop b)
    (u : unitary C)
    (hm : ∀ a : Option ℕ, ∀ l : List (IntAtom ℕ), admissibleIntTail l →
      (∀ b ∈ l, b.1 ≠ 0) →
      σ (integerEval (fun n => φ (d n) - σ (φ (d n)) • 1) u a l) = 0)
    (A : I → B) (hA : ∀ i, ‖A i‖ ≤ 1)
    (a : Option I) (l : List (IntAtom I)) (hl : admissibleIntTail l)
    (hk : ∀ b ∈ l, b.1 ≠ 0) :
    σ (integerEval (fun i => φ (A i) - σ (φ (A i)) • 1) u a l) = 0 := by
  classical
  choose j hj using fun i => hdense (A i) (hA i)
  let F : ℕ → I → C := fun n i => φ (d (j i n)) - σ (φ (d (j i n))) • 1
  apply integer_moment_zero_of_bounded_limits σ hσ trσ
    (F := F) (C := 2) (fun i => gnsTendsto_centered σ hσ
      (gnsTendsto_tracePreserving τ σ φ hφ (hj i))) (by norm_num)
    (fun n i => norm_centered_contraction σ hσ _ ((NonUnitalStarAlgHom.norm_apply_le φ _).trans (hd _))) u a l
  intro n
  have hr : integerEval (fun k => φ (d k) - σ (φ (d k)) • 1) u
      (a.map (fun i => j i n)) (l.map (fun b => (b.1, b.2.map (fun i => j i n)))) =
        integerEval (F n) u a l := by
    simp only [integerEval, List.map_map]
    congr 1
    · exact wordCoeff_map _ _ _
    · congr 1
      apply List.map_congr_left
      intro b _
      dsimp only [Function.comp_apply]
      rw [wordCoeff_map]
      rfl
  rw [← hr]
  apply hm
  · refine ⟨?_, ?_⟩
    · exact fun h => hl.1 (List.map_eq_nil_iff.mp h)
    · intro b hb
      rw [← List.map_dropLast] at hb
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
      exact fun h => hl.2 c hc (Option.map_eq_none_iff.mp h)
  · intro b hb
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
    exact hk c hc

include hσ trσ hφ in
/-- Scaling each coefficient separately removes the contraction restriction. -/
theorem all_integer_moments_of_trace_dense
    (d : ℕ → B) (hd : ∀ n, ‖d n‖ ≤ 1)
    (hdense : ∀ b : B, ‖b‖ ≤ 1 → ∃ j : ℕ → ℕ,
      GNSTendsto τ (fun k => d (j k)) atTop b)
    (u : unitary C)
    (hm : ∀ a : Option ℕ, ∀ l : List (IntAtom ℕ), admissibleIntTail l →
      (∀ b ∈ l, b.1 ≠ 0) →
      σ (integerEval (fun n => φ (d n) - σ (φ (d n)) • 1) u a l) = 0)
    (A : I → B) (a : Option I) (l : List (IntAtom I)) (hl : admissibleIntTail l)
    (hk : ∀ b ∈ l, b.1 ≠ 0) :
    σ (integerEval (fun i => φ (A i) - σ (φ (A i)) • 1) u a l) = 0 := by
  let c : I → ℂ := fun i => ((‖A i‖ + 1 : ℝ) : ℂ)
  have hc (i : I) : c i ≠ 0 := by
    dsimp only [c]
    exact_mod_cast (ne_of_gt (show 0 < ‖A i‖ + 1 by positivity))
  let A' : I → B := fun i => (c i)⁻¹ • A i
  have hA' (i : I) : ‖A' i‖ ≤ 1 := by
    change ‖(c i)⁻¹ • A i‖ ≤ 1
    rw [norm_smul, norm_inv]
    have hn : ‖c i‖ = ‖A i‖ + 1 := by
      simp only [c, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ‖A i‖ + 1)]
    rw [hn, ← div_eq_inv_mul]
    exact (div_le_one (by positivity)).mpr (by linarith)
  have hz := integer_moments_of_trace_dense τ σ hσ trσ φ hφ d hd hdense u hm A' hA' a l hl hk
  have he (i : I) : φ (A i) - σ (φ (A i)) • 1 =
      c i • (φ (A' i) - σ (φ (A' i)) • 1) := by
    dsimp only [A']
    rw [map_smul, map_smul, smul_sub, smul_smul, mul_inv_cancel₀ (hc i), one_smul,
      smul_smul]
    congr 1
    congr 1
    simp only [smul_eq_mul]
    field_simp [hc i]
  simp_rw [he]
  rw [integerEval_smul_family, map_smul, hz, smul_zero]

end KadisonSimilarity

end

end OAI
