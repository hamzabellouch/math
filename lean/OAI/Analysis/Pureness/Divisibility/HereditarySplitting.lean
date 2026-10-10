import OAI.Analysis.Pureness.Operators.OrthogonalRanks
import OAI.Analysis.Pureness.States.ScalarCorner

namespace OAI
namespace CuntzPureness
open Filter Topology ComplexStarModule
open scoped ComplexOrder CStarAlgebra
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
lemma hereditary_complex_smul_mem {h x : A} (z : ℂ) (hx : x ∈ hereditaryCarrier h) :
    z • x ∈ hereditaryCarrier h := by
  obtain ⟨u, hu, ht⟩ := mem_closure_iff_seq_limit.mp hx
  apply isClosed_closure.mem_of_tendsto (ht.const_smul z)
  apply Eventually.of_forall
  intro j
  obtain ⟨w, hw⟩ := hu j
  apply subset_closure
  exact ⟨z • w, by simp only [← hw, mul_smul_comm, smul_mul_assoc]⟩

lemma hereditary_realPart_mem {h x : A} (hh : 0 ≤ h) (hx : x ∈ hereditaryCarrier h) :
    (ℜ x : A) ∈ hereditaryCarrier h := by
  rw [realPart_apply_coe]
  exact (hereditarySubalgebra h hh).smul_mem _
    ((hereditarySubalgebra h hh).add_mem hx (star_mem (s := hereditarySubalgebra h hh) hx))

lemma hereditary_imaginaryPart_mem {h x : A} (hh : 0 ≤ h) (hx : x ∈ hereditaryCarrier h) :
    (ℑ x : A) ∈ hereditaryCarrier h := by
  rw [imaginaryPart_apply_coe]
  apply hereditary_complex_smul_mem
  exact (hereditarySubalgebra h hh).smul_mem _
    ((hereditarySubalgebra h hh).sub_mem hx (star_mem (s := hereditarySubalgebra h hh) hx))

lemma trace_selfAdjoint_im_zero (τ : TracialState A) (x : A) (hx : IsSelfAdjoint x) :
    (τ.functional x).im = 0 := by
  have hp : (τ.functional x⁺).im = 0 :=
    (Complex.nonneg_iff.mp (τ.functional.map_nonneg (CFC.posPart_nonneg x))).2.symm
  have hq : (τ.functional x⁻).im = 0 :=
    (Complex.nonneg_iff.mp (τ.functional.map_nonneg (CFC.negPart_nonneg x))).2.symm
  have he := congrArg (fun a => (τ.functional a).im) (CFC.posPart_sub_negPart x hx)
  simpa only [map_sub, Complex.sub_im, hp, hq, sub_self] using he.symm

lemma trace_zero_selfadjoint_split (τ : TracialState A) (hsimple : TopologicallySimple A)
    (h x : A) (hh : 0 ≤ h) (hx : IsSelfAdjoint x) (hx0 : x ≠ 0)
    (hxm : x ∈ hereditaryCarrier h) (hτ : τ.functional x = 0) :
    ∃ e f : A, 0 ≤ e ∧ e ≠ 0 ∧ e ∈ hereditaryCarrier h ∧
      0 ≤ f ∧ f ≠ 0 ∧ f ∈ hereditaryCarrier h ∧ e * f = 0 := by
  have heq : τ.functional (x⁺) = τ.functional (x⁻) := by
    apply sub_eq_zero.mp
    rw [← map_sub, CFC.posPart_sub_negPart x hx, hτ]
  have hp0 : x⁺ ≠ 0 := by
    intro hp
    have hq := τ.faithful hsimple _ (CFC.negPart_nonneg x) (by rw [← heq, hp, map_zero])
    apply hx0
    rw [← CFC.posPart_sub_negPart x hx, hp, hq, sub_zero]
  have hq0 : x⁻ ≠ 0 := by
    intro hq
    have hp := τ.faithful hsimple _ (CFC.posPart_nonneg x) (by rw [heq, hq, map_zero])
    apply hx0
    rw [← CFC.posPart_sub_negPart x hx, hp, hq, sub_zero]
  refine ⟨x⁺, x⁻, CFC.posPart_nonneg x, hp0, ?_,
    CFC.negPart_nonneg x, hq0, ?_, CFC.posPart_mul_negPart x⟩
  · change x⁺ ∈ hereditarySubalgebra h hh
    rw [CFC.posPart_def]
    exact cfcₙ_mem _ (show x ∈ hereditarySubalgebra h hh from hxm)
  · change x⁻ ∈ hereditarySubalgebra h hh
    rw [CFC.negPart_def]
    exact cfcₙ_mem _ (show x ∈ hereditarySubalgebra h hh from hxm)

theorem exists_orthogonal_pair_hereditary (τ : TracialState A)
    (hsimple : TopologicallySimple A) (hinf : ¬FiniteDimensional ℂ A)
    (h : A) (hh : 0 ≤ h) (hh0 : h ≠ 0) :
    ∃ e f : A, 0 ≤ e ∧ e ≠ 0 ∧ e ∈ hereditaryCarrier h ∧
      0 ≤ f ∧ f ≠ 0 ∧ f ∈ hereditaryCarrier h ∧ e * f = 0 := by
  by_contra hno
  have hτh0 : τ.functional h ≠ 0 := fun hz => hh0 (τ.faithful hsimple h hh hz)
  have hτh : 0 < (τ.functional h).re :=
    (Complex.pos_iff.mp (lt_of_le_of_ne (τ.functional.map_nonneg hh) hτh0.symm)).1
  have hscalar (x : A) (hx : IsSelfAdjoint x) (hxm : x ∈ hereditaryCarrier h) :
      ∃ r : ℝ, x = r • h := by
    let r := (τ.functional x).re / (τ.functional h).re
    have hy : IsSelfAdjoint (x - r • h) := hx.sub ((IsSelfAdjoint.all r).smul hh.isSelfAdjoint)
    have hym : x - r • h ∈ hereditaryCarrier h :=
      (hereditarySubalgebra h hh).sub_mem hxm
        ((hereditarySubalgebra h hh).smul_mem r (self_mem_hereditary h hh))
    have hτy : τ.functional (x - r • h) = 0 := by
      rw [map_sub, τ.functional.map_smul_of_tower]
      apply Complex.ext
      · simp only [Complex.sub_re, Complex.smul_re, Complex.zero_re]
        dsimp [r]
        exact sub_eq_zero.mpr (div_mul_cancel₀ _ (ne_of_gt hτh)).symm
      · simp only [Complex.sub_im, Complex.smul_im, Complex.zero_im,
          trace_selfAdjoint_im_zero τ x hx, trace_selfAdjoint_im_zero τ h hh.isSelfAdjoint,
          smul_zero, sub_zero]
    have hy0 : x - r • h = 0 := by
      by_contra hy0
      exact hno (trace_zero_selfadjoint_split τ hsimple h _ hh hy hy0 hym hτy)
    exact ⟨r, sub_eq_zero.mp hy0⟩
  apply hinf
  apply finiteDimensional_of_scalar_sandwich hsimple h hh hh0
  intro a
  have ham : h * a * h ∈ hereditaryCarrier h := subset_closure ⟨a, rfl⟩
  obtain ⟨r, hr⟩ := hscalar (ℜ (h * a * h)) (ℜ (h * a * h)).2 (hereditary_realPart_mem hh ham)
  obtain ⟨s, hs⟩ := hscalar (ℑ (h * a * h)) (ℑ (h * a * h)).2 (hereditary_imaginaryPart_mem hh ham)
  refine ⟨(r : ℂ) + Complex.I * (s : ℂ), ?_⟩
  rw [← realPart_add_I_smul_imaginaryPart (h * a * h), hr, hs]
  simp only [add_smul, mul_smul, Complex.coe_smul]
end CuntzPureness

end OAI
