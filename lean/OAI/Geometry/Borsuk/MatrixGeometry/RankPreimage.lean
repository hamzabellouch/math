import Mathlib
import OAI.Geometry.Borsuk.Support.SpectralSupport

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section RankOnePreimage
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι]
local notation "E" => EuclideanSpace ℝ ν
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

omit [Nonempty ν] in
lemma symmetric_inner_action {A : Matrix ν ν ℝ} (hA : IsSelfAdjoint A) (u v : E) :
    ⟪u,op A v⟫ = ⟪op A u,v⟫ := by
  rw [← ContinuousLinearMap.adjoint_inner_right,← ContinuousLinearMap.star_eq_adjoint,
    ← map_star,hA.star_eq]

omit [Nonempty ν] in
lemma symmetric_eq_rankOne_of_range {A : Matrix ν ν ℝ} (hA : IsSelfAdjoint A)
    {u : E} (hu : ‖u‖ = 1)
    (hR : LinearMap.range (op A).toLinearMap ≤ Submodule.span ℝ {u}) :
    A = ⟪u,op A u⟫ • rankOne u := by
  have he (v : E) : op A v = ⟪u,op A v⟫ • u := by
    obtain ⟨t,ht⟩ := Submodule.mem_span_singleton.mp (hR (LinearMap.mem_range_self _ v))
    change t • u = (op A) v at ht
    rw [← ht,inner_smul_right,real_inner_self_eq_norm_sq,hu,one_pow,mul_one]
  have hscalar (v : E) : ⟪u,op A v⟫ = ⟪u,op A u⟫ * ⟪u,v⟫ := by
    calc
      ⟪u,op A v⟫ = ⟪op A u,v⟫ := symmetric_inner_action hA u v
      _ = ⟪u,op A u⟫ * ⟪u,v⟫ := by
        conv_lhs => rw [he u]
        simp only [inner_smul_left,conj_trivial]
  apply (Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)).injective
  change op A = op (⟪u,op A u⟫ • rankOne u)
  rw [map_smul]
  apply ContinuousLinearMap.ext
  intro v
  rw [smul_apply,rankOne_action,smul_smul,← hscalar,← he]

lemma Admissible.signedExtension_positive_rankOne {f : E → ι → ℝ} (hf : Admissible f)
    {A : Matrix ν ν ℝ} {I : Finset ι} {w : E} (hw : ‖w‖ = 1)
    (hwi : ∀ i ∈ I, 0 < f w i)
    (hI : ∀ i ∉ I, signedExtension f A i ≤ 0)
    (hpos : ∃ i, 0 < signedExtension f A i) :
    ∃ u : E, ‖u‖ = 1 ∧ ∃ lam : ℝ, 0 < lam ∧ A⁺ = lam • rankOne u := by
  obtain ⟨i,hi⟩ := hpos
  obtain ⟨u,hur,hu,hui⟩ := (hf.signedExtension_positive_support A i).mp hi
  have hwu : ⟪w,u⟫ ≠ 0 := by
    intro he
    have hz := hf.positive_range_separated hw hwi hI hur he
    simp [hz] at hu
  have hr : LinearMap.range (op A⁺).toLinearMap = Submodule.span ℝ {u} :=
    subspace_eq_span_of_inner_separates _ w u hur hwu
      (fun v hv horth => hf.positive_range_separated hw hwi hI hv horth)
  have hP := symmetric_eq_rankOne_of_range (CFC.posPart_nonneg A).isSelfAdjoint hu hr.le
  let lam : ℝ := ⟪u,op A⁺ u⟫
  have hlam : 0 ≤ lam := by
    change 0 ≤ ⟪u,op A⁺ u⟫
    rw [← sqrt_action_norm_sq A⁺ (CFC.posPart_nonneg A) u]
    positivity
  have hlam0 : lam ≠ 0 := by
    intro hz
    have hp0 : A⁺ = 0 := by simpa only [lam,hz,zero_smul] using hP
    obtain ⟨v,hv⟩ := hur
    rw [hp0,map_zero] at hv
    have hu0 : u = 0 := by simpa using hv.symm
    simp [hu0] at hu
  exact ⟨u,hu,lam,lt_of_le_of_ne hlam (Ne.symm hlam0),hP⟩

lemma Admissible.signedExtension_splitting {f : E → ι → ℝ} (hf : Admissible f)
    {A : Matrix ν ν ℝ} (hA : IsSelfAdjoint A) {u : E} (hu : ‖u‖ = 1)
    {lam : ℝ} (hlam : 0 < lam) (he : A⁺ = lam • rankOne u) :
    A = lam • rankOne u - A⁻ ∧
      positiveExtension f A⁺ = lam • f u ∧
      signedExtension f A = lam • f u - positiveExtension f A⁻ := by
  have hp : positiveExtension f A⁺ = lam • f u := by
    rw [he,positiveExtension_smul_nonneg f (rankOne_nonneg u) hlam.le,
      hf.positiveExtension_rankOne u hu]
  refine ⟨?_,hp,?_⟩
  · rw [← he]
    exact (CFC.posPart_sub_negPart A hA).symm
  · exact congrArg (fun v => v - positiveExtension f A⁻) hp

lemma Admissible.signedExtension_line_labels {f : E → ι → ℝ} (hf : Admissible f)
    {A : Matrix ν ν ℝ} {u : E} (hu : ‖u‖ = 1)
    {lam : ℝ} (hlam : 0 < lam) (he : A⁺ = lam • rankOne u) (i : ι) :
    0 < signedExtension f A i ↔ 0 < f u i := by
  rw [hf.signedExtension_pos_iff,he,
    positiveExtension_smul_nonneg f (rankOne_nonneg u) hlam.le,
    hf.positiveExtension_rankOne u hu,Pi.smul_apply,smul_eq_mul]
  exact mul_pos_iff_of_pos_left hlam

end RankOnePreimage
end BorsukNine

end OAI
