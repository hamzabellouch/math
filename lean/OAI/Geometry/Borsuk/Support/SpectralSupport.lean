import Mathlib
import OAI.Geometry.Borsuk.MatrixGeometry.SignedExtension
import OAI.Geometry.Borsuk.MatrixGeometry.Rank

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section SpectralSupport
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι]
local notation "E" => EuclideanSpace ℝ ν
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

lemma Admissible.signedExtension_pos_iff {f : E → ι → ℝ} (hf : Admissible f)
    (A : Matrix ν ν ℝ) (i : ι) :
    0 < signedExtension f A i ↔ 0 < positiveExtension f A⁺ i := by
  have hp := hf.positiveExtension_nonneg A⁺ i
  have hn := hf.positiveExtension_nonneg A⁻ i
  have hpn := hf.positiveExtension_orthogonal (CFC.posPart_nonneg A)
    (CFC.negPart_nonneg A) (CFC.posPart_mul_negPart A) i
  change 0 < positiveExtension f A⁺ i - positiveExtension f A⁻ i ↔ _
  constructor
  · intro h; linarith
  · intro h
    have hz := (mul_eq_zero.mp hpn).resolve_left (ne_of_gt h)
    rwa [hz,sub_zero]

lemma Admissible.signedExtension_neg_iff {f : E → ι → ℝ} (hf : Admissible f)
    (A : Matrix ν ν ℝ) (i : ι) :
    signedExtension f A i < 0 ↔ 0 < positiveExtension f A⁻ i := by
  have hp := hf.positiveExtension_nonneg A⁺ i
  have hn := hf.positiveExtension_nonneg A⁻ i
  have hpn := hf.positiveExtension_orthogonal (CFC.posPart_nonneg A)
    (CFC.negPart_nonneg A) (CFC.posPart_mul_negPart A) i
  change positiveExtension f A⁺ i - positiveExtension f A⁻ i < 0 ↔ _
  constructor
  · intro h; linarith
  · intro h
    have hz := (mul_eq_zero.mp hpn).resolve_right (ne_of_gt h)
    rw [hz,zero_sub]
    exact neg_neg_of_pos h

lemma Admissible.signedExtension_positive_support {f : E → ι → ℝ} (hf : Admissible f)
    (A : Matrix ν ν ℝ) (i : ι) :
    0 < signedExtension f A i ↔ ∃ v : E,
      v ∈ LinearMap.range (op A⁺).toLinearMap ∧ ‖v‖ = 1 ∧ 0 < f v i := by
  rw [hf.signedExtension_pos_iff,hf.positiveExtension_support (CFC.posPart_nonneg A)]

lemma Admissible.signedExtension_negative_support {f : E → ι → ℝ} (hf : Admissible f)
    (A : Matrix ν ν ℝ) (i : ι) :
    signedExtension f A i < 0 ↔ ∃ v : E,
      v ∈ LinearMap.range (op A⁻).toLinearMap ∧ ‖v‖ = 1 ∧ 0 < f v i := by
  rw [hf.signedExtension_neg_iff,hf.positiveExtension_support (CFC.negPart_nonneg A)]

lemma Admissible.positiveExtension_range_mono {f : E → ι → ℝ} (hf : Admissible f)
    {P Q : Matrix ν ν ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hPQ : LinearMap.range (op P).toLinearMap ≤ LinearMap.range (op Q).toLinearMap)
    {i : ι} (hi : 0 < positiveExtension f P i) : 0 < positiveExtension f Q i := by
  obtain ⟨v,hv,hvn,hvi⟩ := (hf.positiveExtension_support hP i).mp hi
  exact (hf.positiveExtension_support hQ i).mpr ⟨v,hPQ hv,hvn,hvi⟩

omit [Nonempty ν] in
lemma rankOne_range (u : E) (hu : ‖u‖ = 1) :
    LinearMap.range (op (rankOne u)).toLinearMap = Submodule.span ℝ {u} := by
  apply le_antisymm
  · rintro v ⟨w,rfl⟩
    rw [ContinuousLinearMap.coe_coe,rankOne_action]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton u))
  · apply Submodule.span_le.mpr
    intro v hv
    have hvu : v = u := Set.mem_singleton_iff.mp hv
    subst v
    refine ⟨u,?_⟩
    simp [rankOne_action,hu]

lemma Admissible.signedExtension_range_labels {f : E → ι → ℝ} (hf : Admissible f)
    {A : Matrix ν ν ℝ} {I : Finset ι}
    (hI : ∀ i ∉ I, signedExtension f A i ≤ 0)
    {v : E} (hv : v ∈ LinearMap.range (op A⁺).toLinearMap) (hvn : ‖v‖ = 1)
    {i : ι} (hi : i ∉ I) : f v i = 0 := by
  apply le_antisymm _ (hf.nonneg v hvn i)
  by_contra hn
  have hp : 0 < f v i := lt_of_not_ge hn
  exact (not_lt_of_ge (hI i hi)) ((hf.signedExtension_positive_support A i).mpr ⟨v,hv,hvn,hp⟩)

omit [DecidableEq ν] [Nonempty ν] in

lemma subspace_eq_span_of_inner_separates (W : Submodule ℝ E) (w u : E)
    (hu : u ∈ W) (huw : ⟪w,u⟫ ≠ 0)
    (hsep : ∀ v ∈ W, ⟪w,v⟫ = 0 → v = 0) : W = Submodule.span ℝ {u} := by
  apply le_antisymm
  · intro v hv
    have hz : v - (⟪w,v⟫ / ⟪w,u⟫) • u = 0 := hsep _
      (W.sub_mem hv (W.smul_mem _ hu)) (by rw [inner_sub_right,inner_smul_right]; field_simp; ring)
    rw [sub_eq_zero] at hz
    rw [hz]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton u))
  · exact Submodule.span_le.mpr (by simpa using hu)

lemma Admissible.positive_range_separated {f : E → ι → ℝ} (hf : Admissible f)
    {A : Matrix ν ν ℝ} {I : Finset ι} {w : E} (hw : ‖w‖ = 1)
    (hwi : ∀ i ∈ I, 0 < f w i)
    (hI : ∀ i ∉ I, signedExtension f A i ≤ 0)
    {v : E} (hv : v ∈ LinearMap.range (op A⁺).toLinearMap) (hwv : ⟪w,v⟫ = 0) : v = 0 := by
  by_contra hn
  let u : E := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := by simp [u,norm_smul,norm_inv,hn]
  have hur : u ∈ LinearMap.range (op A⁺).toLinearMap := Submodule.smul_mem _ _ hv
  obtain ⟨i,hi⟩ := hf.support_nonempty hu
  have hip : 0 < f u i := by simpa [positiveSupport] using hi
  by_cases hiI : i ∈ I
  · exact hf.orthogonal w u hw hu (by simp [u,inner_smul_right,hwv]) i ⟨hwi i hiI,hip⟩
  · have hz := hf.signedExtension_range_labels hI hur hu hiI
    rw [hz] at hip
    exact (lt_irrefl 0) hip

end SpectralSupport
end BorsukNine

end OAI
