import Mathlib
import OAI.Geometry.Borsuk.LocalParity.LocalModel
import OAI.Geometry.Borsuk.MatrixGeometry.BlockLine
import OAI.Geometry.Borsuk.LocalParity.LocalRegular

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
section LocalMix
variable {k : ℕ} {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ν
local notation "W" => EuclideanSpace ℝ (Fin k)
local notation "M" => Matrix ν ν ℝ
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

omit [DecidableEq ν] [Nonempty ν] [DecidableEq ι] in
lemma Admissible.sum_on_support {f : E → ι → ℝ} (hf : Admissible f) {u : E} (hu : ‖u‖ = 1)
    {I : Finset ι} (hI : positiveSupport f u = I) : ∑ i ∈ I, f u i = 1 := by
  rw [← hf.sum_one u hu]
  apply Finset.sum_subset (Finset.subset_univ I)
  intro i _ hi
  apply le_antisymm _ (hf.nonneg u hu i)
  exact le_of_not_gt (fun h => hi (hI ▸ (mem_positiveSupport f u i).mpr h))

omit [DecidableEq ι] in
lemma Admissible.extension_on_positiveLine {f : E → ι → ℝ} (hf : Admissible f)
    {A : M} {u : E} (hu : ‖u‖ = 1) {lam : ℝ} (hl : 0 < lam)
    (hP : A⁺ = lam • rankOne u) {i : ι} (hi : 0 < f u i) :
    signedExtension f A i = lam * f u i := by
  have hn := hf.positiveExtension_kernel (CFC.negPart_nonneg A) hu
    (negPart_kernel_of_positiveLine hu hl hP) hi
  simp only [signedExtension,Pi.sub_apply,hn,sub_zero,hP,
    positiveExtension_smul_nonneg f (rankOne_nonneg u) hl.le,
    hf.positiveExtension_rankOne u hu,Pi.smul_apply,smul_eq_mul]

lemma Admissible.localBlockModel_eq_of_positiveLine {f : E → ι → ℝ} (hf : Admissible f)
    {A : M} (hA : IsSelfAdjoint A) {c : E} (hc : ‖c‖ = 1) (e : W →ₗᵢ[ℝ] E)
    (he : ∀ v, ⟪c,e v⟫ = 0) (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (D : W ≃L[ℝ] W)
    {lam : ℝ} (hl : 0 < lam) (hP : A⁺ = lam • rankOne c) :
    localBlockModel f c e a D A = signedExtension f A := by
  have hb := blockOff_positiveLine e hA hc he hl hP
  have hC : blockCorner e A ≤ 0 := by rw [blockCorner_positiveLine e hA hc he hes hl hP]; exact neg_nonpos.mpr (CFC.negPart_nonneg A)
  have ha : 0 ≤ blockScalar c A := by rw [blockScalar_positiveLine hA hc hl hP]; exact hl.le
  rw [hf.block_extension e hc he hes hA hb ha hC]
  simp only [localBlockModel,hb,map_zero,add_zero]

noncomputable def localBlockMix (f : E → ι → ℝ) (c : E) (e : W →ₗᵢ[ℝ] E)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (D : W ≃L[ℝ] W) (t : ℝ) (A : M) : ι → ℝ :=
  (1-t) • signedExtension f A + t • localBlockModel f c e a D A

lemma Admissible.localBlockMix_sum {f : E → ι → ℝ} (hf : Admissible f)
    {A : M} (hA : IsSelfAdjoint A) {c u : E} (hc : ‖c‖ = 1) (hu : ‖u‖ = 1)
    (e : W →ₗᵢ[ℝ] E) (he : ∀ v, ⟪c,e v⟫ = 0)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (hIc : positiveSupport f c = I) (hIu : positiveSupport f u = I)
    (D : W ≃L[ℝ] W) {lam : ℝ} (hl : 0 < lam) (hP : A⁺ = lam • rankOne u) (t : ℝ) :
    ∑ i ∈ I, localBlockMix f c e a D t A i = (1-t)*lam + t*blockScalar c A := by
  have hF : ∑ i ∈ I, signedExtension f A i = lam := by
    calc
      _ = ∑ i ∈ I, lam * f u i := Finset.sum_congr rfl (fun i hi =>
        hf.extension_on_positiveLine hu hl hP ((mem_positiveSupport f u i).mp (hIu.symm ▸ hi)))
      _ = _ := by rw [← Finset.mul_sum,hf.sum_on_support hu hIu,mul_one]
  simp only [localBlockMix,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_add_distrib,
    ← Finset.mul_sum,hF,hf.localBlockModel_sum_facet hc e he a hIc D hA]

lemma Admissible.localBlockMix_ne_zero {f : E → ι → ℝ} (hf : Admissible f)
    {A : M} (hA : IsSelfAdjoint A) {c u : E} (hc : ‖c‖ = 1) (hu : ‖u‖ = 1)
    (e : W →ₗᵢ[ℝ] E) (he : ∀ v, ⟪c,e v⟫ = 0)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (hIc : positiveSupport f c = I) (hIu : positiveSupport f u = I)
    (D : W ≃L[ℝ] W) {lam : ℝ} (hl : 0 < lam) (hP : A⁺ = lam • rankOne u)
    (ha : 0 < blockScalar c A) {t : ℝ} (ht : t ∈ Set.Icc 0 1) : localBlockMix f c e a D t A ≠ 0 := by
  intro hz
  have hh := hf.localBlockMix_sum hA hc hu e he a hIc hIu D hl hP t
  rw [hz] at hh
  simp only [Pi.zero_apply,Finset.sum_const_zero] at hh
  have hp : 0 < (1-t)*lam + t*blockScalar c A := by
    by_cases ht0 : t = 0
    · simpa [ht0] using hl
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr ht.2) hl.le)
        (mul_pos (lt_of_le_of_ne ht.1 (Ne.symm ht0)) ha)
  linarith

noncomputable def facetTail {I : Finset ι} (a : Fin (k+1) ≃ ↥I) : (ι → ℝ) →ₗ[ℝ] W where
  toFun r := WithLp.toLp 2 (fun j => r (a j.succ).val)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma Admissible.localBlockMix_tangent_zero {f : E → ι → ℝ} (hf : Admissible f)
    {A : M} (hA : IsSelfAdjoint A) {c u : E} (hc : ‖c‖ = 1) (hu : ‖u‖ = 1)
    (e : W →ₗᵢ[ℝ] E) (he : ∀ v, ⟪c,e v⟫ = 0) (_hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (hIc : positiveSupport f c = I) (hIu : positiveSupport f u = I)
    (D : W ≃L[ℝ] W) {lam : ℝ} (hl : 0 < lam) (hP : A⁺ = lam • rankOne u) (_hcu : 0 < ⟪c,u⟫)
    (_hB : NegativeQuadratic (Matrix.toEuclideanCLM (𝕜 := ℝ) (matrixCompress e A)))
    (_hreg : hemisphereInverse c e u ≠ 0 →
      0 < ⟪hemisphereInverse c e u,D.symm (facetTail a (f u - f c))⟫)
    {y : ι → ℝ} {rho d t : ℝ} (hyi : ∀ i ∈ I, y i = rho * f c i)
    (_ht : t ∈ Set.Icc 0 1) (hM : localBlockMix f c e a D t A = d • y) :
    (1-t) • (lam • facetTail a (f u - f c)) + t • D (blockOff c e A) = 0 := by
  have hp : ∀ i ∈ I, 0 < f c i := fun i hi => (mem_positiveSupport f c i).mp (hIc.symm ▸ hi)
  have hpu : ∀ i ∈ I, 0 < f u i := fun i hi => (mem_positiveSupport f u i).mp (hIu.symm ▸ hi)
  have hs : (1-t)*lam+t*blockScalar c A = d*rho := by
    rw [← hf.localBlockMix_sum hA hc hu e he a hIc hIu D hl hP t,hM]
    simp only [Pi.smul_apply,smul_eq_mul]
    calc
      _ = ∑ i ∈ I, d*(rho*f c i) := Finset.sum_congr rfl (fun i hi => by rw [hyi i hi])
      _ = _ := by rw [← Finset.mul_sum,← Finset.mul_sum,hf.sum_on_support hc hIc,mul_one]
  apply PiLp.ext
  intro j
  have hi := (a j.succ).property
  have hh := congrFun hM (a j.succ).val
  simp only [localBlockMix,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
    hf.extension_on_positiveLine hu hl hP (hpu _ hi),
    hf.localBlockModel_on_facet hc e he a hp D hA hi,facetTangent_apply,Fin.cases_succ,hyi _ hi] at hh
  change (1-t)*(lam*(f u (a j.succ).val - f c (a j.succ).val)) + t*(D (blockOff c e A)) j = 0
  nlinarith [congrArg (fun x : ℝ => x * f c (a j.succ).val) hs]

lemma Admissible.localBlockMix_hit {f : E → ι → ℝ} (hf : Admissible f)
    {A : M} (hA : IsSelfAdjoint A) {c u : E} (hc : ‖c‖ = 1) (hu : ‖u‖ = 1)
    (e : W →ₗᵢ[ℝ] E) (he : ∀ v, ⟪c,e v⟫ = 0) (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (hIc : positiveSupport f c = I) (hIu : positiveSupport f u = I)
    (D : W ≃L[ℝ] W) {lam : ℝ} (hl : 0 < lam) (hP : A⁺ = lam • rankOne u) (hcu : 0 < ⟪c,u⟫)
    (hB : NegativeQuadratic (Matrix.toEuclideanCLM (𝕜 := ℝ) (matrixCompress e A)))
    (hreg : hemisphereInverse c e u ≠ 0 →
      0 < ⟪hemisphereInverse c e u,D.symm (facetTail a (f u - f c))⟫)
    {y : ι → ℝ} {rho d t : ℝ} (hyi : ∀ i ∈ I, y i = rho * f c i)
    (ht : t ∈ Set.Icc 0 1) (hM : localBlockMix f c e a D t A = d • y) :
    u = c ∧ localBlockMix f c e a D t A = signedExtension f A := by
  have hz := hf.localBlockMix_tangent_zero hA hc hu e he hes a hIc hIu D hl hP hcu hB hreg hyi ht hM
  have hb : hemisphereInverse c e u ≠ 0 → 0 < ⟪hemisphereInverse c e u,blockOff c e A⟫ := by
    intro hv
    rw [blockOff_eigenvector e hc he hes hu hcu (positiveLine_eigenvector hA hu hl hP)]
    exact negativeQuadratic_pos_sub hB hv hl
  have hv : hemisphereInverse c e u = 0 := regular_mixed_zero D (g := fun _ : W => facetTail a (f u-f c)) (v := hemisphereInverse c e u) (b := blockOff c e A) hreg hb hl ht hz
  have huc : u = c := by
    have hh := hemisphereChart_inverse c e hc he hes hu hcu
    rw [hv] at hh
    simpa only [hemisphereChart,SimplicialChains.unitRadial,map_zero,add_zero,hc,inv_one,one_smul] using hh.symm
  refine ⟨huc,?_⟩
  have hm := hf.localBlockModel_eq_of_positiveLine hA hc e he hes a D hl (huc ▸ hP)
  rw [localBlockMix,hm,← add_smul,sub_add_cancel,one_smul]
end LocalMix
end BorsukNine

end OAI
