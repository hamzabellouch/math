import Mathlib
import OAI.Geometry.Borsuk.Support.MixedHomotopy

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
open Set
section MixedHits
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ
local notation "Y" => EuclideanSpace ℝ ι
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

lemma Admissible.mixedHomotopy_hit {f : E → ι → ℝ} (hf : Admissible f) {I : Finset ι}
    (hI : I.Nonempty)
    (hmax : ∀ u : E, ‖u‖ = 1 → I ⊆ positiveSupport f u → positiveSupport f u = I)
    {w c : E} (hc : c ∈ commonPositiveCone f I) (hcn : ‖c‖ = 1)
    (g : M → EuclideanSpace ℝ ↥(Iᶜ : Finset ι)) (hg : ∀ Q ∈ matrixFibre c, ∑ i, g Q i = 1)
    {r : ι → ℝ} (hro : ∀ i ∉ I, r i = 0) (hrs : ∑ i, r i = 1)
    {z : EuclideanSpace ℝ ↥(Iᶜ : Finset ι)} (hzs : ∑ i, z i = 1)
    {t d : ℝ} (ht : t ∈ Icc 0 1) (hd : 0 < d) {A : M}
    (hSA : A ∈ traceSphere ν) (hA : A ∈ purityChart f I w c)
    (he : mixedHomotopy f I w c g t A = d • blockVector I (1/2:ℝ) r (1/2:ℝ) z) :
    lineRepresentative w A ∈ orientedLevel f w r ∧
      fibreHomotopy f I c g t (lineRepresentative w A) (negativeFibre A) = z ∧
      A = (1/2:ℝ) • rankOne (lineRepresentative w A) - (1/2:ℝ) • negativeFibre A := by
  have hu := purityChart_unit hA
  have hQ := purityChart_fibre hA
  have hl := hasPositiveLine_trace_pos hA.2.1
  have hm := hA.2.2.2.1
  have hzero := hf.maximal_cone_zero hmax hu hA.2.2.2.2.1
  have hsum := hf.fibreHomotopy_sum hI hc hcn hu (interior_subset hA.2.2.2.2.2) g hg ht hQ
  obtain ⟨-,hl2,hm2,ha,hb⟩ := blockVector_ray hl hm (traceSphere_weights hSA) hd hzero hro
    (hf.sum_one _ hu) hrs hsum hzs he
  refine ⟨⟨hu,ha,(lineRepresentative_inner_pos hA.2.1 hA.2.2.1).le⟩,hb,?_⟩
  calc
    A = Matrix.trace A⁺ • rankOne (lineRepresentative w A) - Matrix.trace A⁻ • negativeFibre A :=
      negativeFibre_splitting hSA.1 hA.2.1 hA.2.2.1 hm
    _ = _ := by rw [hl2,hm2]

omit [DecidableEq ι] in
lemma Admissible.negative_trace_pos {f : E → ι → ℝ} (hf : Admissible f) {A : M} {i : ι}
    (hi : signedExtension f A i < 0) : 0 < Matrix.trace A⁻ := by
  have hp := (hf.signedExtension_neg_iff A i).mp hi
  have hle : positiveExtension f A⁻ i ≤ Matrix.trace A⁻ := by
    rw [← hf.positiveExtension_sum (CFC.negPart_nonneg A)]
    exact Finset.single_le_sum (fun j _ => hf.positiveExtension_nonneg A⁻ j) (Finset.mem_univ i)
  exact hp.trans_le hle

lemma Admissible.original_ray_level {f : E → ι → ℝ} (hf : Admissible f) {I : Finset ι}
    (hI : I.Nonempty) [Nonempty ↥(Iᶜ : Finset ι)]
    (hmax : ∀ u : E, ‖u‖ = 1 → I ⊆ positiveSupport f u → positiveSupport f u = I)
    {w : E} (hw : ‖w‖ = 1) (hwi : ∀ i ∈ I, 0 < f w i)
    {r : ι → ℝ} (hr : ∀ i ∈ I, 0 < r i) (hro : ∀ i ∉ I, r i = 0) (hrs : ∑ i, r i = 1)
    {z : EuclideanSpace ℝ ↥(Iᶜ : Finset ι)} (hz : ∀ i, 0 < z i) (hzs : ∑ i, z i = 1)
    {A : M} (hA : A ∈ traceSphere ν) {d : ℝ} (hd : 0 < d)
    (he : WithLp.toLp 2 (signedExtension f A) = d • blockVector I (1/2:ℝ) r (1/2:ℝ) z) :
    IsUnit A ∧ HasPositiveLine A ∧ op A⁺ w ≠ 0 ∧ 0 < Matrix.trace A⁻ ∧
      lineRepresentative w A ∈ orientedLevel f w r := by
  have hpos (i : ι) (hi : i ∈ I) : 0 < signedExtension f A i := by
    have hh := congrArg (fun v : Y => v i) he
    change signedExtension f A i = d * blockVector I (1/2:ℝ) r (1/2:ℝ) z i at hh
    rw [hh,blockVector_in _ _ _ _ _ hi]
    exact mul_pos hd (mul_pos (by norm_num) (hr i hi))
  have hneg (i : ↥(Iᶜ : Finset ι)) : signedExtension f A i.val < 0 := by
    have hh := congrArg (fun v : Y => v i.val) he
    change signedExtension f A i.val = d * blockVector I (1/2:ℝ) r (1/2:ℝ) z i.val at hh
    rw [hh,blockVector_out]
    exact mul_neg_of_pos_of_neg hd (mul_neg_of_neg_of_pos (by norm_num) (hz i))
  have hunit : IsUnit A := hf.signedExtension_fullSupport hA.1 (fun i => by
    by_cases hi : i ∈ I
    · exact ne_of_gt (hpos i hi)
    · exact ne_of_lt (hneg ⟨i,Finset.mem_compl.mpr hi⟩))
  obtain ⟨i,hi⟩ := hI
  have hline : HasPositiveLine A := hf.signedExtension_positive_rankOne hw hwi
    (fun j hj => (hneg ⟨j,Finset.mem_compl.mpr hj⟩).le) ⟨i,hpos i hi⟩
  have hAw : op A⁺ w ≠ 0 := by
    obtain ⟨u,hu,lam,hl,hP⟩ := hline
    have hui : 0 < f u i := (hf.signedExtension_line_labels hu hl hP i).mp (hpos i hi)
    have hwu : ⟪w,u⟫ ≠ 0 := fun heq => hf.orthogonal w u hw hu heq i ⟨hwi i hi,hui⟩
    exact unit_rankOne_inner_nonzero ⟨u,hu,lam,hl,hP⟩ hu hl hP hwu
  have hu := lineRepresentative_norm hAw
  have hc : lineRepresentative w A ∈ commonPositiveCone f I := by
    intro j hj
    rw [homogeneousLift_unit f hu]
    exact (hf.signedExtension_line_labels hu (hasPositiveLine_trace_pos hline)
      (positive_line_representative hline hAw) j).mp (hpos j hj)
  have hm := hf.negative_trace_pos (hneg (Classical.arbitrary ↥(Iᶜ : Finset ι)))
  have hchart : A ∈ purityChart f I w (lineRepresentative w A) :=
    ⟨hunit,hline,hAw,hm,hc,interior_safe_mem_own_chamber (hf.commonPositiveCone_interior_safe I hc)⟩
  have hg := hf.mixedHomotopy_zero hmax (fun _ => (0 : EuclideanSpace ℝ ↥(Iᶜ : Finset ι))) hA.1 hchart
  have hb : blockVector I (Matrix.trace A⁺) (f (lineRepresentative w A)) (Matrix.trace A⁻)
      (negativeCoordinates f I (negativeFibre A)) = d • blockVector I (1/2:ℝ) r (1/2:ℝ) z := by
    rw [← he,← hg]
    exact congrArg (blockVector I (Matrix.trace A⁺) (f (lineRepresentative w A)) (Matrix.trace A⁻))
      (fibreHomotopy_zero f I (lineRepresentative w A) (fun _ => 0) hu (negativeFibre A)).symm
  have hQ := purityChart_fibre hchart
  obtain ⟨-,-,-,ha,-⟩ := blockVector_ray (hasPositiveLine_trace_pos hline) hm (traceSphere_weights hA) hd
    (hf.maximal_cone_zero hmax hu hc) hro (hf.sum_one _ hu) hrs
    (hf.negativeCoordinates_sum (hf.commonPositiveCone_safe I hc) hQ) hzs hb
  exact ⟨hunit,hline,hAw,hm,hu,ha,(lineRepresentative_inner_pos hline hAw).le⟩

end MixedHits
end BorsukNine

end OAI
