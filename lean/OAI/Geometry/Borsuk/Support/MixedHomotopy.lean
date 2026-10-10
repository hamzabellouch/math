import Mathlib
import OAI.Geometry.Borsuk.MatrixGeometry.FibreContinuity
import OAI.Geometry.Borsuk.Support.PurityChart
import OAI.Geometry.Borsuk.MatrixGeometry.BlockVector

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
open Set
section MixedHomotopy
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ
local notation "Y" => EuclideanSpace ℝ ι
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

omit [DecidableEq ν] [Nonempty ν] [DecidableEq ι] in
lemma Admissible.cone_unit_positive {f : E → ι → ℝ} (_hf : Admissible f)
    {I : Finset ι} {u : E} (hu : ‖u‖ = 1) (hc : u ∈ commonPositiveCone f I) :
    ∀ i ∈ I, 0 < f u i := by
  intro i hi
  simpa only [homogeneousLift_unit f hu] using hc i hi

omit [DecidableEq ν] [Nonempty ν] [DecidableEq ι] in
lemma Admissible.maximal_cone_zero {f : E → ι → ℝ} (hf : Admissible f) {I : Finset ι}
    (hmax : ∀ u : E, ‖u‖ = 1 → I ⊆ positiveSupport f u → positiveSupport f u = I)
    {u : E} (hu : ‖u‖ = 1) (hc : u ∈ commonPositiveCone f I) :
    ∀ i ∉ I, f u i = 0 := by
  have he : positiveSupport f u = I := hmax u hu (fun i hi =>
    (mem_positiveSupport f u i).mpr (hf.cone_unit_positive hu hc i hi))
  intro i hi
  apply le_antisymm _ (hf.nonneg u hu i)
  by_contra hp
  have hh := (mem_positiveSupport f u i).mpr (lt_of_not_ge hp)
  rw [he] at hh
  exact hi hh

omit [Nonempty ν] in
lemma traceSphere_weights {A : M} (hA : A ∈ traceSphere ν) :
    Matrix.trace A⁺ + Matrix.trace A⁻ = 1 := by
  rw [← Matrix.trace_add,CFC.posPart_add_negPart A hA.1]; exact hA.2

noncomputable def mixedHomotopy (f : E → ι → ℝ) (I : Finset ι) (w c : E)
    (g : M → EuclideanSpace ℝ ↥(Iᶜ : Finset ι)) (t : ℝ) (A : M) : Y :=
  blockVector I (Matrix.trace A⁺) (f (lineRepresentative w A)) (Matrix.trace A⁻)
    (fibreHomotopy f I c g t (lineRepresentative w A) (negativeFibre A))

lemma Admissible.mixedHomotopy_zero {f : E → ι → ℝ} (hf : Admissible f) {I : Finset ι}
    (hmax : ∀ u : E, ‖u‖ = 1 → I ⊆ positiveSupport f u → positiveSupport f u = I)
    {w c : E} (g : M → EuclideanSpace ℝ ↥(Iᶜ : Finset ι)) {A : M}
    (hSA : IsSelfAdjoint A) (hA : A ∈ purityChart f I w c) :
    mixedHomotopy f I w c g 0 A = WithLp.toLp 2 (signedExtension f A) := by
  have hu := purityChart_unit hA
  have hQ := purityChart_fibre hA
  have hl := hasPositiveLine_trace_pos hA.2.1
  have hm := hA.2.2.2.1
  have hs := (hf.signedExtension_splitting hSA hu hl (positive_line_representative hA.2.1 hA.2.2.1)).2.2
  have hneg : positiveExtension f A⁻ = Matrix.trace A⁻ • positiveExtension f (negativeFibre A) := by
    calc
      positiveExtension f A⁻ = positiveExtension f (Matrix.trace A⁻ • negativeFibre A) :=
        congrArg (positiveExtension f) (negativeFibre_smul (ne_of_gt hm)).symm
      _ = _ := positiveExtension_smul_nonneg f hQ.1 hm.le
  have hpos := hf.cone_unit_positive hu hA.2.2.2.2.1
  have hzero := hf.maximal_cone_zero hmax hu hA.2.2.2.2.1
  have hsafe := hf.commonPositiveCone_safe I hA.2.2.2.2.1
  apply PiLp.ext
  intro i
  change blockVector I (Matrix.trace A⁺) (f (lineRepresentative w A)) (Matrix.trace A⁻)
    (fibreHomotopy f I c g 0 (lineRepresentative w A) (negativeFibre A)) i = signedExtension f A i
  rw [fibreHomotopy_zero f I c g hu,hs,hneg]
  by_cases hi : i ∈ I
  · rw [blockVector_in _ _ _ _ _ hi]
    have hz := hf.positiveExtension_safe_zero hsafe hQ.1 hQ.2.2 hi
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,hz,mul_zero,sub_zero]
  · let j : ↥(Iᶜ : Finset ι) := ⟨i,Finset.mem_compl.mpr hi⟩
    have hj := blockVector_out I (Matrix.trace A⁺) (f (lineRepresentative w A)) (Matrix.trace A⁻)
      (negativeCoordinates f I (negativeFibre A)) j
    rw [hj]
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,hzero i hi,mul_zero,zero_sub]
    exact neg_mul _ _

omit [Nonempty ν] in
lemma Admissible.mixedHomotopy_nonzero {f : E → ι → ℝ} (hf : Admissible f) {I : Finset ι}
    (hI : I.Nonempty) {w c : E} (g : M → EuclideanSpace ℝ ↥(Iᶜ : Finset ι))
    (t : ℝ) {A : M} (hA : A ∈ purityChart f I w c) : mixedHomotopy f I w c g t A ≠ 0 :=
  blockVector_nonzero hI (hasPositiveLine_trace_pos hA.2.1)
    (hf.cone_unit_positive (purityChart_unit hA) hA.2.2.2.2.1) _

lemma Admissible.mixedHomotopy_continuousOn {f : E → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} (hI : I.Nonempty) {w c : E} (hc : c ∈ commonPositiveCone f I) (hcn : ‖c‖ = 1)
    (g : M → EuclideanSpace ℝ ↥(Iᶜ : Finset ι)) (hg : Continuous g) :
    ContinuousOn (fun p : ℝ × traceSphere ν => mixedHomotopy f I w c g p.1 p.2.val)
      (Icc (0:ℝ) 1 ×ˢ {A : traceSphere ν | A.val ∈ purityChart f I w c}) := by
  let S : Set (ℝ × traceSphere ν) := Icc (0:ℝ) 1 ×ˢ {A : traceSphere ν | A.val ∈ purityChart f I w c}
  have hA : Continuous (fun p : ℝ × traceSphere ν => p.2.val) := continuous_subtype_val.comp continuous_snd
  have hSA : ∀ p : ℝ × traceSphere ν, IsSelfAdjoint p.2.val := fun p => p.2.property.1
  have hu : ContinuousOn (fun p : ℝ × traceSphere ν => lineRepresentative w p.2.val) S :=
    (lineRepresentative_continuousOn _ hA hSA w).mono (fun p hp => hp.2.2.2.1)
  have hQ : ContinuousOn (fun p : ℝ × traceSphere ν => negativeFibre p.2.val) S :=
    (negativeFibre_continuousOn _ hA hSA).mono (fun p hp => ne_of_gt hp.2.2.2.2.1)
  have htuple : ContinuousOn (fun p : ℝ × traceSphere ν =>
      (p.1,lineRepresentative w p.2.val,negativeFibre p.2.val)) S :=
    continuous_fst.continuousOn.prodMk (hu.prodMk hQ)
  have hF : ContinuousOn (fun p : ℝ × traceSphere ν =>
      fibreHomotopy f I c g p.1 (lineRepresentative w p.2.val) (negativeFibre p.2.val)) S :=
    ContinuousOn.comp' (g := fun p : ℝ × E × M => fibreHomotopy f I c g p.1 p.2.1 p.2.2)
      (f := fun p : ℝ × traceSphere ν => (p.1,lineRepresentative w p.2.val,negativeFibre p.2.val))
      (hf.fibreHomotopy_continuousOn hI hc hcn g hg) htuple
      (fun p hp => ⟨hp.1,purityChart_unit hp.2,interior_subset hp.2.2.2.2.2.2,purityChart_fibre hp.2⟩)
  have hl : Continuous (fun p : ℝ × traceSphere ν => Matrix.trace p.2.val⁺) :=
    matrix_trace_continuous.comp (matrix_posPart_continuousOn.comp_continuous hA hSA)
  have hm : Continuous (fun p : ℝ × traceSphere ν => Matrix.trace p.2.val⁻) :=
    matrix_trace_continuous.comp (matrix_negPart_continuousOn.comp_continuous hA hSA)
  have hfC : Continuous f := continuous_pi (fun i => (hf.smooth i).continuous)
  exact blockVector_continuousOn I hl.continuousOn (hfC.comp_continuousOn hu) hm.continuousOn hF

end MixedHomotopy
end BorsukNine

end OAI
