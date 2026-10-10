import Mathlib
import OAI.Geometry.Borsuk.Support.ActiveChambers
import OAI.Geometry.Borsuk.SphereGeometry.TraceSphere
import OAI.Geometry.Borsuk.MatrixGeometry.MatrixFibre

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
section PurityGeometry
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

omit [DecidableEq ν] [Nonempty ν] [DecidableEq ι] in
lemma Admissible.safe_orthogonal_zero {f : E → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} {u v : E} (hu : u ∈ safeNormals (activeVectors f I))
    (hv : ‖v‖ = 1) (horth : ⟪u,v⟫ = 0) {i : ι} (hi : i ∈ I) : f v i = 0 := by
  apply le_antisymm _ (hf.nonneg v hv i)
  apply le_of_not_gt
  intro hp
  exact hu v ⟨i,hi,by rwa [homogeneousLift_unit f hv]⟩ horth

omit [DecidableEq ι] in
lemma Admissible.positiveExtension_safe_zero {f : E → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} {u : E} (hu : u ∈ safeNormals (activeVectors f I))
    {Q : M} (hQ : 0 ≤ Q) (hQu : op Q u = 0) {i : ι} (hi : i ∈ I) :
    positiveExtension f Q i = 0 := by
  apply le_antisymm _ (hf.positiveExtension_nonneg Q i)
  apply le_of_not_gt
  intro hp
  obtain ⟨v,⟨x,hx⟩,hv,hvi⟩ := (hf.positiveExtension_support hQ i).mp hp
  have horth : ⟪u,v⟫ = 0 := by rw [← hx]; exact matrix_image_orthogonal_kernel hQ.isSelfAdjoint hQu x
  exact (ne_of_gt hvi) (hf.safe_orthogonal_zero hu hv horth hi)

lemma Admissible.fibre_boundary_missing {f : E → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} {u : E} (hu : u ∈ safeNormals (activeVectors f I))
    {Q : M} (hQ : 0 ≤ Q) (hnot : ¬ IsUnit (rankOne u + Q)) :
    ∃ i ∈ Iᶜ, positiveExtension f Q i = 0 := by
  obtain ⟨v,hv,huv,hQv⟩ := fibre_boundary_kernel hQ u hnot
  obtain ⟨i,hi⟩ := hf.support_nonempty hv
  have hip := (mem_positiveSupport f v i).mp hi
  refine ⟨i,?_,hf.positiveExtension_kernel hQ hv hQv hip⟩
  exact Finset.mem_compl.mpr (fun h => (ne_of_gt hip) (hf.safe_orthogonal_zero hu hv huv h))

noncomputable def orientedLevel (f : E → ι → ℝ) (w : E) (r : ι → ℝ) : Set E :=
  {u | ‖u‖ = 1 ∧ f u = r ∧ 0 ≤ ⟪w,u⟫}

omit [DecidableEq ν] [Nonempty ν] [DecidableEq ι] in
lemma Admissible.orientedLevel_compact {f : E → ι → ℝ} (hf : Admissible f)
    (w : E) (r : ι → ℝ) : IsCompact (orientedLevel f w r) := by
  have hc : Continuous f := continuous_pi (fun i => (hf.smooth i).continuous)
  have he : orientedLevel f w r = Metric.sphere (0:E) 1 ∩
      {u | f u = r ∧ 0 ≤ ⟪w,u⟫} := by ext u; simp [orientedLevel]
  rw [he]
  exact (isCompact_sphere (0:E) 1).inter_right ((isClosed_eq hc continuous_const).inter
    (isClosed_le continuous_const (show Continuous (fun u : E => ⟪w,u⟫) from
      (continuous_const.inner continuous_id))))

omit [DecidableEq ν] [Nonempty ν] [DecidableEq ι] in
lemma Admissible.orientedLevel_inner_pos {f : E → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} (hI : I.Nonempty) {w : E} (hw : ‖w‖ = 1)
    (hwi : ∀ i ∈ I, 0 < f w i) {r : ι → ℝ} (hr : ∀ i ∈ I, 0 < r i)
    {u : E} (hu : u ∈ orientedLevel f w r) : 0 < ⟪w,u⟫ := by
  apply lt_of_le_of_ne hu.2.2
  intro he
  obtain ⟨i,hi⟩ := hI
  exact hf.orthogonal w u hw hu.1 he.symm i ⟨hwi i hi,by rw [hu.2.1]; exact hr i hi⟩

omit [DecidableEq ν] [Nonempty ν] [Fintype ι] [DecidableEq ι] in
lemma orientedLevel_cone {f : E → ι → ℝ} {I : Finset ι} {w : E} {r : ι → ℝ}
    (hr : ∀ i ∈ I, 0 < r i) {u : E} (hu : u ∈ orientedLevel f w r) :
    u ∈ commonPositiveCone f I := by
  intro i hi
  rw [homogeneousLift_unit f hu.1,hu.2.1]
  exact hr i hi

noncomputable def levelFibre (f : E → ι → ℝ) (w : E) (r : ι → ℝ) : Set (E × M) :=
  {p | p.1 ∈ orientedLevel f w r ∧ 0 ≤ p.2 ∧ Matrix.trace p.2 = 1 ∧ op p.2 p.1 = 0}

omit [Nonempty ν] [DecidableEq ι] in
lemma Admissible.levelFibre_compact {f : E → ι → ℝ} (hf : Admissible f)
    (w : E) (r : ι → ℝ) : IsCompact (levelFibre f w r) := by
  have hA : Continuous (fun p : E × M => op p.2) :=
    (op).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional.comp continuous_snd
  have he : levelFibre f w r = (orientedLevel f w r ×ˢ {Q : M | 0 ≤ Q ∧ Matrix.trace Q = 1}) ∩
      {p | op p.2 p.1 = 0} := by ext p; simp only [levelFibre,Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_prod,and_assoc]
  rw [he]
  exact ((hf.orientedLevel_compact w r).prod positive_slice_compact).inter_right
    (isClosed_eq (hA.clm_apply continuous_fst) continuous_const)

omit [Nonempty ν] in
lemma balancedFibre_mem {u : E} (hu : ‖u‖ = 1) {Q : M}
    (hQ : 0 ≤ Q) (htr : Matrix.trace Q = 1) (hQu : op Q u = 0) :
    ((1/2:ℝ) • rankOne u - (1/2:ℝ) • Q) ∈ traceSphere ν := by
  have hSA : IsSelfAdjoint ((1/2:ℝ) • rankOne u - (1/2:ℝ) • Q) :=
    ((IsSelfAdjoint.all (_:ℝ)).smul (rankOne_nonneg u).isSelfAdjoint).sub
      ((IsSelfAdjoint.all (_:ℝ)).smul hQ.isSelfAdjoint)
  refine ⟨hSA,?_⟩
  obtain ⟨hp,hn⟩ := rankOne_split_parts hQ hQu (show (0:ℝ) ≤ 1/2 by norm_num)
    (show (0:ℝ) ≤ 1/2 by norm_num)
  rw [← CFC.posPart_add_negPart _ hSA,hp,hn,Matrix.trace_add,Matrix.trace_smul,Matrix.trace_smul,
    rankOne_trace,hu,one_pow,htr]
  norm_num

end PurityGeometry
end BorsukNine

end OAI
