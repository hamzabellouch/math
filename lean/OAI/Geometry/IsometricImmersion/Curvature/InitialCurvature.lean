import OAI.Geometry.IsometricImmersion.Assembly.AssemblyProfiles
import OAI.Geometry.IsometricImmersion.Assembly.DiagonalAmplitudes

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Set Filter

namespace SmoothLocal.Geometry
open SmoothLocal.Model

def initialCurvatureBudget : ℝ := 1 / 2000

theorem initialCurvatureBudget_pos : 0 < initialCurvatureBudget := by
  norm_num [initialCurvatureBudget]

def initialCurvatureAmplitudes : ℕ → ℝ :=
  Classical.choose (exists_positive_diagonal_amplitudes enumeratedAssemblyProfile
    enumeratedAssemblyProfile_contDiff enumeratedAssemblyProfile_hasCompactSupport
    initialCurvatureBudget initialCurvatureBudget_pos)

theorem initialCurvatureAmplitudes_pos (j : ℕ) : 0 < initialCurvatureAmplitudes j :=
  (Classical.choose_spec (exists_positive_diagonal_amplitudes enumeratedAssemblyProfile
    enumeratedAssemblyProfile_contDiff enumeratedAssemblyProfile_hasCompactSupport
    initialCurvatureBudget initialCurvatureBudget_pos)).1 j

def initialCurvatureTerm (j : ℕ) (p : Coord) : ℝ :=
  initialCurvatureAmplitudes j • enumeratedAssemblyProfile j p

theorem initialCurvatureTerm_derivative_bound (j k : ℕ) (hkj : k ≤ j) (p : Coord) :
    ‖iteratedFDeriv ℝ k (initialCurvatureTerm j) p‖ ≤ patchSeriesWeight initialCurvatureBudget j :=
  (Classical.choose_spec (exists_positive_diagonal_amplitudes enumeratedAssemblyProfile
    enumeratedAssemblyProfile_contDiff enumeratedAssemblyProfile_hasCompactSupport
    initialCurvatureBudget initialCurvatureBudget_pos)).2 j k hkj p

theorem initialCurvatureTerm_contDiff (j : ℕ) : ContDiff ℝ ∞ (initialCurvatureTerm j) :=
  (enumeratedAssemblyProfile_contDiff j).const_smul (initialCurvatureAmplitudes j)

theorem initialCurvatureTerm_tsupport (j : ℕ) :
    tsupport (initialCurvatureTerm j) = tsupport (enumeratedAssemblyProfile j) :=
  tsupport_const_smul_eq_of_pos _ (initialCurvatureAmplitudes_pos j)

theorem initialCurvatureTerm_hasCompactSupport (j : ℕ) :
    HasCompactSupport (initialCurvatureTerm j) := by
  change IsCompact (tsupport (initialCurvatureTerm j))
  rw [initialCurvatureTerm_tsupport]
  exact enumeratedAssemblyProfile_hasCompactSupport j

def initialCurvature : Coord → ℝ := flatPatchSum initialCurvatureTerm

theorem initialCurvature_summable (p : Coord) : Summable (fun j => initialCurvatureTerm j p) :=
  flatPatchSum_summable _ initialCurvatureBudget initialCurvatureTerm_derivative_bound p

theorem initialCurvature_contDiff : ContDiff ℝ ∞ initialCurvature :=
  flatPatchSum_contDiff _ initialCurvatureBudget initialCurvatureTerm_contDiff
    initialCurvatureTerm_hasCompactSupport initialCurvatureTerm_derivative_bound

theorem initialCurvature_abs_le (p : Coord) : |initialCurvature p| ≤ 1 / 2000 := by
  simpa only [Real.norm_eq_abs, initialCurvature, initialCurvatureBudget] using
    flatPatchSum_norm_le initialCurvatureTerm
    initialCurvatureBudget initialCurvatureTerm_derivative_bound p

theorem initialCurvature_small (p : Coord) : |initialCurvature p| ≤ 1 / 1000 := by
  linarith [initialCurvature_abs_le p]

theorem initialCurvature_all_jets_zero (k : ℕ) :
    iteratedFDeriv ℝ k initialCurvature (0 : Coord) = 0 := by
  apply flatPatchSum_all_jets_zero _ initialCurvatureBudget initialCurvatureTerm_contDiff
    initialCurvatureTerm_hasCompactSupport initialCurvatureTerm_derivative_bound _ k
  intro j
  rw [initialCurvatureTerm_tsupport]
  exact zero_not_mem_enumeratedAssemblyProfile_tsupport j

theorem initialCurvature_eq_profile (i : AssemblyProfileIndex) {p : Coord}
    (hp : p ∈ assemblyCarrier i) : initialCurvature p =
      initialCurvatureAmplitudes (Encodable.encode i) * assemblyProfile i p := by
  change (∑' j, initialCurvatureTerm j p) = _
  rw [tsum_eq_single (Encodable.encode i)]
  · simp only [initialCurvatureTerm, enumeratedAssemblyProfile_encode, smul_eq_mul]
  · intro j hj
    simp only [initialCurvatureTerm, enumeratedAssemblyProfile_zero_other i hp hj, smul_zero]

theorem initialCurvature_negative_on_disk_interior (n : ℕ) {p : Coord}
    (hp : p ∈ interior (accumulatingDisk n)) : initialCurvature p < 0 := by
  rw [initialCurvature_eq_profile (Sum.inl n) (interior_subset hp)]
  exact mul_neg_of_pos_of_neg (initialCurvatureAmplitudes_pos _)
    (accumulatingDiskProfile_neg_interior n hp)

theorem initialCurvature_zero_on_disk_frontier (n : ℕ) {p : Coord}
    (hp : p ∈ frontier (accumulatingDisk n)) : initialCurvature p = 0 := by
  have hdisk : p ∈ accumulatingDisk n := by
    simpa only [(accumulatingDisk_isCompact n).isClosed.closure_eq] using frontier_subset_closure hp
  rw [initialCurvature_eq_profile (Sum.inl n) hdisk]
  change _ * accumulatingDiskProfile n p = 0
  rw [accumulatingDiskProfile_frontier_zero n hp, mul_zero]

def initialPatchAmplitude (n k : ℕ) (R : OrientationLabel) (c : Coord)
    (hc : c ∈ orientedExteriorCenters n k R) : ℝ :=
  initialCurvatureAmplitudes (Encodable.encode (Sum.inr ⟨n, k, R, c, hc⟩ : AssemblyProfileIndex))

theorem initialPatchAmplitude_pos (n k : ℕ) (R : OrientationLabel) (c : Coord)
    (hc : c ∈ orientedExteriorCenters n k R) : 0 < initialPatchAmplitude n k R c hc :=
  initialCurvatureAmplitudes_pos _

theorem initialCurvature_model_on_patch (n k : ℕ) (R : OrientationLabel) (c : Coord)
    (hc : c ∈ orientedExteriorCenters n k R) {q : Coord} (hq : ‖q‖ ≤ 13 / 4) :
    initialCurvature (affineCoordinates c (orientedPatchScale n k R • R.val) q) =
      initialPatchAmplitude n k R c hc * ((q 0) ^ 2 - modelProfile (q 1)) := by
  have hbox : q ∈ closedPatchBox := (mem_closedPatchBox_iff_norm_le q).mpr (by linarith)
  have hcarrier : affineCoordinates c (orientedPatchScale n k R • R.val) q ∈
      assemblyCarrier (Sum.inr ⟨n, k, R, c, hc⟩) := ⟨q, hbox, rfl⟩
  rw [initialCurvature_eq_profile (Sum.inr ⟨n, k, R, c, hc⟩) hcarrier]
  change initialPatchAmplitude n k R c hc *
    localPatchProfile (affineInverseCoordinates c (orientedPatchScale n k R • R.val)
      (affineCoordinates c (orientedPatchScale n k R • R.val) q)) = _
  rw [affineInverseCoordinates_affineCoordinates c _ (orientedPatchMatrix_isUnit n k R),
    localPatchProfile_eq_model hq]

end SmoothLocal.Geometry

end

end OAI
