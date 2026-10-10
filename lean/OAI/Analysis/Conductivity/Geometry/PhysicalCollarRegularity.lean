import Mathlib
import OAI.Analysis.Conductivity.Geometry.RegularPatch
import OAI.Analysis.Conductivity.Variational.FiniteEndPhysicalRegularity
import OAI.Analysis.Conductivity.Flux.FiniteEndPhysicalSmoothTensor
import OAI.Analysis.Conductivity.Flux.VariableCollarTensor

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

def variableFaceField (u : Coord3 → Fin 2 → ℝ) (a b : ℝ) (i j : Fin 4) : Coord3 → Fin 2 → ℝ :=
  fun y => u (flatEndCoordinates a b (sourceFaceAngles i j (sourceCollarInverse i j y)))

def variableCollarField (u : Coord3 → Fin 2 → ℝ) (a b : ℝ) : Coord3 → Fin 2 → ℝ :=
  sourceFacePaste (variableFaceField u a b) 0

lemma variableCollarField_open (u : Coord3 → Fin 2 → ℝ) (a b : ℝ)
    (i j : Fin 4) {x : Coord3} (hx : x∈sourceCollarOpenBox) :
    variableCollarField u a b (sourceCollarPiece i j x)=
      u (flatEndCoordinates a b (sourceFaceAngles i j x)) := by
  rw [variableCollarField,sourceFacePaste_open _ _ i j hx]
  simp only [variableFaceField,sourceCollarInverse_point i j hx]

lemma flatEndCoordinates_fderiv_surjective {a : ℝ} (ha : a≠0) (b : ℝ) (x : Coord3) :
    Function.Surjective (fderiv ℝ (flatEndCoordinates a b) x) := by
  change Function.Surjective (fderiv ℝ (endAxialAffine a b) x)
  rw [(endAxialAffine_hasFDeriv a b x).fderiv]
  exact (LinearMap.equivOfDetNeZero (Matrix.toLin' (endAxialMatrix a)) (by
    simpa [LinearMap.det_toLin',endAxialMatrix,Matrix.det_diagonal,Fin.prod_univ_succ] using ha)).surjective

lemma sourceFaceAngles_fderiv_surjective (i j : Fin 4) {x : Coord3}
    (hx : x∈sourceCollarOpenBox) : Function.Surjective (fderiv ℝ (sourceFaceAngles i j) x) := by
  rw [(sourceFaceAngles_hasFDeriv i j x).fderiv]
  exact (LinearMap.equivOfDetNeZero (Matrix.toLin' (sourceFaceAngleMatrix i j x)) (by
    rw [LinearMap.det_toLin']; exact (sourceFaceAngleMatrix_det_pos i j (sourceCollarOpenBox_subset hx)).ne')).surjective

lemma variableCollarTensor_local_eq (K : Coord3 → Mat3) (a b : ℝ)
    (i j : Fin 4) {x : Coord3} (hx : x∈sourceCollarOpenBox) :
    variableCollarTensor K a b =ᶠ[𝓝 (sourceCollarPiece i j x)]
      (attachedVariableTensor (K ∘ flatEndCoordinates a b ∘ sourceFaceAngles i j) a i j ∘ sourceCollarInverse i j) := by
  change ∀ᶠ y in 𝓝 (sourceCollarPiece i j x), _ = _
  rw [←sourceCollarPiece_map_nhds i j hx,eventually_map]
  filter_upwards [isOpen_sourceCollarOpenBox.mem_nhds hx] with y hy
  simpa only [Function.comp_def,sourceCollarInverse_point i j hy] using
    variableCollarTensor_open K a b i j hy

lemma variableCollarTensor_smooth_at {K : Coord3 → Mat3} {a : ℝ} (ha : a≠0) (b : ℝ)
    (i j : Fin 4) {x : Coord3} (hx : x∈sourceCollarOpenBox)
    (hK : ContDiffAt ℝ (↑(⊤:ℕ∞)) K (flatEndCoordinates a b (sourceFaceAngles i j x))) :
    ContDiffAt ℝ (↑(⊤:ℕ∞)) (variableCollarTensor K a b) (sourceCollarPiece i j x) := by
  have hk : ContDiffAt ℝ (↑(⊤:ℕ∞)) (K ∘ flatEndCoordinates a b ∘ sourceFaceAngles i j) x :=
    hK.comp x ((contDiff_flatEndCoordinates a b).contDiffAt.comp x
      (contDiff_sourceFaceAngles i j).contDiffAt)
  have ht : ContDiffAt ℝ (↑(⊤:ℕ∞))
      (attachedVariableTensor (K ∘ flatEndCoordinates a b ∘ sourceFaceAngles i j) a i j)
      (sourceCollarInverse i j (sourceCollarPiece i j x)) := by
    rw [sourceCollarInverse_point i j hx]
    exact contDiffAt_attachedVariableTensor hk ha i j hx
  exact (ht.comp _ (sourceCollarInverse_contDiffAt i j hx)).congr_of_eventuallyEq
    (variableCollarTensor_local_eq K a b i j hx)

theorem variableCollar_regular_at {u : Coord3 → Fin 2 → ℝ} {K : Coord3 → Mat3}
    (hS : ∀ x,(K x).IsSymm) {a : ℝ} (ha : a≠0) (b : ℝ)
    (i j : Fin 4) {x : Coord3} (hx : x∈sourceCollarOpenBox) {U : Set Coord3}
    (hr : flatEndCoordinates a b (sourceFaceAngles i j x)∈
      regularRegion u (fun y => ⟨K y,hS y⟩) U) :
    sourceCollarPiece i j x∈regularRegion (variableCollarField u a b)
      (fun y => ⟨variableCollarTensor K a b y,variableCollarTensor_symm hS a b y⟩)
      (sourceCollarPiece i j '' sourceCollarOpenBox) := by
  obtain ⟨O,hOU,hO,hxO⟩ := mem_regularRegion_iff.mp hr
  let V := sourceCollarPiece i j '' sourceCollarOpenBox
  let g : Coord3 → Coord3 := fun y => flatEndCoordinates a b (sourceFaceAngles i j (sourceCollarInverse i j y))
  have hV : IsOpen V := isOpen_sourceCollarOpenImage i j
  have hg : ContDiffOn ℝ (↑(⊤:ℕ∞)) g V :=
    (contDiff_flatEndCoordinates a b).comp_contDiffOn
      ((contDiff_sourceFaceAngles i j).comp_contDiffOn (sourceCollarInverse_contDiffOn i j))
  let W := V∩g ⁻¹' O
  have hW : IsOpen W := hg.continuousOn.isOpen_inter_preimage hV hO.1
  have hm : MapsTo g W O := fun _ hy => hy.2
  have hd : ∀ y∈W,Function.Surjective (fderiv ℝ g y) := by
    rintro y ⟨⟨z,hz,rfl⟩,_⟩
    have hinv := (sourceCollarInverse_contDiffAt i j hz).differentiableAt (by simp)
    have hang := (contDiff_sourceFaceAngles i j).differentiable (by simp)
    have hflat := (contDiff_flatEndCoordinates a b).differentiable (by simp)
    change Function.Surjective (fderiv ℝ (flatEndCoordinates a b ∘ (sourceFaceAngles i j ∘ sourceCollarInverse i j)) _)
    rw [fderiv_comp _ (hflat _) ((hang _).comp _ hinv),fderiv_comp _ (hang _) hinv]
    have hsur : Function.Surjective (fderiv ℝ (sourceFaceAngles i j)
        (sourceCollarInverse i j (sourceCollarPiece i j z))) := by
      simpa only [sourceCollarInverse_point i j hz] using sourceFaceAngles_fderiv_surjective i j hz
    exact (flatEndCoordinates_fderiv_surjective ha b _).comp
      (hsur.comp (sourceCollarInverse_fderiv_surjective i j ⟨z,hz,rfl⟩))
  have hB : ContDiffOn ℝ (↑(⊤:ℕ∞)) (variableCollarTensor K a b) W := by
    rintro y hy
    obtain ⟨z,hz,rfl⟩ := hy.1
    apply (variableCollarTensor_smooth_at ha b i j hz ?_).contDiffWithinAt
    have hgz : g (sourceCollarPiece i j z)=flatEndCoordinates a b (sourceFaceAngles i j z) := by
      simp only [g,sourceCollarInverse_point i j hz]
    simpa only [hgz] using (hO.2.2.1 _ hy.2).contDiffAt (hO.1.mem_nhds hy.2)
  have hp : RegularPatch (fun y => u (g y))
      (fun y => ⟨variableCollarTensor K a b y,variableCollarTensor_symm hS a b y⟩) W :=
    ⟨hW,hO.2.1.comp (hg.mono inter_subset_left) hm,hB,
      hO.2.2.2.smoothCoordinates hO.1 hW hO.2.1 (hg.mono inter_subset_left) hm hd⟩
  have hc : EqOn (variableCollarField u a b) (fun y => u (g y)) W := by
    rintro y ⟨⟨z,hz,rfl⟩,_⟩
    simpa only [g,sourceCollarInverse_point i j hz] using variableCollarField_open u a b i j hz
  refine mem_regularRegion_iff.mpr ⟨W,inter_subset_left,hp.congr hc (fun _ _ => rfl),?_⟩
  refine ⟨⟨x,hx,rfl⟩,?_⟩
  change g (sourceCollarPiece i j x)∈O
  simpa only [g,sourceCollarInverse_point i j hx] using hxO

end ScalarConductivity

end
end

end OAI
