import Mathlib
import OAI.Geometry.Borsuk.MatrixGeometry.FibreContinuity
import OAI.Geometry.Borsuk.Projectors.FiniteOpenGlue

namespace OAI

namespace BorsukNine
open Set
lemma compact_target_hits {P X Y : Type*} [TopologicalSpace P] [CompactSpace P]
    [TopologicalSpace X] [TopologicalSpace Y] [T1Space Y]
    (φ : P → X) (hφ : Continuous φ) (K : ℝ × P → Y)
    (hK : ContinuousOn K (Icc (0:ℝ) 1 ×ˢ univ)) (y : Y) :
    IsCompact {x : X | ∃ p : P, φ p = x ∧ ∃ t ∈ Icc (0:ℝ) 1, K (t,p) = y} := by
  have hC : IsCompact ((Icc (0:ℝ) 1 ×ˢ (univ : Set P)) ∩ K ⁻¹' {y}) :=
    ((isCompact_Icc.prod isCompact_univ) : IsCompact (Icc (0:ℝ) 1 ×ˢ (univ : Set P))).of_isClosed_subset
      (hK.preimage_isClosed_of_isClosed (isClosed_Icc.prod isClosed_univ) isClosed_singleton) inter_subset_left
  have he : {x : X | ∃ p : P, φ p = x ∧ ∃ t ∈ Icc (0:ℝ) 1, K (t,p) = y} =
      (fun q : ℝ × P => φ q.2) '' ((Icc (0:ℝ) 1 ×ˢ (univ : Set P)) ∩ K ⁻¹' {y}) := by
    ext x
    constructor
    · rintro ⟨p,hp,t,ht,hk⟩
      exact ⟨(t,p),⟨⟨ht,mem_univ _⟩,hk⟩,hp⟩
    · rintro ⟨⟨t,p⟩,⟨⟨ht,-⟩,hk⟩,hp⟩
      exact ⟨p,hp,t,ht,hk⟩
  rw [he]
  exact hC.image (hφ.comp continuous_snd)
end BorsukNine

namespace BorsukNine
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
open Set
section LevelModel
variable {ν ι κ : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι] [DecidableEq ι] [Fintype κ]
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ

noncomputable def balancedModel {f : E → ι → ℝ} {w : E} {r : ι → ℝ}
    (p : levelFibre f w r) : traceSphere ν :=
  ⟨(1/2:ℝ) • rankOne p.val.1 - (1/2:ℝ) • p.val.2,
    balancedFibre_mem p.property.1.1 p.property.2.1 p.property.2.2.1 p.property.2.2.2⟩

omit [Fintype ι] [DecidableEq ι] in
omit [Nonempty ν] in
lemma balancedModel_continuous (f : E → ι → ℝ) (w : E) (r : ι → ℝ) :
    Continuous (balancedModel (f := f) (w := w) (r := r)) := by
  apply Continuous.subtype_mk
  change Continuous (fun p : levelFibre f w r => (1/2:ℝ) • rankOne p.val.1 - (1/2:ℝ) • p.val.2)
  exact ((continuous_const : Continuous (fun _ : levelFibre f w r => (1/2:ℝ))).smul
    (rankOne_continuous.comp continuous_subtype_val.fst)).sub
    ((continuous_const : Continuous (fun _ : levelFibre f w r => (1/2:ℝ))).smul continuous_subtype_val.snd)

noncomputable def modelChambers (f : E → ι → ℝ) (I : Finset ι) (w : E) (r : ι → ℝ)
    (c : κ → E) (j : κ) : Set (levelFibre f w r) :=
  {p | p.val.1 ∈ interior (signChamber (activeVectors f I) (c j))}

omit [Nonempty ν] [Fintype ι] [DecidableEq ι] [Fintype κ] in
lemma modelChambers_open (f : E → ι → ℝ) (I : Finset ι) (w : E) (r : ι → ℝ) (c : κ → E) (j : κ) :
    IsOpen (modelChambers f I w r c j) :=
  isOpen_interior.preimage continuous_subtype_val.fst

omit [Nonempty ν] [Fintype ι] [DecidableEq ι] [Fintype κ] in
lemma modelChambers_disjoint {f : E → ι → ℝ} {I : Finset ι} {w : E} {r : ι → ℝ} {c : κ → E}
    (hd : Pairwise (fun i j => Disjoint (interior (signChamber (activeVectors f I) (c i)))
      (interior (signChamber (activeVectors f I) (c j))))) :
    Pairwise (fun i j => Disjoint (modelChambers f I w r c i) (modelChambers f I w r c j)) := by
  intro i j hij
  exact Set.disjoint_left.mpr (fun p hp hq => Set.disjoint_left.mp (hd hij) hp hq)

omit [Nonempty ν] [Fintype ι] [DecidableEq ι] [Fintype κ] in
lemma modelChambers_cover {f : E → ι → ℝ} {I : Finset ι} {w : E} {r : ι → ℝ} {c : κ → E}
    (hc : orientedLevel f w r ⊆ ⋃ j, interior (signChamber (activeVectors f I) (c j))) :
    (⋃ j, modelChambers f I w r c j) = univ := by
  apply eq_univ_of_forall
  intro p
  obtain ⟨j,hj⟩ := mem_iUnion.mp (hc p.property.1)
  exact mem_iUnion.mpr ⟨j,hj⟩

noncomputable def levelHomotopy (f : E → ι → ℝ) (I : Finset ι) (w : E) (r : ι → ℝ)
    (c : κ → E) (g : κ → M → EuclideanSpace ℝ ↥(Iᶜ : Finset ι)) :
    ℝ × levelFibre f w r → EuclideanSpace ℝ ↥(Iᶜ : Finset ι) :=
  finiteOpenGlue (fun j => {p | p.2 ∈ modelChambers f I w r c j})
    (fun j p => fibreHomotopy f I (c j) (g j) p.1 p.2.val.1 p.2.val.2)

omit [Nonempty ν] in
lemma levelHomotopy_eq {f : E → ι → ℝ} {I : Finset ι} {w : E} {r : ι → ℝ} {c : κ → E}
    (hd : Pairwise (fun i j => Disjoint (interior (signChamber (activeVectors f I) (c i)))
      (interior (signChamber (activeVectors f I) (c j)))))
    (g : κ → M → EuclideanSpace ℝ ↥(Iᶜ : Finset ι)) {p : levelFibre f w r} {j : κ}
    (hp : p.val.1 ∈ interior (signChamber (activeVectors f I) (c j))) (t : ℝ) :
    levelHomotopy f I w r c g (t,p) = fibreHomotopy f I (c j) (g j) t p.val.1 p.val.2 := by
  apply finiteOpenGlue_eq
  · intro a b hab
    exact Set.disjoint_left.mpr (fun q ha hb => Set.disjoint_left.mp (hd hab) ha hb)
  · exact hp

lemma Admissible.levelHomotopy_continuousOn {f : E → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} (hI : I.Nonempty) {w : E} {r : ι → ℝ} (c : κ → E)
    (hc : ∀ j, c j ∈ commonPositiveCone f I) (hcn : ∀ j, ‖c j‖ = 1)
    (hd : Pairwise (fun i j => Disjoint (interior (signChamber (activeVectors f I) (c i)))
      (interior (signChamber (activeVectors f I) (c j)))))
    (hcover : orientedLevel f w r ⊆ ⋃ j, interior (signChamber (activeVectors f I) (c j)))
    (g : κ → M → EuclideanSpace ℝ ↥(Iᶜ : Finset ι)) (hg : ∀ j, Continuous (g j)) :
    ContinuousOn (levelHomotopy f I w r c g) (Icc (0:ℝ) 1 ×ˢ univ) := by
  rw [← modelChambers_cover hcover]
  apply finiteOpenGlue_continuousOn_prod (modelChambers_open f I w r c) (modelChambers_disjoint hd)
  intro j
  have hpar : Continuous (fun p : ℝ × levelFibre f w r => (p.1,p.2.val.1,p.2.val.2)) :=
    continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).fst.prodMk
      (continuous_subtype_val.comp continuous_snd).snd)
  have hmap : MapsTo (fun p : ℝ × levelFibre f w r => (p.1,p.2.val.1,p.2.val.2))
      (Icc (0:ℝ) 1 ×ˢ modelChambers f I w r c j)
      {p : ℝ × E × M | p.1 ∈ Icc 0 1 ∧ ‖p.2.1‖ = 1 ∧
        p.2.1 ∈ signChamber (activeVectors f I) (c j) ∧ p.2.2 ∈ matrixFibre p.2.1} :=
    fun p hp => ⟨hp.1,p.2.property.1.1,interior_subset hp.2,p.2.property.2⟩
  exact ContinuousOn.comp' (g := fun p : ℝ × E × M => fibreHomotopy f I (c j) (g j) p.1 p.2.1 p.2.2)
    (f := fun p : ℝ × levelFibre f w r => (p.1,p.2.val.1,p.2.val.2))
    (hf.fibreHomotopy_continuousOn hI (hc j) (hcn j) (g j) (hg j)) hpar.continuousOn hmap

lemma Admissible.level_hits_compact {f : E → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} (hI : I.Nonempty) {w : E} {r : ι → ℝ} (c : κ → E)
    (hc : ∀ j, c j ∈ commonPositiveCone f I) (hcn : ∀ j, ‖c j‖ = 1)
    (hd : Pairwise (fun i j => Disjoint (interior (signChamber (activeVectors f I) (c i)))
      (interior (signChamber (activeVectors f I) (c j)))))
    (hcover : orientedLevel f w r ⊆ ⋃ j, interior (signChamber (activeVectors f I) (c j)))
    (g : κ → M → EuclideanSpace ℝ ↥(Iᶜ : Finset ι)) (hg : ∀ j, Continuous (g j))
    (z : EuclideanSpace ℝ ↥(Iᶜ : Finset ι)) :
    IsCompact {A : traceSphere ν | ∃ p : levelFibre f w r, balancedModel p = A ∧
      ∃ t ∈ Icc (0:ℝ) 1, levelHomotopy f I w r c g (t,p) = z} := by
  let : CompactSpace (levelFibre f w r) := isCompact_iff_compactSpace.mp (hf.levelFibre_compact w r)
  exact compact_target_hits balancedModel (balancedModel_continuous f w r)
    (levelHomotopy f I w r c g) (hf.levelHomotopy_continuousOn hI c hc hcn hd hcover g hg) z

end LevelModel
end BorsukNine

end OAI
