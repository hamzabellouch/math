import OAI.Computability.BinPacking.PCP.FinalConstants

namespace OAI

namespace BinPackingGames.Foundations.PCP.PreprocessingTables

open PreprocessingRegularTables

abbrev BaseTable := PreprocessingRegularTables.BaseTable

def degree : Nat := 2 * ((internalDegree + 1) + internalDegree)

theorem degree_eq : degree = Preprocessing.degree := by
  unfold degree internalDegree Preprocessing.degree
  rw [pow_two]
  omega

def regularVertices (t : GraphTables.Table) : Nat := vertexCount t (padding t)
def vertices (t : GraphTables.Table) : Nat := PreprocessingLevels.paddedSize (regularVertices t)

def padded (H : BaseTable) (t : GraphTables.Table) :
    PortTables.Table (vertices t) (internalDegree + 1) :=
  PreprocessingPaddingTables.pad (regularize H t)
    (PreprocessingLevels.le_paddedSize (regularVertices t))

def overlayFamily (H : BaseTable) (t : GraphTables.Table) :
    ExpanderTables.Table (vertices t) internalDegree :=
  resizeTable (PreprocessingLevels.table_vertexCount_eq_paddedSize (regularVertices t))
    (ExpanderTables.family H (PreprocessingLevels.boundedLevel (regularVertices t)))

def preprocess (H : BaseTable) (t : GraphTables.Table) :
    PortTables.Table (vertices t) degree :=
  PreprocessingOverlayTables.lazy
    (PreprocessingOverlayTables.overlay (padded H t) (overlayFamily H t))

def output (H : BaseTable) (t : GraphTables.Table) : PortTables.Input degree :=
  ⟨vertices t, preprocess H t⟩

def graphTable (H : BaseTable) (t : GraphTables.Table) : GraphTables.Table :=
  PortTables.graphTable (preprocess H t)

def outputBits (H : BaseTable) (t : GraphTables.Table) : List Bool :=
  PortTables.tableBits (preprocess H t)

theorem regularVertices_ge_darts (t : GraphTables.Table) : t.darts ≤ regularVertices t := by
  change t.darts ≤ t.darts + _
  omega

theorem regularVertices_le (t : GraphTables.Table) :
    regularVertices t ≤ ExpanderFamily.growth * t.darts := vertexCount_le t

theorem vertices_positive (t : GraphTables.Table) : 0 < vertices t :=
  PreprocessingLevels.paddedSize_positive _

theorem vertices_le_of_positive (t : GraphTables.Table) (ht : 0 < t.darts) :
    vertices t ≤ ExpanderFamily.growth ^ 2 * t.darts := by
  have hr : 0 < regularVertices t := ht.trans_le (regularVertices_ge_darts t)
  calc
    _ ≤ ExpanderFamily.growth * regularVertices t :=
      (PreprocessingLevels.paddedSize_bounds hr).2
    _ ≤ ExpanderFamily.growth * (ExpanderFamily.growth * t.darts) :=
      Nat.mul_le_mul_left _ (regularVertices_le t)
    _ = _ := by ring

theorem vertices_eq_one_of_no_darts (t : GraphTables.Table) (ht : t.darts = 0) :
    vertices t = 1 := by
  unfold vertices regularVertices
  rw [vertexCount_eq_zero_of_no_darts t ht, PreprocessingLevels.paddedSize_zero]

theorem vertices_le (t : GraphTables.Table) :
    vertices t ≤ ExpanderFamily.growth ^ 2 * (t.darts + 1) := by
  by_cases ht : t.darts = 0
  · rw [vertices_eq_one_of_no_darts t ht, ht]
    have hg : 0 < ExpanderFamily.growth := Nat.zero_lt_one.trans ExpanderFamily.growth_gt_one
    have hp : 0 < ExpanderFamily.growth ^ 2 := Nat.pow_pos hg
    simpa using Nat.succ_le_of_lt hp
  · exact (vertices_le_of_positive t (Nat.pos_of_ne_zero ht)).trans
      (Nat.mul_le_mul_left _ (Nat.le_succ _))

theorem darts_eq (H : BaseTable) (t : GraphTables.Table) :
    (graphTable H t).darts = vertices t * degree := rfl

theorem darts_le (H : BaseTable) (t : GraphTables.Table) :
    (graphTable H t).darts ≤ Preprocessing.sizeFactor * (t.darts + 1) := by
  rw [darts_eq]
  calc
    _ ≤ (ExpanderFamily.growth ^ 2 * (t.darts + 1)) * degree :=
      Nat.mul_le_mul_right _ (vertices_le t)
    _ = _ := by rw [degree_eq]; unfold Preprocessing.sizeFactor; ring

theorem vertices_le_inputBits (t : GraphTables.Table) :
    vertices t ≤ ExpanderFamily.growth ^ 2 * ((GraphTables.tableBits t).length + 1) :=
  (vertices_le t).trans (Nat.mul_le_mul_left _
    (Nat.add_le_add_right (GraphTables.darts_le_tableBits_length t) 1))

theorem darts_le_inputBits (H : BaseTable) (t : GraphTables.Table) :
    (graphTable H t).darts ≤
      Preprocessing.sizeFactor * ((GraphTables.tableBits t).length + 1) :=
  (darts_le H t).trans (Nat.mul_le_mul_left _
    (Nat.add_le_add_right (GraphTables.darts_le_tableBits_length t) 1))

end BinPackingGames.Foundations.PCP.PreprocessingTables

namespace BinPackingGames.Foundations.PCP.PreprocessingStageMaps
open PreprocessingRegularTables

abbrev BaseTable := PreprocessingTables.BaseTable

def regular (H : BaseTable) (t : GraphTables.Table) : PortTables.Input (internalDegree + 1) :=
  ⟨vertexCount t (PreprocessingRegularTables.padding t), regularize H t⟩

def padding (d : Nat) (input : PortTables.Input d) : PortTables.Input d :=
  ⟨PreprocessingLevels.paddedSize input.1,
    PreprocessingPaddingTables.pad input.2 (PreprocessingLevels.le_paddedSize input.1)⟩

def familyAt (H : BaseTable) (n : Nat) :
    ExpanderTables.Table (PreprocessingLevels.paddedSize n) internalDegree :=
  resizeTable (PreprocessingLevels.table_vertexCount_eq_paddedSize n)
    (ExpanderTables.family H (PreprocessingLevels.boundedLevel n))

def paddedOverlay (H : BaseTable) (d : Nat) (input : PortTables.Input d) :
    PortTables.Input (d + internalDegree) :=
  ⟨PreprocessingLevels.paddedSize input.1,
    PreprocessingOverlayTables.overlay (padding d input).2 (familyAt H input.1)⟩

def lazy (d : Nat) (input : PortTables.Input d) : PortTables.Input (2 * d) :=
  ⟨input.1, PreprocessingOverlayTables.lazy input.2⟩

theorem output_eq (H : BaseTable) (t : GraphTables.Table) :
    PreprocessingTables.output H t =
      lazy ((internalDegree + 1) + internalDegree)
        (paddedOverlay H (internalDegree + 1) (regular H t)) := rfl

end BinPackingGames.Foundations.PCP.PreprocessingStageMaps

noncomputable section

namespace BinPackingGames.Foundations.PCP.PreprocessingGuarantees

open PoweringWalks SpectralReturn PreprocessingTables
open PreprocessingRegularTables (internalDegree regularize)

variable {n d e : Nat}

theorem overlay_rejectionCount (G : PortTables.Table n d) (H : ExpanderTables.Table n e)
    (labels : Fin n → GraphTables.Label) :
    (PortTables.baseGraph (PreprocessingOverlayTables.overlay G H)).rejectionCount labels =
      (PortTables.baseGraph G).rejectionCount labels := by
  rw [PreprocessingOverlayTables.overlay_semantics]
  calc
    _ = (Overlay.constraintGraph (PortTables.baseGraph G) (ExpanderTables.graph H)).rejectionCount labels := by
      convert ConstraintGraph.reindex_rejectionCount
        (Overlay.constraintGraph (PortTables.baseGraph G) (ExpanderTables.graph H))
        (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _)
          (PreprocessingOverlayTables.overlayPorts d e)) (Equiv.refl _) labels using 1
      rfl
    _ = _ := Overlay.rejectionCount_eq _ _ rfl labels

theorem lazy_rejectionCount (G : PortTables.Table n d)
    (labels : Fin n → GraphTables.Label) :
    (PortTables.baseGraph (PreprocessingOverlayTables.lazy G)).rejectionCount labels =
      (PortTables.baseGraph G).rejectionCount labels := by
  rw [PreprocessingOverlayTables.lazy_semantics]
  calc
    _ = (LazyConstraint.constraintGraph (PortTables.baseGraph G)).rejectionCount labels := by
      convert ConstraintGraph.reindex_rejectionCount
        (LazyConstraint.constraintGraph (PortTables.baseGraph G))
        (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _)
          (PreprocessingOverlayTables.lazyPorts d)) (Equiv.refl _) labels using 1
      rfl
    _ = _ := LazyConstraint.rejectionCount_eq _ rfl labels

theorem overlayFamily_certificate (H : BaseTable)
    (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (t : GraphTables.Table) :
    SpectralCertificate (ExpanderTables.graph (overlayFamily H t)) (1 / 2 : ℝ) := by
  let : NeZero Expanders.baseDegree := ⟨PreprocessingRegularSoundness.baseDegree_ne_zero⟩
  apply PreprocessingRegularSoundness.resizeTable_certificate
  exact ExpanderTables.family_certificate H certificate _

theorem overlay_certificate (H : BaseTable)
    (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (t : GraphTables.Table) :
    SpectralCertificate (PortTables.portGraph
      (PreprocessingOverlayTables.overlay (padded H t) (overlayFamily H t))) (7 / 8 : ℝ) :=
  PreprocessingTableSpectral.overlay_certificate_seven_eighths _ _
    (vertices_positive t) rfl PreprocessingRegularSoundness.internalDegree_ge_eight
    (overlayFamily_certificate H certificate t)

theorem spectral_certificate (H : BaseTable)
    (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (t : GraphTables.Table) :
    SpectralCertificate (PortTables.portGraph (preprocess H t)) (31 / 32 : ℝ) := by
  apply PreprocessingTableSpectral.lazy_certificate_31_32
  · omega
  · exact overlay_certificate H certificate t

def restrictedLabel (t : GraphTables.Table)
    (labels : Fin (vertices t) → GraphTables.Label) :
    Fin (regularVertices t) → GraphTables.Label :=
  fun v => labels (v.castLE (PreprocessingLevels.le_paddedSize (regularVertices t)))

theorem rejectionCount_eq_regularized (H : BaseTable) (t : GraphTables.Table)
    (labels : Fin (vertices t) → GraphTables.Label) :
    (PortTables.baseGraph (preprocess H t)).rejectionCount labels =
      (PortTables.baseGraph (regularize H t)).rejectionCount (restrictedLabel t labels) := by
  unfold preprocess PreprocessingTables.degree
  rw [lazy_rejectionCount, overlay_rejectionCount]
  exact PreprocessingPaddingTables.pad_rejectionCount _ _ labels

def roundLabels (t : GraphTables.Table)
    (labels : Fin (vertices t) → GraphTables.Label) : Fin t.vertices → GraphTables.Label :=
  PreprocessingRegularSoundness.roundLabels t (restrictedLabel t labels)

theorem soundness (H : BaseTable)
    (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (t : GraphTables.Table) (labels : Fin (vertices t) → GraphTables.Label) :
    (GraphTables.semantics t).rejectionCount (roundLabels t labels) ≤
      (PortTables.baseGraph (preprocess H t)).rejectionCount labels := by
  rw [rejectionCount_eq_regularized]
  exact PreprocessingRegularSoundness.soundness H certificate t (restrictedLabel t labels)

theorem completeness (H : BaseTable) (t : GraphTables.Table)
    (h : (GraphTables.semantics t).Satisfiable) :
    (PortTables.baseGraph (preprocess H t)).Satisfiable := by
  have hp : (PortTables.baseGraph (padded H t)).Satisfiable :=
    (PreprocessingPaddingTables.pad_satisfiable_iff _ _).mpr
      (PreprocessingRegularSoundness.completeness H t h)
  obtain ⟨labels, hlabels⟩ := hp
  refine ⟨labels, ?_⟩
  apply (ConstraintGraph.rejectionCount_eq_zero_iff _ labels).mp
  unfold preprocess PreprocessingTables.degree
  rw [lazy_rejectionCount, overlay_rejectionCount]
  exact (ConstraintGraph.rejectionCount_eq_zero_iff _ labels).mpr hlabels

theorem gap_transfer_real (H : BaseTable)
    (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (t : GraphTables.Table) (ht : 0 < t.darts)
    (epsilon : ℝ) (he : 0 ≤ epsilon)
    (lower : ∀ labels : Fin t.vertices → GraphTables.Label,
      epsilon * t.darts ≤ ((GraphTables.semantics t).rejectionCount labels : ℝ))
    (labels : Fin (vertices t) → GraphTables.Label) :
    (epsilon / Preprocessing.sizeFactor) *
        Fintype.card (Fin (vertices t) × Fin PreprocessingTables.degree) ≤
      ((PortTables.baseGraph (preprocess H t)).rejectionCount labels : ℝ) := by
  have hs : (0 : ℝ) < Preprocessing.sizeFactor :=
    Nat.cast_pos.mpr Preprocessing.sizeFactor_positive
  have hcount : Fintype.card (Fin (vertices t) × Fin PreprocessingTables.degree) ≤
      Preprocessing.sizeFactor * t.darts := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    calc
      _ ≤ (ExpanderFamily.growth ^ 2 * t.darts) * PreprocessingTables.degree :=
        Nat.mul_le_mul_right _ (vertices_le_of_positive t ht)
      _ = _ := by rw [PreprocessingTables.degree_eq]; unfold Preprocessing.sizeFactor; ring
  have hcountR : (Fintype.card (Fin (vertices t) × Fin PreprocessingTables.degree) : ℝ) ≤
      (Preprocessing.sizeFactor : ℝ) * t.darts := by exact_mod_cast hcount
  calc
    _ ≤ (epsilon / Preprocessing.sizeFactor) *
        ((Preprocessing.sizeFactor : ℝ) * t.darts) :=
      mul_le_mul_of_nonneg_left hcountR (div_nonneg he hs.le)
    _ = epsilon * t.darts := by field_simp
    _ ≤ ((GraphTables.semantics t).rejectionCount (roundLabels t labels) : ℝ) := lower _
    _ ≤ _ := Nat.cast_le.mpr (soundness H certificate t labels)

end BinPackingGames.Foundations.PCP.PreprocessingGuarantees

end

end OAI
