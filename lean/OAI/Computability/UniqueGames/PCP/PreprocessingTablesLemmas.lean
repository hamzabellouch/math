import OAI.Computability.UniqueGames.Machines.MachineLemmas
import OAI.Computability.UniqueGames.PCP.AlphabetGraphLemmas
import OAI.Computability.UniqueGames.PCP.AlphabetReductionLemmas
import OAI.Computability.UniqueGames.PCP.ExpanderRowControlLemmas
import OAI.Computability.UniqueGames.PCP.FinalConstantsLemmas
import OAI.Computability.UniqueGames.PCP.PoweringTableSemanticsLemmas
import OAI.Computability.UniqueGames.PCP.Preprocessing
import OAI.Computability.UniqueGames.PCP.PreprocessingOverlayTables
import OAI.Computability.UniqueGames.PCP.PreprocessingPaddingOffsets
import OAI.Computability.UniqueGames.PCP.PreprocessingPaddingTables
import OAI.Computability.UniqueGames.PCP.PreprocessingRegularSoundness
import OAI.Computability.UniqueGames.PCP.PreprocessingRegularTablesLemmas
import OAI.Computability.UniqueGames.PCP.PreprocessingTableSpectral

namespace OAI

section

/-!
# Concrete preprocessing table algorithm

Given one fixed expander base table, this function computes regularized
cloud rows, pads the whole vertex set, overlays a stored family table, and
adds the half-lazy rows. It is total even on zero-dart input tables. The
bounds below concern actual output data; an actual TM2 execution certificate
is a separate theorem and is not inferred from these size bounds.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingTables

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

/-- The total algorithm also has a uniform data bound on empty inputs. -/
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

end UniqueGamesTheorem.Foundations.PCP.PreprocessingTables

end

section

/-! Soundness and expansion of the actual executable preprocessing tables.
The fixed base-table spectral certificate is supplied by the proved expander
existence theorem; no output expansion or output gap is assumed. -/

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingGuarantees

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

/-- The concrete generated rows have the required absolute contraction. -/
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

end UniqueGamesTheorem.Foundations.PCP.PreprocessingGuarantees

end

end

section

/-! Bounds on actual metadata, stored rotor words, and emitted prefixes. These
are size estimates used inside separately proved machine executions. -/
namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingMachineBounds
open PreprocessingRegularTables PreprocessingCloudIndex
open UniqueGamesTheorem.Foundations.Complexity
open scoped BigOperators

def inputLength (t : GraphTables.Table) : Nat := (GraphTables.tableBits t).length

theorem cloudSize_le_input (t : GraphTables.Table) (v : Fin t.vertices) :
    cloudSize t v ≤ inputLength t :=
  (cloudSize_le_darts t v).trans (GraphTables.darts_le_tableBits_length t)

theorem cloudTotal_le_input (t : GraphTables.Table) (v : Fin t.vertices) :
    cloudSize t v + padding t v ≤ ExpanderFamily.growth * inputLength t := by
  rw [cloudSize_add_padding]
  exact (PreprocessingLevels.cloudPaddedSize_bounds _).2.trans
    (Nat.mul_le_mul_left _ (cloudSize_le_input t v))

theorem level_le_input (t : GraphTables.Table) (v : Fin t.vertices) :
    PreprocessingLevels.boundedLevel (cloudSize t v) ≤ inputLength t :=
  (PreprocessingLevels.boundedLevel_le_input _).trans (cloudSize_le_input t v)

theorem regularVertices_le_input (t : GraphTables.Table) :
    vertexCount t (padding t) ≤ ExpanderFamily.growth * inputLength t :=
  (vertexCount_le t).trans
    (Nat.mul_le_mul_left _ (GraphTables.darts_le_tableBits_length t))

theorem offset_le_sum {n : Nat} (p : Fin n → Nat) (k : Nat) :
    PreprocessingPaddingOffsets.offset p k ≤ ∑ v, p v := by
  have hfull : (List.finRange n).take n = List.finRange n := by simp
  have hsplit : PreprocessingPaddingOffsets.offset p k +
      (((List.finRange n).drop k).map p).sum =
      PreprocessingPaddingOffsets.offset p n := by
    simp only [PreprocessingPaddingOffsets.offset, hfull]
    rw [← List.sum_append, ← List.map_append, List.take_append_drop]
  rw [PreprocessingPaddingOffsets.offset_all] at hsplit
  omega

theorem prefix_le_input (t : GraphTables.Table) (k : Nat) :
    PreprocessingPaddingOffsets.offset (padding t) k ≤
      ExpanderFamily.growth * inputLength t := by
  have hsum : (∑ v, padding t v) ≤ vertexCount t (padding t) := by
    unfold vertexCount
    omega
  exact (offset_le_sum (padding t) k).trans (hsum.trans (regularVertices_le_input t))

/-- A two-parameter bound for the complete unary graph codec. -/
noncomputable def tablePolynomial (a b : Nat) : Polynomial Nat :=
  Polynomial.C a * Polynomial.X + Polynomial.C b * Polynomial.X + 2 +
    (Polynomial.C b * Polynomial.X) *
      (Polynomial.C a * Polynomial.X + Polynomial.C b * Polynomial.X + 8192)

theorem tableBits_le_of_counts (t : GraphTables.Table) (a b L : Nat)
    (hv : t.vertices ≤ a * L) (he : t.darts ≤ b * L) :
    (GraphTables.tableBits t).length ≤ (tablePolynomial a b).eval L := by
  have hsum := Nat.add_le_add hv he
  have hprod := Nat.mul_le_mul he (Nat.add_le_add_right hsum 8192)
  have h := (GraphTables.tableBits_length_le t).trans
    (Nat.add_le_add (Nat.add_le_add_right hsum 2) hprod)
  simpa only [tablePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat] using h

noncomputable def regularPolynomial : Polynomial Nat :=
  tablePolynomial ExpanderFamily.growth (ExpanderFamily.growth * (internalDegree + 1))

theorem regularBits_le (H : BaseTable) (t : GraphTables.Table) :
    (PortTables.tableBits (regularize H t)).length ≤
      regularPolynomial.eval (inputLength t) := by
  have hv : (PortTables.graphTable (regularize H t)).vertices ≤
      ExpanderFamily.growth * inputLength t := regularVertices_le_input t
  have he : (PortTables.graphTable (regularize H t)).darts ≤
      (ExpanderFamily.growth * (internalDegree + 1)) * inputLength t := by
    change vertexCount t (padding t) * (internalDegree + 1) ≤ _
    calc
      _ ≤ (ExpanderFamily.growth * inputLength t) * (internalDegree + 1) :=
        Nat.mul_le_mul_right _ hv
      _ = _ := by ac_rfl
  exact tableBits_le_of_counts (PortTables.graphTable (regularize H t)) _ _ _ hv he

noncomputable def rotorPolynomial (q : Nat) : Polynomial Nat :=
  (Polynomial.C (ExpanderFamily.growth * q) * Polynomial.X) *
    (Polynomial.C (ExpanderFamily.growth * q) * Polynomial.X + 1)

theorem cloudRotorBits_le (t : GraphTables.Table) (v : Fin t.vertices) {q : Nat}
    (table : ExpanderTables.Table (cloudSize t v + padding t v) q) :
    (encodeWords (ExpanderTableWords.rotationWords table)).length ≤
      (rotorPolynomial q).eval (inputLength t) := by
  have hd : (cloudSize t v + padding t v) * q ≤
      (ExpanderFamily.growth * q) * inputLength t := by
    calc
      _ ≤ (ExpanderFamily.growth * inputLength t) * q :=
        Nat.mul_le_mul_right _ (cloudTotal_le_input t v)
      _ = _ := by ac_rfl
  have h := (ExpanderTableWords.encode_rotationWords_length_le table).trans
    (Nat.mul_le_mul hd (Nat.add_le_add_right hd 1))
  simpa only [rotorPolynomial, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one] using h

end UniqueGamesTheorem.Foundations.PCP.PreprocessingMachineBounds

end

section

/-! Executable, codec-compatible stage maps for the actual preprocessing
constructor. The decomposition below is an equality of its existing functions;
runtime certificates must be supplied by the respective concrete machines. -/
namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingStageMaps
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

/-- Exact equality with the original executable constructor, including all
chosen row coordinates and the actual fixed base table. -/
theorem output_eq (H : BaseTable) (t : GraphTables.Table) :
    PreprocessingTables.output H t =
      lazy ((internalDegree + 1) + internalDegree)
        (paddedOverlay H (internalDegree + 1) (regular H t)) := rfl

end UniqueGamesTheorem.Foundations.PCP.PreprocessingStageMaps

end

section

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.RoundGap

open AmplificationRound

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [Nonempty E]

def poweredLower (epsilon : ℝ) : ℝ :=
  PoweringSoundness.gain (Fintype.card Label) FinalConstants.windowHalf (31 / 32) *
    min (epsilon / (Preprocessing.sizeFactor : ℝ)) FinalConstants.cap

theorem poweredLower_nonnegative (epsilon : ℝ) (he : 0 ≤ epsilon) :
    0 ≤ poweredLower epsilon := by
  have hg := PoweringGap.gain_nonneg (Fintype.card Label)
    FinalConstants.windowHalf (31 / 32) (by norm_num)
  have hs : (0 : ℝ) < Preprocessing.sizeFactor := by
    exact_mod_cast Preprocessing.sizeFactor_positive
  exact mul_nonneg hg (le_min (div_nonneg he hs.le) FinalConstants.cap_positive.le)

theorem powered_count_gap (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (G : ConstraintGraph V E Label)
    (labeling : Preprocessing.Vertex G → PoweredAlphabet) :
    poweredLower G.gap * (Fintype.card (PoweredDart G) : ℝ) ≤
      ((powered addresses complete G).rejectionCount labeling : ℝ) := by
  let H := Overlay.originalPortGraph (Preprocessing.overlayGraph G)
  have certificate : SpectralReturn.SpectralCertificate
      (PoweringWalks.lazyGraph H) (31 / 32 : ℝ) :=
    Preprocessing.spectral_certificate G
  have lower : ∀ assignment : Preprocessing.Vertex G → Label,
      (G.gap / (Preprocessing.sizeFactor : ℝ)) *
          (Fintype.card (Preprocessing.Vertex G × Preprocessing.Port) : ℝ) ≤
        ((Preprocessing.graph G).rejectionCount assignment : ℝ) :=
    Preprocessing.gap_transfer_real G G.gap G.gap_nonnegative
      ((G.le_gap_iff G.gap).mp le_rfl)
  have hs : (0 : ℝ) < Preprocessing.sizeFactor := by
    exact_mod_cast Preprocessing.sizeFactor_positive
  have h := PoweringGap.uniform_count_gap H (31 / 32) certificate
    (Preprocessing.graph G).accepts (Preprocessing.accepts_reverse G)
    FinalConstants.windowHalf FinalConstants.windowHalf_positive
    (selectors addresses complete G)
    (G.gap / (Preprocessing.sizeFactor : ℝ)) (div_nonneg G.gap_nonnegative hs.le)
    lower labeling
  convert h using 1 <;>
    simp only [poweredLower, powered, FinalConstants.cap, FinalConstants.walkLength,
      PoweringFinalConstants.center_eq]
  rfl

theorem amplifies (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (G : ConstraintGraph V E Label) :
    min (2 * G.gap) FinalConstants.cap ≤ (graph addresses complete G).gap := by
  apply ((graph addresses complete G).le_gap_iff _).mpr
  intro labeling
  have hcount := AlphabetGraphBounds.gap_transfer_real (powered addresses complete G)
    (poweredLower G.gap) (poweredLower_nonnegative G.gap G.gap_nonnegative)
    (powered_count_gap addresses complete G) labeling
  have hscalar : min (2 * G.gap) FinalConstants.cap ≤ poweredLower G.gap / 12288 := by
    simpa only [poweredLower, FinalConstants.cap, FinalConstants.walkLength,
      PoweringFinalConstants.center_eq] using
      PoweringFinalConstants.composed_scaled_gap G.gap G.gap_nonnegative
  exact (mul_le_mul_of_nonneg_right hscalar (Nat.cast_nonneg _)).trans hcount

end UniqueGamesTheorem.Foundations.PCP.RoundGap

end

end

end OAI
