import Mathlib
import OAI.Computability.DirectedFeedback.Encoding.PreprocessingRegularTables
import OAI.Computability.DirectedFeedback.Encoding.PreprocessingOverlayTables

namespace OAI

namespace DFVSGames.Foundations.PCP.LazySpectral

open PoweringWalks SpectralReturn

noncomputable section

variable {V D : Type*}

theorem half_sum_sq_le (a b : ℝ) : ((a + b) / 2) ^ 2 ≤ (a ^ 2 + b ^ 2) / 2 := by
  nlinarith [sq_nonneg (a - b)]

theorem lazy_energy_le_average [Fintype V] [Fintype D] [Nonempty D]
    (G : PortGraph V D) (f : V → ℝ) :
    energy (averagingOperator (lazyGraph G) f) ≤
      (energy f + energy (averagingOperator G f)) / 2 := by
  calc
    energy (averagingOperator (lazyGraph G) f) =
        mean (fun v => ((f v + averagingOperator G f v) / 2) ^ 2) := by
      unfold energy
      congr 1
      funext v
      rw [PoweringLazy.averagingOperator_lazy]
    _ ≤ mean (fun v => (f v ^ 2 + averagingOperator G f v ^ 2) / 2) :=
      mean_mono (fun v => half_sum_sq_le _ _)
    _ = mean (fun v => (1 / 2 : ℝ) * (f v ^ 2 + averagingOperator G f v ^ 2)) := by
      congr 1
      funext v
      ring
    _ = (1 / 2 : ℝ) * (energy f + energy (averagingOperator G f)) := by
      rw [mean_mul_left, mean_add]
      rfl
    _ = (energy f + energy (averagingOperator G f)) / 2 := by ring

theorem lazy_energy_bound [Fintype V] [Fintype D] [Nonempty D]
    (G : PortGraph V D) (lambda : ℝ) (hG : SpectralCertificate G lambda)
    (f : V → ℝ) (hf : mean f = 0) :
    energy (averagingOperator (lazyGraph G) f) ≤
      ((1 + lambda ^ 2) / 2) * energy f := by
  calc
    energy (averagingOperator (lazyGraph G) f) ≤
        (energy f + energy (averagingOperator G f)) / 2 := lazy_energy_le_average G f
    _ ≤ (energy f + lambda ^ 2 * energy f) / 2 := by
      have h := hG.contraction f hf
      linarith
    _ = ((1 + lambda ^ 2) / 2) * energy f := by ring

theorem lazy_certificate_31_32 [Fintype V] [Fintype D] [Nonempty D]
    (G : PortGraph V D) (hG : SpectralCertificate G (7 / 8)) :
    SpectralCertificate (lazyGraph G) (31 / 32) where
  nonnegative := by norm_num
  lt_one := by norm_num
  contraction f hf := by
    have h := lazy_energy_bound G (7 / 8) hG f hf
    have hcoef : ((1 + (7 / 8 : ℝ) ^ 2) / 2) ≤ (31 / 32 : ℝ) ^ 2 := by norm_num
    exact h.trans (mul_le_mul_of_nonneg_right hcoef (energy_nonnegative f))

end

end DFVSGames.Foundations.PCP.LazySpectral

noncomputable section

namespace DFVSGames.Foundations.PCP.Preprocessing

open PoweringWalks SpectralReturn

variable {V E A : Type*} [Fintype V] [Fintype E] [Fintype A]
  [DecidableEq V] [DecidableEq E] [DecidableEq A] [Nonempty E] [Nonempty A]

abbrev Vertex (G : ConstraintGraph V E A) := VertexPadding.Vertex (Regularization.Vertex G)
abbrev OverlayPort := Regularization.Port ⊕ ExpanderFamily.Port
abbrev Port := Bool × OverlayPort

def degree : Nat := 2 * (2 * Expanders.baseDegree ^ 2 + 1)
def sizeFactor : Nat := ExpanderFamily.growth ^ 2 * degree

private theorem card_lazy_sum_inline_Preprocessing {X Y : Type*} [Fintype X] [Fintype Y]
    (a b : Nat) (hX : Fintype.card X = a) (hY : Fintype.card Y = b) :
    Fintype.card (Bool × (X ⊕ Y)) = 2 * (a + b) := by
  rw [Fintype.card_prod, Fintype.card_bool, Fintype.card_sum, hX, hY]

private theorem doubled_add_inline_Preprocessing (a : Nat) : 2 * (2 * a + 1) = 2 * ((a + 1) + a) := by omega

theorem degree_eq_card : degree = Fintype.card Port := by
  have hr : Fintype.card Regularization.Port = Expanders.baseDegree ^ 2 + 1 :=
    Regularization.degree_eq.trans
      (congrArg (fun n : Nat => n + 1) ExpanderFamily.card_port)
  have hp : Fintype.card Port =
      2 * ((Expanders.baseDegree ^ 2 + 1) + Expanders.baseDegree ^ 2) :=
    card_lazy_sum_inline_Preprocessing _ _ hr ExpanderFamily.card_port
  exact (doubled_add_inline_Preprocessing _).trans hp.symm

theorem degree_positive : 0 < degree := by
  unfold degree
  omega

theorem sizeFactor_positive : 0 < sizeFactor := by
  have hg : 0 < ExpanderFamily.growth :=
    Nat.zero_lt_one.trans ExpanderFamily.growth_gt_one
  exact Nat.mul_pos (Nat.pow_pos hg) degree_positive

def paddedGraph (G : ConstraintGraph V E A) :
    ConstraintGraph (Vertex G) (Vertex G × Regularization.Port) A :=
  VertexPadding.paddedG (Regularization.graph G)

def overlayExpander (G : ConstraintGraph V E A) :
    PortGraph (Vertex G) ExpanderFamily.Port :=
  GraphTransport.reindex
    (ExpanderFamily.family (ExpanderFamily.level (Fintype.card (Regularization.Vertex G))))
    (VertexPadding.familyVertexEquiv (Regularization.Vertex G)).symm (Equiv.refl _)

omit [Fintype A] [DecidableEq E] [DecidableEq A] [Nonempty E] [Nonempty A] in
theorem overlayExpander_certificate (G : ConstraintGraph V E A) :
    SpectralCertificate (overlayExpander G) (1 / 2 : ℝ) :=
  GraphTransport.reindex_spectralCertificate _ _ _ _ (ExpanderFamily.family_certificate _)

def overlayGraph (G : ConstraintGraph V E A) :
    ConstraintGraph (Vertex G) (Vertex G × OverlayPort) A :=
  Overlay.constraintGraph (paddedGraph G) (overlayExpander G)

def graph (G : ConstraintGraph V E A) :
    ConstraintGraph (Vertex G) (Vertex G × Port) A :=
  LazyConstraint.constraintGraph (overlayGraph G)

def portGraph (G : ConstraintGraph V E A) : PortGraph (Vertex G) Port :=
  Overlay.originalPortGraph (graph G)

omit [Fintype A] [DecidableEq E] [Nonempty E] [Nonempty A] in
@[simp] theorem graph_tail (G : ConstraintGraph V E A) : (graph G).tail = Prod.fst := rfl

omit [Fintype A] [DecidableEq E] [Nonempty E] [Nonempty A] in
@[simp] theorem graph_reverse (G : ConstraintGraph V E A) :
    (graph G).reverse = (portGraph G).rot := rfl

omit [Fintype A] [DecidableEq E] [Nonempty E] [Nonempty A] in
theorem accepts_reverse (G : ConstraintGraph V E A) (e : Vertex G × Port) (a b : A) :
    (graph G).accepts ((portGraph G).rot e) b a = (graph G).accepts e a b :=
  (graph G).reverse_accepts e a b

omit [Fintype A] [DecidableEq E] [Nonempty E] [Nonempty A] in
theorem portGraph_eq_lazyGraph (G : ConstraintGraph V E A) :
    portGraph G = lazyGraph (Overlay.originalPortGraph (overlayGraph G)) := rfl

omit [Fintype A] [DecidableEq E] [Nonempty A] in
theorem overlayGraph_certificate (G : ConstraintGraph V E A) :
    SpectralCertificate (Overlay.originalPortGraph (overlayGraph G)) (7 / 8 : ℝ) := by
  apply Overlay.constraintGraph_spectralCertificate
  · exact Regularization.degree_eq
  · have h := ExpanderFamily.port_degree_ge_eight
    omega
  · exact overlayExpander_certificate G

omit [Fintype A] [DecidableEq E] [Nonempty A] in

theorem spectral_certificate (G : ConstraintGraph V E A) :
    SpectralCertificate (portGraph G) (31 / 32 : ℝ) := by
  rw [portGraph_eq_lazyGraph]
  exact LazySpectral.lazy_certificate_31_32 _ (overlayGraph_certificate G)

omit [Nonempty A] in
omit [Fintype A] [DecidableEq E] [DecidableEq A] in
theorem vertex_count_le (G : ConstraintGraph V E A) :
    Fintype.card (Vertex G) ≤ ExpanderFamily.growth ^ 2 * Fintype.card E := by
  calc
    _ ≤ ExpanderFamily.growth * Fintype.card (Regularization.Vertex G) :=
      VertexPadding.card_vertex_le _
    _ ≤ ExpanderFamily.growth * (ExpanderFamily.growth * Fintype.card E) :=
      Nat.mul_le_mul_left _ (Regularization.vertex_count_le G)
    _ = _ := by ring

omit [Fintype A] [DecidableEq E] [DecidableEq A] [Nonempty E] [Nonempty A] in
theorem dart_count (G : ConstraintGraph V E A) :
    Fintype.card (Vertex G × Port) = Fintype.card (Vertex G) * degree := by
  rw [Fintype.card_prod, ← degree_eq_card]

omit [Nonempty A] in
omit [Fintype A] [DecidableEq E] [DecidableEq A] in
theorem dart_count_le (G : ConstraintGraph V E A) :
    Fintype.card (Vertex G × Port) ≤ sizeFactor * Fintype.card E := by
  rw [dart_count]
  calc
    _ ≤ (ExpanderFamily.growth ^ 2 * Fintype.card E) * degree :=
      Nat.mul_le_mul_right degree (vertex_count_le G)
    _ = _ := Nat.mul_right_comm _ _ _

def liftLabel (G : ConstraintGraph V E A) (labeling : V → A) : Vertex G → A :=
  VertexPadding.liftLabel (Classical.choice ‹Nonempty A›) (Regularization.liftLabel G labeling)

omit [Nonempty E] in
omit [Fintype A] [DecidableEq E] in

theorem lift_rejectionCount (G : ConstraintGraph V E A) (labeling : V → A) :
    (graph G).rejectionCount (liftLabel G labeling) = G.rejectionCount labeling := by
  unfold graph
  rw [LazyConstraint.rejectionCount_eq _ rfl]
  unfold overlayGraph
  rw [Overlay.rejectionCount_eq _ _ rfl]
  unfold paddedGraph liftLabel
  rw [VertexPadding.rejectionCount_liftLabel _ rfl]
  exact Regularization.lift_rejectionCount G labeling

omit [Nonempty E] in
omit [Fintype A] [DecidableEq E] in
theorem completeness (G : ConstraintGraph V E A) (hG : G.Satisfiable) :
    (graph G).Satisfiable := by
  apply (LazyConstraint.satisfiable_iff _ rfl).mpr
  apply (Overlay.satisfiable_iff _ _ rfl).mpr
  exact VertexPadding.paddedG_satisfiable (Regularization.graph G) rfl
    (Classical.choice ‹Nonempty A›) (Regularization.completeness G hG)

def roundLabels (G : ConstraintGraph V E A) (labeling : Vertex G → A) : V → A :=
  Regularization.roundLabels G (fun v => labeling (Sum.inl v))

omit [Nonempty E] in

theorem soundness (G : ConstraintGraph V E A) (labeling : Vertex G → A) :
    G.rejectionCount (roundLabels G labeling) ≤ (graph G).rejectionCount labeling := by
  calc
    _ ≤ (Regularization.graph G).rejectionCount (fun v => labeling (Sum.inl v)) :=
      Regularization.soundness G _
    _ = (paddedGraph G).rejectionCount labeling :=
      (VertexPadding.paddedG_rejectionCount (Regularization.graph G) rfl labeling).symm
    _ = (overlayGraph G).rejectionCount labeling :=
      (Overlay.rejectionCount_eq (paddedGraph G) (overlayExpander G) rfl labeling).symm
    _ = (graph G).rejectionCount labeling :=
      (LazyConstraint.rejectionCount_eq (overlayGraph G) rfl labeling).symm

omit [Nonempty E] in
theorem satisfiable_iff (G : ConstraintGraph V E A) :
    (graph G).Satisfiable ↔ G.Satisfiable := by
  constructor
  · rintro ⟨labeling, hlabel⟩
    by_contra hG
    have hpositive := G.rejectionCount_positive hG (roundLabels G labeling)
    have hzero : (graph G).rejectionCount labeling = 0 := by
      simp [ConstraintGraph.rejectionCount, ConstraintGraph.rejectedDarts, hlabel]
    have hsound := soundness G labeling
    omega
  · exact completeness G

theorem gap_transfer (G : ConstraintGraph V E A) (epsilon : ℚ) (he : 0 ≤ epsilon)
    (lower : ∀ labeling : V → A,
      epsilon * Fintype.card E ≤ (G.rejectionCount labeling : ℚ))
    (labeling : Vertex G → A) :
    (epsilon / sizeFactor) * Fintype.card (Vertex G × Port) ≤
      ((graph G).rejectionCount labeling : ℚ) := by
  have hfactor : (0 : ℚ) < sizeFactor := by exact_mod_cast sizeFactor_positive
  have hcard : (Fintype.card (Vertex G × Port) : ℚ) ≤
      sizeFactor * Fintype.card E := by exact_mod_cast dart_count_le G
  calc
    _ ≤ (epsilon / sizeFactor) * (sizeFactor * Fintype.card E) :=
      mul_le_mul_of_nonneg_left hcard (div_nonneg he hfactor.le)
    _ = epsilon * Fintype.card E := by field_simp
    _ ≤ (G.rejectionCount (roundLabels G labeling) : ℚ) := lower _
    _ ≤ ((graph G).rejectionCount labeling : ℚ) := by exact_mod_cast soundness G labeling

theorem gap_transfer_real (G : ConstraintGraph V E A) (epsilon : ℝ) (he : 0 ≤ epsilon)
    (lower : ∀ labeling : V → A,
      epsilon * Fintype.card E ≤ (G.rejectionCount labeling : ℝ))
    (labeling : Vertex G → A) :
    (epsilon / sizeFactor) * Fintype.card (Vertex G × Port) ≤
      ((graph G).rejectionCount labeling : ℝ) := by
  have hfactor : (0 : ℝ) < sizeFactor := by exact_mod_cast sizeFactor_positive
  have hcard : (Fintype.card (Vertex G × Port) : ℝ) ≤
      sizeFactor * Fintype.card E := by exact_mod_cast dart_count_le G
  calc
    _ ≤ (epsilon / sizeFactor) * (sizeFactor * Fintype.card E) :=
      mul_le_mul_of_nonneg_left hcard (div_nonneg he hfactor.le)
    _ = epsilon * Fintype.card E := by field_simp
    _ ≤ (G.rejectionCount (roundLabels G labeling) : ℝ) := lower _
    _ ≤ ((graph G).rejectionCount labeling : ℝ) := by exact_mod_cast soundness G labeling

end DFVSGames.Foundations.PCP.Preprocessing
end

namespace DFVSGames.Foundations.PCP.PreprocessingTables

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

end DFVSGames.Foundations.PCP.PreprocessingTables

namespace DFVSGames.Foundations.PCP.PreprocessingRegularSoundness

open PoweringWalks DegreeReplacement SpectralReturn PreprocessingRegularTables

theorem internalDegree_ge_eight : 8 ≤ internalDegree := by
  simpa only [ExpanderFamily.card_port, internalDegree, pow_two] using
    ExpanderFamily.port_degree_ge_eight

theorem baseDegree_ne_zero : Expanders.baseDegree ≠ 0 := by
  intro h
  have hdegree := internalDegree_ge_eight
  simp only [internalDegree, h, Nat.zero_mul] at hdegree
  omega

theorem resizeTable_certificate {n m q : Nat} (h : n = m)
    (table : ExpanderTables.Table n q) (lambda : ℝ)
    (certificate : SpectralCertificate (ExpanderTables.graph table) lambda) :
    SpectralCertificate (ExpanderTables.graph (resizeTable h table)) lambda := by
  cases h
  exact certificate

theorem familyCloudTable_certificate_of_pos (H : BaseTable)
    (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (t : GraphTables.Table) (v : Fin t.vertices)
    (hk : 0 < PreprocessingCloudIndex.cloudSize t v) :
    SpectralCertificate (ExpanderTables.graph (familyCloudTable H t v)) (1 / 2 : ℝ) := by
  let : NeZero Expanders.baseDegree := ⟨baseDegree_ne_zero⟩
  unfold familyCloudTable
  rw [dite_eq_right (Nat.ne_of_gt hk)]
  apply resizeTable_certificate
  exact ExpanderTables.family_certificate H certificate _

theorem cloudGraphs_certificate_of_pos (H : BaseTable)
    (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (t : GraphTables.Table) (v : Fin t.vertices)
    (hk : 0 < PreprocessingCloudIndex.cloudSize t v) :
    SpectralCertificate (cloudGraphs t (padding t) (familyCloudTable H t) v)
      (1 / 2 : ℝ) := by
  exact GraphTransport.reindex_spectralCertificate _ _ _ _
    (familyCloudTable_certificate_of_pos H certificate t v hk)

theorem cloud_expansion (H : BaseTable)
    (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (t : GraphTables.Table) (v : Fin t.vertices)
    (S : Finset (PreprocessingCloudIndex.PaddedCloud t (padding t) v))
    (hsmall : S.card ≤
      Fintype.card (PreprocessingCloudIndex.PaddedCloud t (padding t) v) / 2) :
    2 * S.card ≤ (CloudRounding.directedCut
      (fun ed => ((cloudGraphs t (padding t) (familyCloudTable H t) v).rot ed).1) S).card := by
  by_cases hk : PreprocessingCloudIndex.cloudSize t v = 0
  · have hzero : Fintype.card (PreprocessingCloudIndex.PaddedCloud t (padding t) v) = 0 := by
      rw [PreprocessingCloudIndex.card_paddedCloud, cloudSize_add_padding, hk]
      rfl
    have hs : S.card = 0 := by omega
    simp only [hs, mul_zero, Nat.zero_le]
  · exact SpectralCut.cut_card_ge_twice
      (cloudGraphs t (padding t) (familyCloudTable H t) v)
      (cloudGraphs_certificate_of_pos H certificate t v (Nat.pos_of_ne_zero hk))
      (by simpa only [Fintype.card_fin] using internalDegree_ge_eight) S (by
        change 2 * S.card ≤
          Fintype.card (PreprocessingCloudIndex.PaddedCloud t (padding t) v)
        omega)

noncomputable def roundLabels (t : GraphTables.Table)
    (labels : Fin (vertexCount t (padding t)) → GraphTables.Label) :
    Fin t.vertices → GraphTables.Label :=
  CloudRounding.roundLabels
    (paddedGraph (GraphTables.semantics t) (fun v => Fin (padding t v)))
    (fun z => labels (vertexOrder t (padding t) z))

theorem soundness (H : BaseTable)
    (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (t : GraphTables.Table)
    (labels : Fin (vertexCount t (padding t)) → GraphTables.Label) :
    (GraphTables.semantics t).rejectionCount (roundLabels t labels) ≤
      (PortTables.baseGraph (regularize H t)).rejectionCount labels := by
  rw [regularize, rejectionCount_ofCloudTables]
  exact CloudRounding.padded_replacement_soundness (GraphTables.semantics t)
    (fun v => Fin (padding t v)) (cloudGraphs t (padding t) (familyCloudTable H t))
    (cloud_expansion H certificate t) (fun z => labels (vertexOrder t (padding t) z))

theorem exists_rounding (H : BaseTable)
    (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (t : GraphTables.Table)
    (labels : Fin (vertexCount t (padding t)) → GraphTables.Label) :
    ∃ original : Fin t.vertices → GraphTables.Label,
      (GraphTables.semantics t).rejectionCount original ≤
        (PortTables.baseGraph (regularize H t)).rejectionCount labels :=
  ⟨roundLabels t labels, soundness H certificate t labels⟩

theorem lift_rejectionCount (H : BaseTable) (t : GraphTables.Table)
    (labels : Fin t.vertices → GraphTables.Label) :
    (PortTables.baseGraph (regularize H t)).rejectionCount
        (liftedLabel t (padding t) labels) = (GraphTables.semantics t).rejectionCount labels :=
  rejectionCount_liftedLabel t (padding t) (familyCloudTable H t) labels

theorem completeness (H : BaseTable) (t : GraphTables.Table)
    (h : (GraphTables.semantics t).Satisfiable) :
    (PortTables.baseGraph (regularize H t)).Satisfiable := by
  obtain ⟨labels, hlabels⟩ := h
  refine ⟨liftedLabel t (padding t) labels, ?_⟩
  intro e
  obtain ⟨z, rfl⟩ :=
    (Equiv.prodCongr (vertexOrder t (padding t)) (portOrder internalDegree)).surjective e
  rcases z with ⟨v, p⟩
  change (PortTables.baseGraph (regularize H t)).edgeSatisfied
    (liftedLabel t (padding t) labels)
    (vertexOrder t (padding t) v, portOrder internalDegree p) = true
  rw [regularize, edgeSatisfied_ofCloudTables]
  simp only [liftedLabel, Equiv.symm_apply_apply]
  have hcomplete := replacement_complete
    (paddedGraph (GraphTables.semantics t) (fun v => Fin (padding t v)))
    (cloudGraphs t (padding t) (familyCloudTable H t)) labels
    (padded_complete (GraphTables.semantics t) (fun v => Fin (padding t v)) labels hlabels)
    (v, p)
  convert hcomplete using 1
  rfl

theorem soundness_of_uniform_lower_bound (H : BaseTable)
    (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (t : GraphTables.Table) (k : Nat)
    (lower : ∀ original : Fin t.vertices → GraphTables.Label,
      k ≤ (GraphTables.semantics t).rejectionCount original)
    (labels : Fin (vertexCount t (padding t)) → GraphTables.Label) :
    k ≤ (PortTables.baseGraph (regularize H t)).rejectionCount labels :=
  (lower (roundLabels t labels)).trans (soundness H certificate t labels)

theorem soundness_of_uniform_real_lower_bound (H : BaseTable)
    (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (t : GraphTables.Table) (k : ℝ)
    (lower : ∀ original : Fin t.vertices → GraphTables.Label,
      k ≤ ((GraphTables.semantics t).rejectionCount original : ℝ))
    (labels : Fin (vertexCount t (padding t)) → GraphTables.Label) :
    k ≤ ((PortTables.baseGraph (regularize H t)).rejectionCount labels : ℝ) :=
  (lower (roundLabels t labels)).trans (Nat.cast_le.mpr (soundness H certificate t labels))

end DFVSGames.Foundations.PCP.PreprocessingRegularSoundness

namespace DFVSGames.Foundations.PCP.PreprocessingTableSpectral

open PoweringWalks SpectralReturn

private theorem portGraph_ext_inline_PreprocessingTableSpectral {V D : Type*} {G H : PortGraph V D}
    (h : ∀ x, G.rot x = H.rot x) : G = H := by
  have hr : G.rot = H.rot := Equiv.ext h
  cases G
  cases H
  cases hr
  rfl

theorem materialize_portGraph {n d : Nat} {D : Type*}
    (G : ConstraintGraph (Fin n) (Fin n × D) PortTables.Label)
    (ports : D ≃ Fin d) :
    PortTables.portGraph (PreprocessingOverlayTables.materialize G ports) =
      GraphTransport.reindex (Overlay.originalPortGraph G) (Equiv.refl _) ports := by
  apply portGraph_ext_inline_PreprocessingTableSpectral
  intro x
  rw [PortTables.portGraph_rot, PreprocessingOverlayTables.rotation_materialize]
  rfl

theorem overlay_portGraph {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) :
    PortTables.portGraph (PreprocessingOverlayTables.overlay G H) =
      GraphTransport.reindex
        (Overlay.portGraph (PortTables.portGraph G) (ExpanderTables.graph H))
        (Equiv.refl _) (PreprocessingOverlayTables.overlayPorts d e) := by
  unfold PreprocessingOverlayTables.overlay
  rw [materialize_portGraph]
  rfl

theorem overlay_rotation_eq {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) (x : Fin n × Fin (d + e)) :
    PortTables.rotation (PreprocessingOverlayTables.overlay G H) x =
      (GraphTransport.reindex
        (Overlay.portGraph (PortTables.portGraph G) (ExpanderTables.graph H))
        (Equiv.refl _) (PreprocessingOverlayTables.overlayPorts d e)).rot x := by
  change (PortTables.portGraph (PreprocessingOverlayTables.overlay G H)).rot x = _
  rw [overlay_portGraph]

theorem lazy_portGraph {n d : Nat} (G : PortTables.Table n d) :
    PortTables.portGraph (PreprocessingOverlayTables.lazy G) =
      GraphTransport.reindex (lazyGraph (PortTables.portGraph G))
        (Equiv.refl _) (PreprocessingOverlayTables.lazyPorts d) := by
  unfold PreprocessingOverlayTables.lazy
  rw [materialize_portGraph]
  rfl

theorem lazy_rotation_eq {n d : Nat} (G : PortTables.Table n d)
    (x : Fin n × Fin (2 * d)) :
    PortTables.rotation (PreprocessingOverlayTables.lazy G) x =
      (GraphTransport.reindex (lazyGraph (PortTables.portGraph G))
        (Equiv.refl _) (PreprocessingOverlayTables.lazyPorts d)).rot x := by
  change (PortTables.portGraph (PreprocessingOverlayTables.lazy G)).rot x = _
  rw [lazy_portGraph]

theorem overlay_certificate_seven_eighths {n d e : Nat}
    (G : PortTables.Table n d) (H : ExpanderTables.Table n e)
    (hn : 0 < n) (hdegree : d = e + 1) (he : 8 ≤ e)
    (hH : SpectralCertificate (ExpanderTables.graph H) (1 / 2 : ℝ)) :
    SpectralCertificate (PortTables.portGraph (PreprocessingOverlayTables.overlay G H))
      (7 / 8 : ℝ) := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [overlay_portGraph]
  apply GraphTransport.reindex_spectralCertificate
  apply Overlay.spectralCertificate_seven_eighths
    (PortTables.portGraph G) (ExpanderTables.graph H)
  · simpa only [Fintype.card_fin] using hdegree
  · simp only [Fintype.card_fin]
    omega
  · exact hH

theorem lazy_certificate_31_32 {n d : Nat} (G : PortTables.Table n d)
    (hd : 0 < d) (hG : SpectralCertificate (PortTables.portGraph G) (7 / 8 : ℝ)) :
    SpectralCertificate (PortTables.portGraph (PreprocessingOverlayTables.lazy G))
      (31 / 32 : ℝ) := by
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  rw [lazy_portGraph]
  exact GraphTransport.reindex_spectralCertificate _ _ _ _
    (LazySpectral.lazy_certificate_31_32 (PortTables.portGraph G) hG)

end DFVSGames.Foundations.PCP.PreprocessingTableSpectral

noncomputable section

namespace DFVSGames.Foundations.PCP.PreprocessingGuarantees

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
          (PreprocessingOverlayTables.overlayPorts d e)) (Equiv.refl _) labels using 1 ; rfl
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
          (PreprocessingOverlayTables.lazyPorts d)) (Equiv.refl _) labels using 1 ; rfl
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

end DFVSGames.Foundations.PCP.PreprocessingGuarantees
end

namespace DFVSGames.Foundations.PCP.PoweringLabels

open PoweringWalks
open scoped BigOperators

variable {V D A : Type*}

abbrev PortWords (D : Type*) (t : Nat) := (n : Fin (t + 1)) × (Fin n.val → D)

instance finitePortWords [Finite D] (t : Nat) : Finite (PortWords D t) := by
  let := Fintype.ofFinite D
  exact Finite.of_fintype _

def Ball (G : PortGraph V D) (t : Nat) (v : V) :=
  {u : V // ∃ n, n ≤ t ∧ ∃ p : Fin n → D, wordEnd G n v p = u}

def wordToBall (G : PortGraph V D) (t : Nat) (v : V) (w : PortWords D t) : Ball G t v :=
  ⟨wordEnd G w.1.val v w.2, w.1.val, Nat.le_of_lt_succ w.1.isLt, w.2, rfl⟩

theorem wordToBall_surjective (G : PortGraph V D) (t : Nat) (v : V) :
    Function.Surjective (wordToBall G t v) := by
  intro u
  obtain ⟨n, hn, p, hp⟩ := u.property
  refine ⟨⟨⟨n, Nat.lt_succ_of_le hn⟩, p⟩, ?_⟩
  exact Subtype.ext hp

instance finiteBall [Finite D] (G : PortGraph V D) (t : Nat) (v : V) :
    Finite (Ball G t v) :=
  Finite.of_surjective (wordToBall G t v) (wordToBall_surjective G t v)

theorem card_portWords [Finite D] (t : Nat) :
    Nat.card (PortWords D t) = ∑ n : Fin (t + 1), Nat.card D ^ n.val := by
  simp [PortWords, Nat.card_sigma, Nat.card_fun]

theorem card_ball_le [Finite D] (G : PortGraph V D) (t : Nat) (v : V) :
    Nat.card (Ball G t v) ≤ ∑ n : Fin (t + 1), Nat.card D ^ n.val := by
  calc
    _ ≤ Nat.card (PortWords D t) := Nat.card_le_card_of_surjective
      (wordToBall G t v) (wordToBall_surjective G t v)
    _ = _ := card_portWords t

structure AddressSelector (G : PortGraph V D) (t : Nat) (v : V) where
  address : Ball G t v → PortWords D t
  correct : ∀ u, wordToBall G t v (address u) = u

noncomputable def classicalSelector (G : PortGraph V D) (t : Nat) (v : V) :
    AddressSelector G t v where
  address u := Classical.choose (wordToBall_surjective G t v u)
  correct u := Classical.choose_spec (wordToBall_surjective G t v u)

def scanWitness {A : Type*} (p : A → Prop) [DecidablePred p] :
    (xs : List A) → (∃ a ∈ xs, p a) → {a // p a}
  | [], h => False.elim (by simp at h)
  | a :: xs, h =>
    if ha : p a then ⟨a, ha⟩ else
      scanWitness p xs (by
        obtain ⟨b, hb, hp⟩ := h
        rcases List.mem_cons.mp hb with he | hm
        · exact False.elim (ha (he ▸ hp))
        · exact ⟨b, hm, hp⟩)

def listSelector [DecidableEq V] (G : PortGraph V D) (t : Nat) (v : V)
    (addresses : List (PortWords D t)) (complete : ∀ w, w ∈ addresses) :
    AddressSelector G t v where
  address u := (scanWitness (fun w => (wordToBall G t v w).val = u.val) addresses (by
    obtain ⟨w, hw⟩ := wordToBall_surjective G t v u
    exact ⟨w, complete w, congrArg Subtype.val hw⟩)).val
  correct u := Subtype.ext (scanWitness
    (fun w => (wordToBall G t v w).val = u.val) addresses (by
      obtain ⟨w, hw⟩ := wordToBall_surjective G t v u
      exact ⟨w, complete w, congrArg Subtype.val hw⟩)).property

abbrev PaddedLabel (D : Type*) (t : Nat) (A : Type*) := PortWords D t → A

def encode (G : PortGraph V D) (t : Nat) (v : V) (ℓ : Ball G t v → A) :
    PaddedLabel D t A := fun w => ℓ (wordToBall G t v w)

def decode {G : PortGraph V D} {t : Nat} {v : V} (S : AddressSelector G t v)
    (a : PaddedLabel D t A) : Ball G t v → A := fun u => a (S.address u)

theorem decode_encode {G : PortGraph V D} {t : Nat} {v : V}
    (S : AddressSelector G t v) (ℓ : Ball G t v → A) :
    decode S (encode G t v ℓ) = ℓ := by
  funext u
  change ℓ (wordToBall G t v (S.address u)) = ℓ u
  rw [S.correct]

theorem decode_surjective {G : PortGraph V D} {t : Nat} {v : V}
    (S : AddressSelector G t v) : Function.Surjective (decode (A := A) S) :=
  fun ℓ => ⟨encode G t v ℓ, decode_encode S ℓ⟩

theorem encode_injective (G : PortGraph V D) (t : Nat) (v : V) :
    Function.Injective (encode (A := A) G t v) := by
  intro a b h
  funext u
  obtain ⟨w, rfl⟩ := wordToBall_surjective G t v u
  exact congrFun h w

theorem decoded_word_collision {G : PortGraph V D} {t : Nat} {v : V}
    (S : AddressSelector G t v) (a : PaddedLabel D t A) (w z : PortWords D t)
    (h : (wordToBall G t v w).val = (wordToBall G t v z).val) :
    decode S a (wordToBall G t v w) = decode S a (wordToBall G t v z) :=
  congrArg (decode S a) (Subtype.ext h)

theorem card_paddedLabel [Finite D] [Finite A] (t : Nat) :
    Nat.card (PaddedLabel D t A) =
      Nat.card A ^ (∑ n : Fin (t + 1), Nat.card D ^ n.val) := by
  rw [Nat.card_fun, card_portWords]

end DFVSGames.Foundations.PCP.PoweringLabels

end OAI
