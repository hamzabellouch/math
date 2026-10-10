import Mathlib
import OAI.Computability.MaxCut.PCP.SpectralCut

namespace OAI

/-!
# Soundness of the executable regularization tables

The fixed input base table is required only to have its proved spectral
certificate. Every positive cloud uses the actual recursively generated table
at its computed size. Its spectral certificate gives the precise cut bound
used by majority rounding. Empty clouds are handled by their zero cardinality.
Thus neither expansion nor the desired count comparison is an input premise.
-/

namespace MaxCutGames.Foundations.PCP.PreprocessingRegularSoundness

open PoweringWalks DegreeReplacement SpectralReturn PreprocessingRegularTables

theorem internalDegree_ge_eight : 8 ≤ internalDegree := by
  simpa only [ExpanderFamily.card_port, internalDegree, pow_two] using
    ExpanderFamily.port_degree_ge_eight

theorem baseDegree_ne_zero : Expanders.baseDegree ≠ 0 := by
  intro h
  have hdegree := internalDegree_ge_eight
  simp only [internalDegree, h, Nat.zero_mul] at hdegree
  omega

/-- Erasing a proof-equal table size preserves its exact spectral certificate. -/
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

/-- The exact finite cut inequality needed to pay for each changed cloud label. -/
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

/-- Decode the actual numbered output labels by majority in each padded cloud. -/
noncomputable def roundLabels (t : GraphTables.Table)
    (labels : Fin (vertexCount t (padding t)) → GraphTables.Label) :
    Fin t.vertices → GraphTables.Label :=
  CloudRounding.roundLabels
    (paddedGraph (GraphTables.semantics t) (fun v => Fin (padding t v)))
    (fun z => labels (vertexOrder t (padding t) z))

/-- Direct soundness for the generated tables, with no matching-base premise. -/
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

/-- Completeness preserves the number of rejected original dart occurrences. -/
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

end MaxCutGames.Foundations.PCP.PreprocessingRegularSoundness

/-!
Spectral certificates for the actual materialized preprocessing tables.
Exact rotation identities transport the checked semantic overlay and lazy
estimates to the stored tables. No spectral premise is imposed on the
original constraint table in the overlay theorem.
-/

namespace MaxCutGames.Foundations.PCP.PreprocessingTableSpectral

open PoweringWalks SpectralReturn

private theorem portGraph_ext_inline_PreprocessingTableSpectral {V D : Type*} {G H : PortGraph V D}
    (h : ∀ x, G.rot x = H.rot x) : G = H := by
  have hr : G.rot = H.rot := Equiv.ext h
  cases G
  cases H
  cases hr
  rfl

/-- Materialization retains exactly the explicitly reindexed rotation. -/
theorem materialize_portGraph {n d : Nat} {D : Type*}
    (G : ConstraintGraph (Fin n) (Fin n × D) PortTables.Label)
    (ports : D ≃ Fin d) :
    PortTables.portGraph (PreprocessingOverlayTables.materialize G ports) =
      GraphTransport.reindex (Overlay.originalPortGraph G) (Equiv.refl _) ports := by
  apply portGraph_ext_inline_PreprocessingTableSpectral
  intro x
  rw [PortTables.portGraph_rot, PreprocessingOverlayTables.rotation_materialize]
  rfl

/-- The stored overlaid graph is the actual semantic overlay in numbered
port coordinates. This is equality of reversible port graphs. -/
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

/-- The stored lazy graph is exactly the Boolean-flag lazy graph, with the
declared false-first port encoding. -/
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

/-- An actual half-spectral expander overlay gives a `7/8` certificate for
the stored table. The original table needs no spectral certificate.
The degree hypothesis supplies nonempty old and expander port types. -/
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

/-- An actual `7/8` certificate gives a `31/32` certificate for the
materialized lazy table. Only the original port set must be nonempty. -/
theorem lazy_certificate_31_32 {n d : Nat} (G : PortTables.Table n d)
    (hd : 0 < d) (hG : SpectralCertificate (PortTables.portGraph G) (7 / 8 : ℝ)) :
    SpectralCertificate (PortTables.portGraph (PreprocessingOverlayTables.lazy G))
      (31 / 32 : ℝ) := by
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  rw [lazy_portGraph]
  exact GraphTransport.reindex_spectralCertificate _ _ _ _
    (LazySpectral.lazy_certificate_31_32 (PortTables.portGraph G) hG)

end MaxCutGames.Foundations.PCP.PreprocessingTableSpectral

/-! Soundness and expansion of the actual executable preprocessing tables.
The fixed base-table spectral certificate is supplied by the proved expander
existence theorem; no output expansion or output gap is assumed. -/

noncomputable section

namespace MaxCutGames.Foundations.PCP.PreprocessingGuarantees

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

end MaxCutGames.Foundations.PCP.PreprocessingGuarantees
end

/-! Full-radius local opinions use a common alphabet indexed by bounded
port addresses. Every opinion is decoded through a fixed address selector;
arbitrary alphabet symbols need not agree on colliding addresses. -/

namespace MaxCutGames.Foundations.PCP.PoweringLabels

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

/-- Executable first-match search, with a proof that a match is present. -/
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

/-- A concrete complete address list supplies a computational selector. Its
length depends on the degree and radius, not on the ambient vertex count. -/
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

end MaxCutGames.Foundations.PCP.PoweringLabels

/-!
# Executable bounded port-address enumeration

For a port alphabet `Fin d`, the lists below enumerate every word of every
length at most the fixed radius. The resulting first-match selector searches
these addresses and never enumerates the ambient vertex type.
-/

namespace MaxCutGames.Foundations.PCP.PoweringAddresses

open PoweringWalks PoweringLabels
open scoped BigOperators

variable {V : Type*}

/-- All words of a specified length, ordered first by their head port. -/
def allWords (d : Nat) : (n : Nat) → List (Fin n → Fin d)
  | 0 => [Fin.elim0]
  | n + 1 => (List.finRange d).flatMap fun a =>
      (allWords d n).map fun p => Fin.cases a p

theorem mem_allWords (d : Nat) :
    ∀ n (p : Fin n → Fin d), p ∈ allWords d n := by
  intro n
  induction n with
  | zero =>
    intro p
    simp only [allWords, List.mem_singleton]
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    intro p
    simp only [allWords, List.mem_flatMap, List.mem_map]
    refine ⟨p 0, List.mem_finRange (p 0), (fun j => p j.succ), ih _, ?_⟩
    funext j
    exact Fin.cases rfl (fun _ => rfl) j

/-- The complete address list, including the unique empty word. -/
def allAddresses (d t : Nat) : List (PortWords (Fin d) t) :=
  (List.finRange (t + 1)).flatMap fun n =>
    (allWords d n.val).map fun p => Sigma.mk n p

theorem mem_allAddresses (d t : Nat) (w : PortWords (Fin d) t) :
    w ∈ allAddresses d t := by
  rcases w with ⟨n, p⟩
  unfold allAddresses
  apply List.mem_flatMap.mpr
  refine ⟨n, List.mem_finRange n, ?_⟩
  exact List.mem_map.mpr ⟨p, mem_allWords d n.val p, rfl⟩

theorem length_allWords (d : Nat) :
    ∀ n, (allWords d n).length = d ^ n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [allWords, List.length_flatMap, List.length_map, ih,
      List.map_const', List.length_finRange, List.sum_replicate_nat]
    exact (Nat.mul_comm d (d ^ n)).trans (Nat.pow_succ d n).symm

/-- The selector's search-list bound depends only on degree and radius. -/
theorem length_allAddresses (d t : Nat) :
    (allAddresses d t).length = ∑ n : Fin (t + 1), d ^ n.val := by
  unfold allAddresses
  simp only [List.length_flatMap, List.length_map, length_allWords]
  exact (Fin.sum_univ_def (fun n : Fin (t + 1) => d ^ n.val)).symm

/-- A fully executable selector from the explicit bounded address list. -/
def finitePortSelector {d : Nat} [DecidableEq V] (G : PortGraph V (Fin d))
    (t : Nat) (v : V) : AddressSelector G t v :=
  listSelector G t v (allAddresses d t) (mem_allAddresses d t)

end MaxCutGames.Foundations.PCP.PoweringAddresses

/-!
# Executable integer encodings for the powering construction

All encodings below have explicit inverses. They use the arithmetic finite
function, sigma, and product equivalences rather than choosing enumerations
from cardinality proofs. Word digits use the head-major convention; addresses
are grouped by increasing word length. A dart is numbered first by its vertex,
then its word, with its two orientations adjacent.
-/

namespace MaxCutGames.Foundations.PCP.PoweringEnumeration

open PoweringLabels
open scoped BigOperators

/-- The number of words with length at most `t`, including the empty word. -/
def addressCount (d t : Nat) : Nat := ∑ i : Fin (t + 1), d ^ i.val

/-- Reverse the digit positions before using the little-endian arithmetic
encoding from mathlib. Both directions are the same executable operation. -/
def reverseWordEquiv (d n : Nat) : (Fin n → Fin d) ≃ (Fin n → Fin d) where
  toFun p i := p i.rev
  invFun p i := p i.rev
  left_inv p := by funext i; simp only [Fin.rev_rev]
  right_inv p := by funext i; simp only [Fin.rev_rev]

/-- An executable bijection from fixed-length port words to their ranks. -/
def wordEquiv (d n : Nat) : (Fin n → Fin d) ≃ Fin (d ^ n) :=
  (reverseWordEquiv d n).trans finFunctionFinEquiv

theorem wordEquiv_val (d n : Nat) (p : Fin n → Fin d) :
    (wordEquiv d n p).val = ∑ i : Fin n, (p i.rev).val * d ^ i.val := rfl

/-- Arithmetic prefix sums give a rank for every bounded-length address. -/
def addressEquiv (d t : Nat) : PortWords (Fin d) t ≃ Fin (addressCount d t) :=
  (Equiv.sigmaCongrRight (fun i : Fin (t + 1) => wordEquiv d i.val)).trans
    finSigmaFinEquiv

theorem addressEquiv_val (d t : Nat) (w : PortWords (Fin d) t) :
    (addressEquiv d t w).val =
      (∑ i : Fin w.1.val, d ^ i.val) + (wordEquiv d w.1.val w.2).val := by
  change (finSigmaFinEquiv
    (⟨w.1, wordEquiv d w.1.val w.2⟩ : (i : Fin (t + 1)) × Fin (d ^ i.val))).val = _
  rw [finSigmaFinEquiv_apply]
  rfl

/-- A padded label is a base-`q` integer whose digits are indexed by the
explicit bounded-address equivalence. -/
def paddedLabelEquiv (d t q : Nat) :
    PaddedLabel (Fin d) t (Fin q) ≃ Fin (q ^ addressCount d t) :=
  ((addressEquiv d t).arrowCongr (Equiv.refl (Fin q))).trans
    (wordEquiv q (addressCount d t))

theorem paddedLabelEquiv_val (d t q : Nat) (a : PaddedLabel (Fin d) t (Fin q)) :
    (paddedLabelEquiv d t q a).val =
      ∑ i : Fin (addressCount d t),
        (a ((addressEquiv d t).symm i.rev)).val * q ^ i.val := rfl

/-- False and true are the adjacent orientation digits zero and one. -/
def orientationEquiv : Bool ≃ Fin 2 := finTwoEquiv.symm

@[simp] theorem orientationEquiv_false : orientationEquiv false = 0 := rfl
@[simp] theorem orientationEquiv_true : orientationEquiv true = 1 := rfl

/-- A vertex's block consists of one adjacent orientation pair per word. -/
def dartBlockEquiv (d n : Nat) :
    ((Fin (n + 1) → Fin d) × Bool) ≃ Fin (2 * d ^ (n + 1)) :=
  ((wordEquiv d (n + 1)).prodCongr orientationEquiv).trans
    (finProdFinEquiv.trans (finCongr (Nat.mul_comm (d ^ (n + 1)) 2)))

theorem dartBlockEquiv_val (d n : Nat) (p : Fin (n + 1) → Fin d) (b : Bool) :
    (dartBlockEquiv d n (p, b)).val =
      2 * (wordEquiv d (n + 1) p).val + (orientationEquiv b).val := by
  change (orientationEquiv b).val + 2 * (wordEquiv d (n + 1) p).val = _
  exact Nat.add_comm _ _

/-- The tuple permutation putting the vertex before its word and orientation. -/
def dartVertexEquiv (vertices d n : Nat) :
    (Bool × (Fin vertices × (Fin (n + 1) → Fin d))) ≃
      (Fin vertices × ((Fin (n + 1) → Fin d) × Bool)) where
  toFun x := (x.2.1, (x.2.2, x.1))
  invFun x := (x.2.2, (x.1, x.2.1))
  left_inv x := by rcases x with ⟨b, v, p⟩; rfl
  right_inv x := by rcases x with ⟨v, p, b⟩; rfl

/-- Executable vertex-major dart numbering, with adjacent orientations. -/
def dartEquiv (vertices d n : Nat) :
    (Bool × (Fin vertices × (Fin (n + 1) → Fin d))) ≃
      Fin (2 * vertices * d ^ (n + 1)) :=
  (dartVertexEquiv vertices d n).trans
    (((Equiv.refl (Fin vertices)).prodCongr (dartBlockEquiv d n)).trans
      (finProdFinEquiv.trans
        (finCongr (show vertices * (2 * d ^ (n + 1)) =
          2 * vertices * d ^ (n + 1) by ac_rfl))))

theorem dartEquiv_val (vertices d n : Nat) (b : Bool) (v : Fin vertices)
    (p : Fin (n + 1) → Fin d) :
    (dartEquiv vertices d n (b, (v, p))).val =
      (2 * d ^ (n + 1)) * v.val +
        2 * (wordEquiv d (n + 1) p).val + (orientationEquiv b).val := by
  change (dartBlockEquiv d n (p, b)).val + (2 * d ^ (n + 1)) * v.val = _
  rw [dartBlockEquiv_val]
  omega

/-- The true orientation immediately follows the false orientation. -/
theorem dartEquiv_true_eq_false_add_one (vertices d n : Nat) (v : Fin vertices)
    (p : Fin (n + 1) → Fin d) :
    (dartEquiv vertices d n (true, (v, p))).val =
      (dartEquiv vertices d n (false, (v, p))).val + 1 := by
  rw [dartEquiv_val, dartEquiv_val, orientationEquiv_true, orientationEquiv_false]
  rfl

def encodeWord (d n : Nat) : (Fin n → Fin d) → Fin (d ^ n) := wordEquiv d n
def decodeWord (d n : Nat) : Fin (d ^ n) → (Fin n → Fin d) := (wordEquiv d n).symm

@[simp] theorem decodeWord_encodeWord (d n : Nat) (p : Fin n → Fin d) :
    decodeWord d n (encodeWord d n p) = p := (wordEquiv d n).symm_apply_apply p

@[simp] theorem encodeWord_decodeWord (d n : Nat) (i : Fin (d ^ n)) :
    encodeWord d n (decodeWord d n i) = i := (wordEquiv d n).apply_symm_apply i

def encodeAddress (d t : Nat) : PortWords (Fin d) t → Fin (addressCount d t) :=
  addressEquiv d t

def decodeAddress (d t : Nat) : Fin (addressCount d t) → PortWords (Fin d) t :=
  (addressEquiv d t).symm

@[simp] theorem decodeAddress_encodeAddress (d t : Nat) (w : PortWords (Fin d) t) :
    decodeAddress d t (encodeAddress d t w) = w := (addressEquiv d t).symm_apply_apply w

@[simp] theorem encodeAddress_decodeAddress (d t : Nat) (i : Fin (addressCount d t)) :
    encodeAddress d t (decodeAddress d t i) = i := (addressEquiv d t).apply_symm_apply i

def encodeLabel (d t q : Nat) :
    PaddedLabel (Fin d) t (Fin q) → Fin (q ^ addressCount d t) := paddedLabelEquiv d t q

def decodeLabel (d t q : Nat) :
    Fin (q ^ addressCount d t) → PaddedLabel (Fin d) t (Fin q) :=
  (paddedLabelEquiv d t q).symm

@[simp] theorem decodeLabel_encodeLabel (d t q : Nat) (a : PaddedLabel (Fin d) t (Fin q)) :
    decodeLabel d t q (encodeLabel d t q a) = a := (paddedLabelEquiv d t q).symm_apply_apply a

@[simp] theorem encodeLabel_decodeLabel (d t q : Nat) (i : Fin (q ^ addressCount d t)) :
    encodeLabel d t q (decodeLabel d t q i) = i := (paddedLabelEquiv d t q).apply_symm_apply i

@[simp] theorem decodeLabel_apply (d t q : Nat) (i : Fin (q ^ addressCount d t))
    (w : PortWords (Fin d) t) :
    decodeLabel d t q i w = decodeWord q (addressCount d t) i (encodeAddress d t w) := rfl

def encodeDart (vertices d n : Nat) :
    (Bool × (Fin vertices × (Fin (n + 1) → Fin d))) →
      Fin (2 * vertices * d ^ (n + 1)) := dartEquiv vertices d n

def decodeDart (vertices d n : Nat) :
    Fin (2 * vertices * d ^ (n + 1)) →
      (Bool × (Fin vertices × (Fin (n + 1) → Fin d))) := (dartEquiv vertices d n).symm

@[simp] theorem decodeDart_encodeDart (vertices d n : Nat)
    (e : Bool × (Fin vertices × (Fin (n + 1) → Fin d))) :
    decodeDart vertices d n (encodeDart vertices d n e) = e :=
  (dartEquiv vertices d n).symm_apply_apply e

@[simp] theorem encodeDart_decodeDart (vertices d n : Nat)
    (i : Fin (2 * vertices * d ^ (n + 1))) :
    encodeDart vertices d n (decodeDart vertices d n i) = i :=
  (dartEquiv vertices d n).apply_symm_apply i

theorem card_words (d n : Nat) : Nat.card (Fin n → Fin d) = d ^ n := by
  simpa only [Nat.card_fin] using Nat.card_congr (wordEquiv d n)

theorem card_addresses (d t : Nat) :
    Nat.card (PortWords (Fin d) t) = addressCount d t := by
  simpa only [Nat.card_fin] using Nat.card_congr (addressEquiv d t)

theorem card_labels (d t q : Nat) :
    Nat.card (PaddedLabel (Fin d) t (Fin q)) = q ^ addressCount d t := by
  simpa only [Nat.card_fin] using Nat.card_congr (paddedLabelEquiv d t q)

theorem card_darts (vertices d n : Nat) :
    Nat.card (Bool × (Fin vertices × (Fin (n + 1) → Fin d))) =
      2 * vertices * d ^ (n + 1) := by
  simpa only [Nat.card_fin] using Nat.card_congr (dartEquiv vertices d n)

theorem length_allAddresses (d t : Nat) :
    (PoweringAddresses.allAddresses d t).length = addressCount d t :=
  PoweringAddresses.length_allAddresses d t

end MaxCutGames.Foundations.PCP.PoweringEnumeration

end OAI
