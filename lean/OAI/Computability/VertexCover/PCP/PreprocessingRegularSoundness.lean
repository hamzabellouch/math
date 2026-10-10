import Mathlib
import OAI.Computability.VertexCover.PCP.PreprocessingTables

namespace OAI

                                                                                                      

namespace UniqueGames.Foundations.PCP.PreprocessingRegularSoundness

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

end UniqueGames.Foundations.PCP.PreprocessingRegularSoundness

end OAI
