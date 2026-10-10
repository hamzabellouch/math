import OAI.Analysis.SphereIsometry.SpernerIncidence
import OAI.Analysis.SphereIsometry.SpernerBoundary
import OAI.Analysis.SphereIsometry.SubdivisionRestriction
import OAI.Analysis.SphereIsometry.SubdivisionIncidence
import OAI.Analysis.SphereIsometry.BarycentricZero

namespace OAI

/-!
# Geometric Sperner parity for the concrete iterated subdivisions

The labels belong to the actual recursively constructed vertex carriers.
The incidence theorem and the exact original-face restriction discharge the
finite counting hypotheses. Induction on dimension proves an odd number of
fully labelled top cells at every subdivision depth.
-/

namespace Tingley

theorem iterated_sperner_odd (m k : ℕ)
    (label : IterVertex m k → Fin (m + 1))
    (hlabel : ∀ v, label v ∈ iterCarrier m k v) :
    Odd (((topCells m k).filter
      (fun σ => σ.image label = Finset.univ)).card) := by
  classical
  induction m with
  | zero =>
      have hfull : ∀ σ ∈ topCells 0 k, σ.image label = Finset.univ := by
        intro σ hσ
        have hcard : σ.card = 1 := (mem_topCells.mp hσ).2
        have hne : σ.Nonempty := Finset.card_pos.mp (by rw [hcard]; exact Nat.zero_lt_one)
        obtain ⟨v, hv⟩ := hne
        apply Finset.eq_univ_iff_forall.mpr
        intro i
        refine Finset.mem_image.mpr ⟨v, hv, ?_⟩
        apply Fin.ext
        exact (Nat.lt_one_iff.mp (label v).isLt).trans
          (Nat.lt_one_iff.mp i.isLt).symm
      have hfilter : (topCells 0 k).filter
          (fun σ => σ.image label = Finset.univ) = topCells 0 k :=
        Finset.filter_eq_self.mpr hfull
      rw [hfilter, iter_topCells_zero_card]
      exact ⟨0, rfl⟩
  | succ m ih =>
      let e := lastFaceEmbedding m k
      have hne : ∀ v, label (e v) ≠ Fin.last (m + 1) := by
        intro v hv
        have hlast : Fin.last (m + 1) ∉ iterCarrier (m + 1) k (e v) :=
          (lastFace_range_iff m k (e v)).mpr ⟨v, rfl⟩
        exact hlast (hv ▸ hlabel (e v))
      let lowerLabel : IterVertex m k → Fin (m + 1) :=
        spernerRestrictedLabel e label hne
      have hcast : ∀ v, label (e v) = (lowerLabel v).castSucc :=
        fun v => (castSucc_spernerRestrictedLabel e label hne v).symm
      have hlower : ∀ v, lowerLabel v ∈ iterCarrier m k v := by
        apply restricted_label_mem_carrier e label hne (iterCarrier m k)
        intro v
        have h := hlabel (e v)
        change label (lastFaceEmbedding m k v) ∈
          iterCarrier (m + 1) k (lastFaceEmbedding m k v) at h
        rw [lastFace_carrier] at h
        simpa only [e, Finset.map_eq_image, Fin.coe_castSuccEmb] using h
      have hboundaryCard :
          (((codimFaces (m + 1) k).filter
            (fun τ => τ.image label = spernerSmallLabels (m + 1) ∧
              (faceCarrier (m + 1) k τ).card = m + 1)).card) =
          (((topCells m k).filter
            (fun σ => σ.image lowerLabel = Finset.univ)).card) := by
        change (((codimFaces (m + 1) k).filter
          (fun τ => τ.image label = spernerSmallLabels (m + 1) ∧
            (τ.biUnion (iterCarrier (m + 1) k)).card = m + 1)).card) = _
        rw [good_boundary_filter_eq_last_face_filter label
          (iterCarrier (m + 1) k) (codimFaces (m + 1) k) hlabel]
        exact mapped_good_family_card_of_map e label lowerLabel hcast
          (topCells m k)
          ((codimFaces (m + 1) k).filter
            (fun τ => Fin.last (m + 1) ∉ faceCarrier (m + 1) k τ))
          (lastFace_top_image m k).symm
      apply FiniteComplex.sperner_odd_of_boundary_odd
        (iterData (Fin ((m + 1) + 1)) k).complex (m + 1) label
        (fun τ => (faceCarrier (m + 1) k τ).card = m + 1)
      · intro τ hτ
        exact incidentTop_card_eq_if_boundary (Nat.succ_pos m) hτ
      · change Odd (((codimFaces (m + 1) k).filter
          (fun τ => τ.image label = spernerSmallLabels (m + 1) ∧
            (faceCarrier (m + 1) k τ).card = m + 1)).card)
        rw [hboundaryCard]
        exact ih lowerLabel hlower

/-- Each actual subdivision contains an actual fully labelled top cell. -/
theorem iterated_sperner_exists (m k : ℕ)
    (label : IterVertex m k → Fin (m + 1))
    (hlabel : ∀ v, label v ∈ iterCarrier m k v) :
    ∃ σ, σ ∈ topCells m k ∧ σ.image label = Finset.univ := by
  classical
  have hodd := iterated_sperner_odd m k label hlabel
  have hcard : ((topCells m k).filter
      (fun σ => σ.image label = Finset.univ)).card ≠ 0 := by
    intro hzero
    rw [hzero] at hodd
    simp at hodd
  obtain ⟨σ, hσ⟩ := Finset.card_ne_zero.mp hcard
  exact ⟨σ, (Finset.mem_filter.mp hσ).1, (Finset.mem_filter.mp hσ).2⟩

end Tingley

end OAI
