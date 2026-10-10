import OAI.Analysis.SphereIsometry.SubdivisionData
import OAI.Analysis.SphereIsometry.BarycentricIncidence

namespace OAI

/-!
# Incidence counts for the concrete iterated simplex

The missing-rank alternative for an actual flag transports the old boundary
count, or gives two completions around a retained old top face. Iteration
therefore gives one incident top cell on the original boundary and two in
the interior.
-/

noncomputable section

namespace Tingley

/-- At depth zero the unique top cell is the full original vertex set. -/
theorem incidentTop_zero_eq_singleton (m : ℕ) (s : Finset (IterVertex m 0)) :
    incidentTop m 0 s = {Finset.univ} := by
  classical
  change Finset (Fin (m + 1)) at s
  change (FiniteComplex.full : FiniteComplex (Fin (m + 1))).incidentTop m s =
    {Finset.univ}
  ext t
  rw [FiniteComplex.mem_incidentTop, Finset.mem_singleton]
  constructor
  · rintro ⟨_, ht, _⟩
    exact t.eq_univ_of_card (by simpa only [Fintype.card_fin] using ht)
  · rintro rfl
    exact ⟨FiniteComplex.mem_full _, Finset.card_fin _, Finset.subset_univ _⟩

/-- The initial carrier of a face is that face itself. -/
theorem faceCarrier_zero (m : ℕ) (s : Finset (IterVertex m 0)) :
    faceCarrier m 0 s = s := by
  change Finset (Fin (m + 1)) at s
  change s.biUnion (fun i => {i}) = s
  exact Finset.biUnion_singleton_eq_self

/-- Actual codimension-one incidence for every positive-dimensional iterated
standard simplex. The boundary condition refers to the original coordinates. -/
theorem incidentTop_card_eq_if_boundary {m k : ℕ} (hm : 0 < m) :
    ∀ {s : Finset (IterVertex m k)}, s ∈ codimFaces m k →
      (incidentTop m k s).card =
        if (faceCarrier m k s).card = m then 1 else 2 := by
  classical
  induction k with
  | zero =>
      intro s hs
      have hcard := (mem_codimFaces.mp hs).2
      have hface : (faceCarrier m 0 s).card = m :=
        (congrArg (fun t : Finset (Fin (m + 1)) => t.card)
          (faceCarrier_zero m s)).trans hcard
      rw [incidentTop_zero_eq_singleton, Finset.card_singleton, ite_eq_left hface]
  | succ k ih =>
      intro s hs
      let K := (iterData (Fin (m + 1)) k).complex
      have hK : K.CardBound m := by
        intro t ht
        exact iter_card_le ht
      change s ∈ K.sd.codimFaces m at hs
      rcases FiniteComplex.incidentTop_sd_cases hm hK hs with
        ⟨hcount, T, hTs, hTcard, hmax⟩ | ⟨T, hTs, hTcard, hmax, hcount⟩
      · have hcarrier : faceCarrier m (k + 1) s = faceCarrier m k T.val :=
          FiniteComplex.faceCarrier_sd_eq_greatest hTs hmax
        have htop : T.val ∈ topCells m k :=
          mem_topCells.mpr ⟨T.property.1, hTcard⟩
        have hnot : (Finset.univ : Finset (Fin (m + 1))).card ≠ m := by simp
        rw [hcarrier, top_faceCarrier htop, ite_eq_right hnot]
        exact hcount
      · have hcarrier : faceCarrier m (k + 1) s = faceCarrier m k T.val :=
          FiniteComplex.faceCarrier_sd_eq_greatest hTs hmax
        have hcodim : T.val ∈ codimFaces m k :=
          mem_codimFaces.mpr ⟨T.property.1, hTcard⟩
        calc
          (incidentTop m (k + 1) s).card = (incidentTop m k T.val).card := hcount
          _ = if (faceCarrier m k T.val).card = m then 1 else 2 := ih hcodim
          _ = if (faceCarrier m (k + 1) s).card = m then 1 else 2 := by rw [hcarrier]

end Tingley

end

end OAI
