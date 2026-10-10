import OAI.MeasureTheory.Falconer.Estimates.TubeUniformization

namespace OAI

/-! The equal-cardinality reduction with all original incidence and
non-concentration properties retained explicitly. -/
namespace Falconer
open Set
attribute [local instance] Classical.propDecidable

theorem regularize_tube_pencils {δ b f K : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hPchart : InBoundedLineChart P) (hPsep : FiniteSeparatedAt δ P)
    (hPball : NormalizedFiniteBallBound δ f K P)
    (hT : ∀ x ∈ P, (T x).Nonempty ∧ InBoundedLineChart (T x) ∧
      FiniteSeparatedAt δ (T x) ∧ NormalizedFiniteBallBound δ b K (T x) ∧
      ∀ l ∈ T x, TubeIncident δ x l) :
    let L := Nat.log 2 (P.biUnion T).card+1
    ∃ k : ℕ, ∃ Q : Finset (Space 2), ∃ U : Space 2 → Finset (Space 2),
      Q.Nonempty ∧ Q ⊆ P ∧ (P.card : ℝ) ≤ L*(Q.card : ℝ) ∧
      InBoundedLineChart Q ∧ FiniteSeparatedAt δ Q ∧
      NormalizedFiniteBallBound δ f (K*L) Q ∧
      Q.biUnion U ⊆ P.biUnion T ∧
      ∀ x ∈ Q, (U x).card = 2^k ∧ (U x).Nonempty ∧ InBoundedLineChart (U x) ∧
        FiniteSeparatedAt δ (U x) ∧ NormalizedFiniteBallBound δ b (2*K) (U x) ∧
        ∀ l ∈ U x, TubeIncident δ x l := by
  dsimp only
  have hmax : ∀ x ∈ P, (T x).card ≤ (P.biUnion T).card := fun x hx =>
    Finset.card_le_card (Finset.subset_biUnion_of_mem T hx)
  obtain ⟨k,Q,U,hQ,hQP,hsize,hU⟩ := exists_equal_size_tube_pencils P T hP
    (fun x hx => (hT x hx).1) hmax
  refine ⟨k,Q,U,hQ,hQP,hsize,(fun x hx => hPchart x (hQP hx)),
    finiteSeparatedAt_subset hQP hPsep,
    normalized_finite_ball_bound_subset hδ.le hK hQP hsize hPball,?_,?_⟩
  · intro l hl
    obtain ⟨x,hx,hl⟩ := Finset.mem_biUnion.mp hl
    exact Finset.mem_biUnion.mpr ⟨x,hQP hx,(hU x hx).1 hl⟩
  · intro x hx
    obtain ⟨hsub,hcard,hsizeT⟩ := hU x hx
    have ht := hT x (hQP hx)
    have hsizeR : ((T x).card : ℝ) ≤ 2*((U x).card : ℝ) := by exact_mod_cast hsizeT
    refine ⟨hcard,Finset.card_pos.mp (by rw [hcard]; positivity),
      (fun l hl => ht.2.1 l (hsub hl)),finiteSeparatedAt_subset hsub ht.2.2.1,?_,
      (fun l hl => ht.2.2.2.2 l (hsub hl))⟩
    simpa only [mul_comm K 2] using
      normalized_finite_ball_bound_subset hδ.le hK hsub hsizeR ht.2.2.2.1

end Falconer

end OAI
