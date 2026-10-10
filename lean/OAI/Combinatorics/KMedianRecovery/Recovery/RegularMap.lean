import Mathlib
import OAI.Combinatorics.KMedianRecovery.Strictness.OpenableMap
import OAI.Combinatorics.KMedianRecovery.Recovery.MergeCross

namespace OAI

namespace MetricKMedianRecovery.PhaseParameterAlignment
open PhaseSequence PhaseMergeCompletion PhaseCountCrossing
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

omit [Fintype D] [PseudoMetricSpace X] [DecidableEq X] in
lemma regular_map_eq (F : Finset X) (G : List X) (r : X → X)
    (hfix : ∀ i ∈ F, r i = i) (hG : ∀ i ∈ G, i ∈ F) : G.map r = G := by
  have he : G.map r = G.map id := List.map_congr_left (fun i hi => hfix i (hG i hi))
  simpa only [List.map_id] using he

theorem align (loc : D → X) (F B Q : Finset X) (G : List X) (r : X → X)
    (v lam lam' eta eps : ℝ) (q n k a b : ℕ)
    (hv : 0 < v) (hvsmall : v < 1/6) (hlam : 0 < lam) (heps : 0 ≤ eps)
    (hprice : lam ≤ lam')
    (herror : lam'-lam+(Fintype.card D:ℝ)*((1-3*v)*eps) ≤ (Fintype.card D:ℝ)*eta)
    (hinj : Function.Injective r) (hfix : ∀ i ∈ F, r i = i)
    (hQ : Q ⊆ F ∪ B)
    (hshrink : ∀ j, ∀ x ∈ F ∪ B, dist (loc j) (r x) ≤ dist (loc j) x)
    (hloss : ∀ j, ∀ x ∈ F ∪ B, dist (loc j) x ≤ dist (loc j) (r x)+eps)
    (hrow : ∀ i ∈ F, bidRow loc (1-3*v) ((1+v^2)^q) Q i ≤ lam)
    (hG : Valid loc F B Q v ((1+v^2)^q) lam 0 G)
    (hGr : ∀ i ∈ G, i ∈ F) (hab : Sandwich k a b) :
    Valid loc F (B.image r) (Q.image r) v ((1+v^2)^q) lam' eta G ∧
      ∃ c, Attains loc F (B.image r) (Q.image r ∪ G.toFinset) v lam' (q+1) n c ∧
        (c = k ∨ Sandwich k a c ∨ Sandwich k c b) := by
  have hbase : ∀ i ∈ F, bidRow loc (1-3*v) ((1+v^2)^q) (Q ∪ G.toFinset) i ≤ lam := by
    intro i hi
    exact (bidRow_antitone_open loc (1-3*v) _ Q (Q ∪ G.toFinset) i
      (by linarith only [hvsmall]) Finset.subset_union_left).trans (hrow i hi)
  have hG' := PhaseParameterTransfer.valid_map loc F B Q G r v _ lam lam' eta eps
    hv hvsmall (by positivity) hlam heps hprice herror hinj hfix hQ hshrink hloss hbase hG
  rw [regular_map_eq F G r hfix hGr] at hG'
  refine ⟨hG',?_⟩
  have hQ' : Q.image r ⊆ F ∪ B.image r :=
    (Finset.image_subset_image hQ).trans (PhaseParameterTransfer.image_regular_union hfix)
  obtain ⟨c,hc⟩ := attains_exists loc F (B.image r) (Q.image r ∪ G.toFinset) v lam'
    (q+1) n (Finset.union_subset hQ' hG'.1.opened_subset)
  refine ⟨c,hc,?_⟩
  unfold Sandwich at hab ⊢
  omega

end MetricKMedianRecovery.PhaseParameterAlignment

end OAI
