import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Success

namespace OAI

namespace MetricKMedianRecovery.PhaseCountCrossing
open PhaseSequence PhaseMergePath PhaseMergeRefinement PhaseMergeCompletion
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

omit [Fintype D] [PseudoMetricSpace X] in
lemma disjoint_pool (F B : Finset X) (copy : X → X) (hdis : Disjoint F B)
    (hc : ∀ i ∈ F, copy i ∉ F ∪ B) : Disjoint F (pool F B copy) := by
  rw [Finset.disjoint_left]
  intro x hx hxpool
  rcases Finset.mem_union.mp hxpool with hxB | hxc
  · exact Finset.disjoint_left.mp hdis hx hxB
  · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hxc
    exact hc i hi (Finset.mem_union_left _ hx)

theorem regular_phase_crossing (loc : D → X) (F B Q : Finset X) (copy spare : X → X)
    (v lam eta : ℝ) (q n k a b : ℕ) (hv : 0 < v) (hvsmall : v < 1/6)
    (hlam : 0 < lam) (heta : 0 ≤ eta) (hQ : Q ⊆ F ∪ B) (hdis : Disjoint F B)
    (hrow : ∀ i ∈ F, bidRow loc (1-3*v) ((1+v^2)^q) Q i ≤ lam)
    (hc : ∀ i ∈ F, copy i ∉ F ∪ B)
    (hd : ∀ i ∈ F, ∀ j, dist (loc j) i = dist (loc j) (copy i))
    (hs : ∀ i ∈ F, spare i ∉ F ∪ pool F B copy)
    (he : ∀ i ∈ F, ∀ j, dist (loc j) i = dist (loc j) (spare i))
    (H G : List X) (hH : Valid loc F B Q v ((1+v^2)^q) lam eta H)
    (hG : Valid loc F B Q v ((1+v^2)^q) lam eta G)
    (hHr : ∀ i ∈ H, i ∈ F) (hGr : ∀ i ∈ G, i ∈ F) (hab : Sandwich k a b)
    (ha : Attains loc F B (Q ∪ H.toFinset) v lam (q+1) n a)
    (hb : Attains loc F B (Q ∪ G.toFinset) v lam (q+1) n b) :
    Outcome loc F (pool F (pool F B copy) spare) Q v lam eta q n k := by
  obtain ⟨m,_,hchain⟩ := regular_phase_chain loc F B Q copy spare v ((1+v^2)^q)
    lam eta hv hvsmall (by positivity) hlam heta hQ hdis hrow hc hd hs he H G hH hG hHr hGr
  have hB : B ⊆ pool F (pool F B copy) spare :=
    (subset_pool F B copy).trans (subset_pool F (pool F B copy) spare)
  exact chain_crossing loc F (pool F (pool F B copy) spare) Q v lam eta q n k
    (hQ.trans (Finset.union_subset_union_right hB))
    (disjoint_pool F (pool F B copy) spare (disjoint_pool F B copy hdis hc) hs)
    (by linarith only [hvsmall]) hlam hchain hab (ha.mono_free hB) (hb.mono_free hB)

end MetricKMedianRecovery.PhaseCountCrossing

namespace MetricKMedianRecovery.PriceBisection

def refine (count : ℚ → ℕ) (h : ℕ) (I : ℚ × ℚ) : ℚ × ℚ :=
  let mid := (I.1+I.2)/2
  if h ≤ count mid then (mid,I.2) else (I.1,mid)

def search (count : ℚ → ℕ) (h : ℕ) : ℕ → ℚ × ℚ → ℚ × ℚ
  | 0,I => I
  | n+1,I => search count h n (refine count h I)

lemma refine_bounds (count : ℚ → ℕ) (h : ℕ) (a b : ℚ) (hab : a ≤ b) :
    a ≤ (refine count h (a,b)).1 ∧
    (refine count h (a,b)).1 ≤ (refine count h (a,b)).2 ∧
    (refine count h (a,b)).2 ≤ b := by
  dsimp only [refine]
  split_ifs <;> dsimp
  · exact ⟨by linarith, by linarith, le_rfl⟩
  · exact ⟨le_rfl, by linarith, by linarith⟩

lemma refine_width (count : ℚ → ℕ) (h : ℕ) (a b : ℚ) :
    (refine count h (a,b)).2-(refine count h (a,b)).1 = (b-a)/2 := by
  dsimp only [refine]
  split_ifs <;> dsimp <;> ring

lemma refine_bracket (count : ℚ → ℕ) (h : ℕ) (a b : ℚ)
    (ha : h ≤ count a) (hb : count b ≤ h) :
    h ≤ count (refine count h (a,b)).1 ∧ count (refine count h (a,b)).2 ≤ h := by
  dsimp only [refine]
  split_ifs with hm
  · exact ⟨hm,hb⟩
  · exact ⟨ha,(Nat.lt_of_not_ge hm).le⟩

lemma search_spec (count : ℚ → ℕ) (h n : ℕ) (a b : ℚ) (hab : a ≤ b)
    (ha : h ≤ count a) (hb : count b ≤ h) :
    let I := search count h n (a,b)
    a ≤ I.1 ∧ I.1 ≤ I.2 ∧ I.2 ≤ b ∧
      h ≤ count I.1 ∧ count I.2 ≤ h ∧ I.2-I.1 = (b-a)/2^n := by
  induction n generalizing a b with
  | zero =>
    simp only [search,pow_zero,div_one]
    exact ⟨le_rfl,hab,le_rfl,ha,hb,True.intro⟩
  | succ n ih =>
    obtain ⟨hlo,hm,hhi⟩ := refine_bounds count h a b hab
    obtain ⟨hcl,hch⟩ := refine_bracket count h a b ha hb
    obtain ⟨hl',he',hh',hcl',hch',hw'⟩ := ih _ _ hm hcl hch
    refine ⟨hlo.trans hl',he',hh'.trans hhi,hcl',hch',?_⟩
    change (search count h n (refine count h (a,b))).2 -
      (search count h n (refine count h (a,b))).1 = _
    rw [hw',refine_width,pow_succ]
    ring

def iterations (a b : ℚ) (N : ℕ) : ℕ := N + Nat.clog 2 (Nat.ceil (b-a))

lemma iterations_precision (a b : ℚ) (N : ℕ) :
    (b-a) / (2:ℚ) ^ iterations a b N ≤ 1 / (2:ℚ)^N := by
  have hwidth : b-a ≤ (2:ℚ)^(Nat.clog 2 (Nat.ceil (b-a))) := by
    exact (Nat.le_ceil (b-a)).trans (by exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) (Nat.ceil (b-a)))
  unfold iterations
  rw [pow_add]
  apply (div_le_iff₀ (by positivity : (0:ℚ) < 2^N*2^(Nat.clog 2 (Nat.ceil (b-a))))).mpr
  simpa using hwidth

theorem close_bracket (count : ℚ → ℕ) (h N : ℕ) (a b : ℚ) (hab : a ≤ b)
    (ha : h ≤ count a) (hb : count b ≤ h) :
    ∃ l u : ℚ, a ≤ l ∧ l ≤ u ∧ u ≤ b ∧ u-l ≤ 1/(2:ℚ)^N ∧
      h ≤ count l ∧ count u ≤ h := by
  let I := search count h (iterations a b N) (a,b)
  obtain ⟨hl,hle,hu,hcl,hcu,hw⟩ := search_spec count h (iterations a b N) a b hab ha hb
  refine ⟨I.1,I.2,hl,hle,hu,?_,hcl,hcu⟩
  exact hw ▸ iterations_precision a b N

end MetricKMedianRecovery.PriceBisection

end OAI
