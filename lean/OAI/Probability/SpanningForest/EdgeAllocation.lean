import OAI.Probability.SpanningForest.Definitions

namespace OAI

noncomputable section
namespace Problem336
namespace EdgeAllocation

def neighborRank (G : GraphCode) (key : ℕ → ℝ) (u v : ℕ) : ℕ :=
  Set.ncard {w : ℕ | Adj G u w ∧ key w < key v}

lemma neighborRank_strictMono {G : GraphCode} (hG : GraphLocallyFinite G)
    {key : ℕ → ℝ} {u v w : ℕ} (hv : Adj G u v)
    (hvw : key v < key w) : neighborRank G key u v < neighborRank G key u w := by
  apply Set.ncard_lt_ncard
  · refine Set.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · intro x hx
      exact ⟨hx.1, hx.2.trans hvw⟩
    · intro heq
      have hmem : v ∈ {x : ℕ | Adj G u x ∧ key x < key w} := ⟨hv, hvw⟩
      rw [← heq] at hmem
      exact (lt_irrefl (key v)) hmem.2
  · exact (hG u).subset (fun _ h => h.1)

lemma neighborRank_injOn {G : GraphCode} (hG : GraphLocallyFinite G)
    {key : ℕ → ℝ} (hkey : Function.Injective key) (u : ℕ) :
    Set.InjOn (neighborRank G key u) {v : ℕ | Adj G u v} := by
  intro v hv w hw hrank
  apply hkey
  rcases lt_trichotomy (key v) (key w) with hlt | heq | hgt
  · exact False.elim ((ne_of_lt (neighborRank_strictMono hG hv hlt)) hrank)
  · exact heq
  · exact False.elim ((ne_of_lt (neighborRank_strictMono hG hw hgt)) hrank.symm)

def source (key : ℕ → ℝ) (e : EdgeCode) : ℕ :=
  if key e.1.1 < key e.1.2 then e.1.1 else e.1.2

def target (key : ℕ → ℝ) (e : EdgeCode) : ℕ :=
  if key e.1.1 < key e.1.2 then e.1.2 else e.1.1

def coordinate (G : GraphCode) (key : ℕ → ℝ) (e : EdgeCode) : ℕ × ℕ :=
  (source key e, neighborRank G key (source key e) (target key e))

lemma rawPair_source_target (key : ℕ → ℝ) (e : EdgeCode) :
    rawPair (source key e) (target key e) = e.1 := by
  unfold source target
  split_ifs with h
  · simp [rawPair, e.2]
  · simp [rawPair, Nat.not_lt.mpr (Nat.le_of_lt e.2)]

lemma adjacent_source_target {G : GraphCode} {key : ℕ → ℝ} {e : EdgeCode}
    (he : Adj G e.1.1 e.1.2) : Adj G (source key e) (target key e) := by
  unfold source target
  split_ifs
  · exact he
  · unfold Adj at *
    rw [G.2.2]
    exact he

theorem coordinate_injOn {G : GraphCode} (hG : GraphLocallyFinite G)
    {key : ℕ → ℝ} (hkey : Function.Injective key) :
    Set.InjOn (coordinate G key) {e : EdgeCode | Adj G e.1.1 e.1.2} := by
  intro e he f hf hcoord
  have hs : source key e = source key f := congrArg Prod.fst hcoord
  have hr : neighborRank G key (source key e) (target key e) =
      neighborRank G key (source key f) (target key f) := congrArg Prod.snd hcoord
  rw [← hs] at hr
  have hf' : Adj G (source key e) (target key f) := by
    rw [hs]
    exact adjacent_source_target hf
  have ht := neighborRank_injOn hG hkey (source key e)
    (adjacent_source_target he) hf' hr
  apply Subtype.ext
  rw [← rawPair_source_target key e, ← rawPair_source_target key f, hs, ht]

lemma neighborRank_relabel (σ : Equiv ℕ ℕ) (G : GraphCode) (key : ℕ → ℝ)
    (u v : ℕ) :
    neighborRank (relabelGraph σ G) (relabelLabels σ key) (σ u) (σ v) =
      neighborRank G key u v := by
  unfold neighborRank
  have hset : {w : ℕ | Adj (relabelGraph σ G) (σ u) w ∧
      relabelLabels σ key w < relabelLabels σ key (σ v)} =
      σ '' {w : ℕ | Adj G u w ∧ key w < key v} := by
    ext w
    constructor
    · intro hw
      refine ⟨σ.symm w, ?_, σ.apply_symm_apply w⟩
      simpa [Adj, relabelGraph, relabelLabels] using hw
    · rintro ⟨x, hx, rfl⟩
      simpa [Adj, relabelGraph, relabelLabels] using hx
  rw [hset, Set.ncard_image_of_injective _ σ.injective]

lemma source_relabel (σ : Equiv ℕ ℕ) {key : ℕ → ℝ}
    (hkey : Function.Injective key) (e : EdgeCode) :
    source (relabelLabels σ key) (mapEdge σ e) = σ (source key e) := by
  have hne : key e.1.1 ≠ key e.1.2 := fun h => Nat.ne_of_lt e.2 (hkey h)
  by_cases hs : σ e.1.1 < σ e.1.2
  · simp [source, mapEdge, mkEdge, hs, relabelLabels]
    split_ifs <;> rfl
  · by_cases hk : key e.1.1 < key e.1.2
    · simp [source, mapEdge, mkEdge, hs, relabelLabels, hk, not_lt_of_gt hk]
    · have hr : key e.1.2 < key e.1.1 := lt_of_le_of_ne (le_of_not_gt hk) hne.symm
      simp [source, mapEdge, mkEdge, hs, relabelLabels, hk, hr]

lemma target_relabel (σ : Equiv ℕ ℕ) {key : ℕ → ℝ}
    (hkey : Function.Injective key) (e : EdgeCode) :
    target (relabelLabels σ key) (mapEdge σ e) = σ (target key e) := by
  have hne : key e.1.1 ≠ key e.1.2 := fun h => Nat.ne_of_lt e.2 (hkey h)
  by_cases hs : σ e.1.1 < σ e.1.2
  · simp [target, mapEdge, mkEdge, hs, relabelLabels]
    split_ifs <;> rfl
  · by_cases hk : key e.1.1 < key e.1.2
    · simp [target, mapEdge, mkEdge, hs, relabelLabels, hk, not_lt_of_gt hk]
    · have hr : key e.1.2 < key e.1.1 := lt_of_le_of_ne (le_of_not_gt hk) hne.symm
      simp [target, mapEdge, mkEdge, hs, relabelLabels, hk, hr]

theorem coordinate_relabel (σ : Equiv ℕ ℕ) (G : GraphCode) {key : ℕ → ℝ}
    (hkey : Function.Injective key) (e : EdgeCode) :
    coordinate (relabelGraph σ G) (relabelLabels σ key) (mapEdge σ e) =
      (σ (coordinate G key e).1, (coordinate G key e).2) := by
  simp only [coordinate, source_relabel σ hkey, target_relabel σ hkey,
    neighborRank_relabel]

end EdgeAllocation
end Problem336

end

end OAI
