import OAI.Combinatorics.PlanarL1.Noncrossing

namespace OAI

section

namespace PlanarL1
/-! ## Finite switching paths in the manuscript's column models
A switch retains height and has zero cost. Between switches a path travels
vertically; its length is the sum of all vertical variations. The band argument
below does not identify an ambient distance with a band distance. -/
namespace Columns

/-- Neighbors in the cyclic order, including the wrap-around edge. -/
def Consecutive {n : ℕ} (i j : Fin n) : Prop :=
  i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
    (i.val = 0 ∧ j.val + 1 = n) ∨ (j.val = 0 ∧ i.val + 1 = n)

/-- The data and standing hypotheses of a column model.
Only the actual prescribed switch heights identify columns. -/
structure Model (n : ℕ) where
  link : SimpleGraph (Fin n)
  heights : Fin n → Fin n → Set ℝ
  symm : ∀ i j, heights i j = heights j i
  permitted : ∀ i j H, H ∈ heights i j → link.Adj i j
  compact : ∀ i j, IsCompact (heights i j)
  noncrossing : ColumnOrder.Noncrossing link
  terminal : ∀ i j, link.Adj i j → ¬ Consecutive i j →
    ∃ H, heights i j = {H} ∧ ∀ k T,
      (T ∈ heights i k ∨ T ∈ heights j k) → T ≤ H

namespace Model

variable {n : ℕ} (M : Model n)

/-- A link is active in a band exactly when it has an allowed height there. -/
def activeGraph (J : Set ℝ) : SimpleGraph (Fin n) where
  Adj i j := ∃ H ∈ J, H ∈ M.heights i j
  symm := ⟨by
    intro i j
    rintro ⟨H, hH, h⟩
    exact ⟨H, hH, by rwa [M.symm i j] at h⟩⟩
  loopless := ⟨by
    intro i
    rintro ⟨H, _, h⟩
    exact M.link.loopless.irrefl i (M.permitted i i H h)⟩

lemma active_subgraph (J : Set ℝ) : M.activeGraph J ≤ M.link := by
  rintro i j ⟨H, _, h⟩
  exact M.permitted i j H h

lemma active_noncrossing (J : Set ℝ) : ColumnOrder.Noncrossing (M.activeGraph J) := by
  intro a b c d hab hbc hcd h
  exact M.noncrossing a b c d hab hbc hcd
    ⟨M.active_subgraph J h.1, M.active_subgraph J h.2⟩

/-- A finite column word with an allowed band-switch height at every step.
Endpoint heights are supplied separately; the nil word is a vertical segment. -/
inductive Path (J : Set ℝ) : Fin n → Fin n → Type
  | nil (i : Fin n) : Path J i i
  | cons {i j k : Fin n} (H : ℝ) (inBand : H ∈ J)
      (switch : H ∈ M.heights i j) (tail : Path J j k) : Path J i k

namespace Path

variable {M} {J : Set ℝ} {i j k : Fin n}

/-- Source length: sum of the lengths of vertical segments, with switches free. -/
def length : {i j : Fin n} → M.Path J i j → ℝ → ℝ → ℝ
  | _, _, .nil _, a, b => |a - b|
  | _, _, .cons H _ _ p, a, b => |a - H| + p.length H b

/-- The associated walk in the active column graph, used for planar separation. -/
def word : {i j : Fin n} → M.Path J i j → (M.activeGraph J).Walk i j
  | _, _, .nil _ => .nil
  | _, _, .cons H hH hs p => .cons ⟨H, hH, hs⟩ p.word

lemma length_nonneg (p : M.Path J i j) (a b : ℝ) : 0 ≤ p.length a b := by
  induction p generalizing a with
  | nil => exact abs_nonneg _
  | cons H _ _ p ih => exact add_nonneg (abs_nonneg _) (ih H)

lemma height_change_le (p : M.Path J i j) (a b : ℝ) : |a - b| ≤ p.length a b := by
  induction p generalizing a with
  | nil => exact le_rfl
  | cons H hH hs p ih =>
    dsimp only [length]
    linarith [abs_sub_le a H b, ih H]

/-- Moving just the final endpoint vertically changes a path length by at most
that vertical distance. The intermediate switch heights stay unchanged. -/
lemma length_end_le (p : M.Path J i j) (a b c : ℝ) :
    p.length a c ≤ p.length a b + |b - c| := by
  induction p generalizing a with
  | nil => exact abs_sub_le a b c
  | cons H hH hs p ih =>
    dsimp only [length]
    linarith [ih H]

lemma length_start_le (p : M.Path J i j) (a b c : ℝ) :
    p.length a c ≤ |a - b| + p.length b c := by
  cases p with
  | nil => exact abs_sub_le a b c
  | cons H hH hs p =>
    dsimp only [length]
    linarith [abs_sub_le a b H]

/-- Concatenate switching words. Any redundant final/initial vertical detour at
the common column is removed, so length can only decrease. -/
def append : {i j k : Fin n} → M.Path J i j → M.Path J j k → M.Path J i k
  | _, _, _, .nil _, q => q
  | _, _, _, .cons H hH hs p, q => .cons H hH hs (p.append q)

lemma length_append_le (p : M.Path J i j) (q : M.Path J j k) (a b c : ℝ) :
    (p.append q).length a c ≤ p.length a b + q.length b c := by
  induction p generalizing a with
  | nil => exact q.length_start_le a b c
  | cons H hH hs p ih =>
    dsimp only [length, append]
    linarith [ih q H]

/-- Adjoin one final switch at height `H`. -/
def snoc (p : M.Path J i j) (H : ℝ) (hH : H ∈ J) (hs : H ∈ M.heights j k) :
    M.Path J i k := p.append (.cons H hH hs (.nil k))

lemma length_snoc (p : M.Path J i j) (H : ℝ) (hH : H ∈ J)
    (hs : H ∈ M.heights j k) (a b : ℝ) :
    (p.snoc H hH hs).length a b = p.length a H + |H - b| := by
  induction p generalizing a with
  | nil => rfl
  | cons T hT ht p ih =>
    dsimp only [snoc, append, length] at *
    rw [ih]
    ring

/-- Reverse the column word and all its zero-cost switches. -/
def reverse : {i j : Fin n} → M.Path J i j → M.Path J j i
  | _, _, .nil _ => .nil _
  | _, _, .cons H hH hs p => p.reverse.snoc H hH (by rwa [M.symm] at hs)

lemma length_reverse (p : M.Path J i j) (a b : ℝ) :
    p.reverse.length b a = p.length a b := by
  induction p generalizing a with
  | nil => exact abs_sub_comm b a
  | cons H hH hs p ih =>
    dsimp only [reverse]
    rw [length_snoc, ih]
    dsimp only [length]
    rw [abs_sub_comm H a, add_comm]

/-- Every walk in the active graph really is a switching path: one chooses an
available height independently for each prescribed switch. -/
lemma exists_word (p : (M.activeGraph J).Walk i j) :
    ∃ q : M.Path J i j, q.word = p := by
  induction p with
  | nil => exact ⟨.nil _, rfl⟩
  | cons h p ih =>
    obtain ⟨H, hH, hs⟩ := h
    obtain ⟨q, hq⟩ := ih
    exact ⟨.cons H hH hs q, by simp only [word, hq]⟩

/-- A visit in a column word admits a genuine length-exact split at a height
in the band. This keeps paths that leave an individual radial cell available. -/
lemma split_at_column (p : M.Path J i j) {a b : ℝ} (ha : a ∈ J) (_hb : b ∈ J)
    {v : Fin n} (hv : v ∈ p.word.support) :
    ∃ H ∈ J, ∃ (q : M.Path J i v) (r : M.Path J v j),
      q.length a H + r.length H b = p.length a b := by
  induction p generalizing a with
  | nil i =>
    have hvi : v = i := by simpa only [word, SimpleGraph.Walk.support_nil,
      List.mem_singleton] using hv
    subst v
    exact ⟨a, ha, .nil _, .nil _, by simp only [length, sub_self, abs_zero, zero_add]⟩
  | @cons i z j H hH hs p ih =>
    rcases List.mem_cons.mp hv with hvi | hv
    · subst v
      exact ⟨a, ha, .nil _, .cons H hH hs p,
        by simp only [length, sub_self, abs_zero, zero_add]⟩
    · obtain ⟨T, hT, q, r, hqr⟩ := ih hH hv
      refine ⟨T, hT, .cons H hH hs q, r, ?_⟩
      dsimp only [length]
      linarith

/-- Split a vertical segment at a prescribed traveled length, remaining in
its closed interval. This is valid for every interval band in the paper. -/
lemma vertical_split (hJ : Set.OrdConnected J) {a b ℓ : ℝ}
    (ha : a ∈ J) (hb : b ∈ J) (hℓ : 0 ≤ ℓ) (hbound : ℓ ≤ |a - b|) :
    ∃ T ∈ J, |a - T| = ℓ ∧ |T - b| = |a - b| - ℓ := by
  by_cases hab : a ≤ b
  · have hlen : |a - b| = b - a := by rw [abs_of_nonpos (by linarith)]; ring
    refine ⟨a + ℓ, hJ.out ha hb ⟨by linarith, by rw [hlen] at hbound; linarith⟩, ?_, ?_⟩
    · rw [abs_of_nonpos (by linarith)]; ring
    · rw [abs_of_nonpos (by rw [hlen] at hbound; linarith), hlen]; ring
  · have hlen : |a - b| = a - b := abs_of_nonneg (by linarith)
    refine ⟨a - ℓ, hJ.out hb ha ⟨by rw [hlen] at hbound; linarith, by linarith⟩, ?_, ?_⟩
    · rw [abs_of_nonneg (by linarith)]; ring
    · rw [abs_of_nonneg (by rw [hlen] at hbound; linarith), hlen]; ring

/-- Every intermediate arclength is attained on a switching path in an
interval band, by actual finite prefix and suffix paths. No abstract length
space or geodesicity hypothesis is added. -/
lemma split_at_length (hJ : Set.OrdConnected J) (p : M.Path J i j)
    {a b ℓ : ℝ} (ha : a ∈ J) (hb : b ∈ J) (hℓ : 0 ≤ ℓ)
    (hbound : ℓ ≤ p.length a b) :
    ∃ (k : Fin n) (T : ℝ), T ∈ J ∧
      ∃ (q : M.Path J i k) (r : M.Path J k j),
        q.length a T = ℓ ∧ r.length T b = p.length a b - ℓ := by
  induction p generalizing a ℓ with
  | nil i =>
    obtain ⟨T, hT, h₁, h₂⟩ := vertical_split hJ ha hb hℓ hbound
    exact ⟨i, T, hT, .nil _, .nil _, h₁, h₂⟩
  | @cons i k j H hH hs p ih =>
    by_cases hfirst : ℓ ≤ |a - H|
    · obtain ⟨T, hT, h₁, h₂⟩ := vertical_split hJ ha hH hℓ hfirst
      refine ⟨i, T, hT, .nil _, .cons H hH hs p, h₁, ?_⟩
      dsimp only [length]
      rw [h₂]
      ring
    · have htail : ℓ - |a - H| ≤ p.length H b := by
        change ℓ ≤ |a - H| + p.length H b at hbound
        linarith
      obtain ⟨v, T, hT, q, r, hq, hr⟩ := ih hH (by linarith) htail
      refine ⟨v, T, hT, .cons H hH hs q, r, ?_, ?_⟩
      · dsimp only [length]
        linarith
      · dsimp only [length]
        linarith

/-- A finite switching word from outside a column set to inside it has a
crossing switch. The decomposition retains the exact metric length, including
both endpoint vertical segments. -/
lemma crosses_set (p : M.Path J i j) (S : Set (Fin n)) (hi : i ∉ S) (hj : j ∈ S)
    (a b : ℝ) :
    ∃ (u v : Fin n) (H : ℝ) (_hH : H ∈ J) (_hs : H ∈ M.heights u v),
      u ∉ S ∧ v ∈ S ∧ ∃ (q : M.Path J i u) (r : M.Path J v j),
        q.length a H + r.length H b = p.length a b := by
  classical
  induction p generalizing a with
  | nil => exact False.elim (hi hj)
  | @cons i z j H hH hs p ih =>
    by_cases hz : z ∈ S
    · exact ⟨i, z, H, hH, hs, hi, hz, .nil _, p, rfl⟩
    · obtain ⟨u, v, T, hT, ht, hu, hv, q, r, he⟩ := ih hz hj H
      refine ⟨u, v, T, hT, ht, hu, hv, .cons H hH hs q, r, ?_⟩
      dsimp only [length] at *
      linarith

/-- Deleting a prefix up to a visited column cannot increase vertical
variation, even when the new initial height is the old initial height. -/
lemma suffix_at_column (p : M.Path J i j) (a b : ℝ) {v : Fin n}
    (hv : v ∈ p.word.support) :
    ∃ r : M.Path J v j, r.word.support.Sublist p.word.support ∧
      r.length a b ≤ p.length a b := by
  induction p generalizing a with
  | nil i =>
    have hvi : v = i := by simpa only [word, SimpleGraph.Walk.support_nil,
      List.mem_singleton] using hv
    subst v
    exact ⟨.nil _, List.Sublist.refl _, le_rfl⟩
  | @cons i z j H hH hs p ih =>
    rcases List.mem_cons.mp hv with hvi | hv
    · subst v
      exact ⟨.cons H hH hs p, List.Sublist.refl _, le_rfl⟩
    · obtain ⟨r, hr, hlen⟩ := ih H hv
      refine ⟨r, hr.trans (List.sublist_cons_self _ _), ?_⟩
      exact (r.length_start_le a H b).trans (add_le_add (le_refl _) hlen)

/-- Loop erasure with its essential metric estimate: replacing a detour by
vertical travel never increases length. The resulting word has no repeated
column, so the later minimization is over finitely many words. -/
lemma simple_replacement (p : M.Path J i j) (a b : ℝ) :
    ∃ q : M.Path J i j, q.word.IsPath ∧ q.length a b ≤ p.length a b := by
  classical
  induction p generalizing a with
  | nil i => exact ⟨.nil i, by simp [word], le_rfl⟩
  | @cons i z j H hH hs p ih =>
    obtain ⟨q, hq, hlen⟩ := ih H
    by_cases hi : i ∈ q.word.support
    · obtain ⟨r, hr, hlenr⟩ := q.suffix_at_column H b hi
      refine ⟨r, ?_, ?_⟩
      · exact SimpleGraph.Walk.IsPath.mk' (hq.support_nodup.sublist hr)
      · exact (r.length_start_le a H b).trans
          (add_le_add (le_refl _) (hlenr.trans hlen))
    · refine ⟨.cons H hH hs q, ?_, add_le_add (le_refl _) hlen⟩
      exact SimpleGraph.Walk.IsPath.mk' (List.nodup_cons.mpr ⟨hi, hq.support_nodup⟩)

/-- Zero length is possible only at one common height, through switches all
available at exactly that height. -/
lemma zero_length_identifies (p : M.Path J i j) (a b : ℝ)
    (h : p.length a b = 0) :
    a = b ∧ (M.activeGraph {a}).Reachable i j := by
  induction p generalizing a with
  | nil =>
    exact ⟨sub_eq_zero.mp (abs_eq_zero.mp h), .refl _⟩
  | @cons i k j H hH hs p ih =>
    have ht : p.length H b = 0 := by
      have := p.length_nonneg H b
      have := abs_nonneg (a - H)
      dsimp only [length] at h
      linarith
    have ha : a = H := by
      have hn := p.length_nonneg H b
      have hz : |a - H| = 0 := by dsimp only [length] at h; linarith [abs_nonneg (a-H)]
      exact sub_eq_zero.mp (abs_eq_zero.mp hz)
    obtain ⟨hb, hr⟩ := ih H ht
    subst a
    exact ⟨hb, (show (M.activeGraph {H}).Adj i k from ⟨H, rfl, hs⟩).reachable.trans hr⟩

lemma exists_zero_path (H : ℝ) (hH : H ∈ J) (w : (M.activeGraph {H}).Walk i j) :
    ∃ p : M.Path J i j, p.length H H = 0 := by
  induction w with
  | nil => exact ⟨.nil _, by simp only [length, sub_self, abs_zero]⟩
  | @cons i k j hk p ih =>
    obtain ⟨q, hq⟩ := ih
    obtain ⟨T, hT, hs⟩ := hk
    have he : T = H := hT
    subst T
    exact ⟨.cons H hH hs q,
      by simp only [length, sub_self, abs_zero, zero_add, hq]⟩

end Path

/-- A schedule specifies one allowed height for each edge of a fixed word.
This recursive finite product carries its usual compact topology when the band
is closed. -/
def Schedule (J : Set ℝ) : {i j : Fin n} → (M.activeGraph J).Walk i j → Type
  | _, _, .nil => PUnit
  | _, _, @SimpleGraph.Walk.cons _ _ i k _ _ p =>
      ↥(M.heights i k ∩ J) × Schedule J p

namespace Schedule

variable {M} {J : Set ℝ} {i j : Fin n}

noncomputable instance topology (w : (M.activeGraph J).Walk i j) : TopologicalSpace (M.Schedule J w) := by
  induction w with
  | nil => exact inferInstanceAs (TopologicalSpace PUnit)
  | @cons i k j h p ih =>
    change TopologicalSpace (↥(M.heights i k ∩ J) × M.Schedule J p)
    letI := ih
    infer_instance

lemma compactSpace (hJ : IsClosed J) (w : (M.activeGraph J).Walk i j) :
    CompactSpace (M.Schedule J w) := by
  induction w with
  | nil => exact inferInstanceAs (CompactSpace PUnit)
  | @cons i k j h p ih =>
    have hc := (M.compact i k).inter_right hJ
    let : CompactSpace ↥(M.heights i k ∩ J) := isCompact_iff_compactSpace.mp hc
    let := ih
    exact inferInstanceAs (CompactSpace (↥(M.heights i k ∩ J) × M.Schedule J p))

/-- Realize a schedule as the literal switching path of the fixed word. -/
def toPath : {i j : Fin n} → {w : (M.activeGraph J).Walk i j} →
    M.Schedule J w → M.Path J i j
  | i, _, .nil, _ => .nil i
  | _, _, .cons _ _, s => .cons s.1.val s.1.property.2 s.1.property.1 (toPath s.2)

lemma word_toPath {w : (M.activeGraph J).Walk i j} (s : M.Schedule J w) :
    (toPath s).word = w := by
  induction w with
  | nil => rfl
  | cons h p ih =>
    change SimpleGraph.Walk.cons _ (toPath s.2).word = .cons h p
    rw [ih]

def ofPath : {i j : Fin n} → (p : M.Path J i j) → M.Schedule J p.word
  | _, _, .nil _ => PUnit.unit
  | _, _, .cons H hH hs p => (⟨H, hs, hH⟩, ofPath p)

lemma toPath_ofPath (p : M.Path J i j) : toPath (ofPath p) = p := by
  induction p with
  | nil => rfl
  | cons H hH hs p ih =>
    change Path.cons H hH hs (toPath (ofPath p)) = _
    rw [ih]

/-- Length is a continuous function of all endpoint and switch heights. -/
lemma continuous_length {T : Type*} [TopologicalSpace T]
    (w : (M.activeGraph J).Walk i j) (a b : T → ℝ) (s : T → M.Schedule J w)
    (ha : Continuous a) (hb : Continuous b) (hs : Continuous s) :
    Continuous (fun t => (toPath (s t)).length (a t) (b t)) := by
  induction w generalizing a b with
  | nil => exact (ha.sub hb).abs
  | @cons i k j h p ih =>
    have hH : Continuous (fun t => ((s t).1 : ℝ)) := continuous_subtype_val.comp hs.fst
    exact ((ha.sub hH).abs).add (ih _ b (fun t => (s t).2) hH hb hs.snd)

end Schedule

/-- Points before quotienting, in one component of the intrinsic band. -/
structure Point (J : Set ℝ) (root : Fin n) where
  column : Fin n
  height : ℝ
  inBand : height ∈ J
  reachable : (M.activeGraph J).Reachable root column

end Model
end Columns
end PlanarL1

end

end OAI
