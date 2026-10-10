import OAI.NumberTheory.Ostmann.Arithmetic.HistoryActiveCoordinates
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightSourceXi

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryActiveCoordinates
open Construction HistoryOccurrenceVariables HistorySymbolicEncoding PrimeCellFreezing
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [Fintype κ] in
theorem sourceDomain_insert_exp (b k : ℕ) (G : ℝ) (center : ℕ → ℝ)
    {l : ℕ} (h : History l) (m : Key h → κ) (I : Finset κ)
    (background : κ → ℝ) (lo hi : I → ℝ)
    (hbackground : SourceDomain b k G center h (fun i => background (m i)))
    (hsource : ∀ i q, independentSlot h i=some q → q.role≠.bulk → ∀ hm : m i∈I,
      center q.origin-1 ≤ lo ⟨m i,hm⟩ ∧ hi ⟨m i,hm⟩ ≤ center q.origin+1)
    (hgiant : ∀ a : Bool, ∀ hm : m (Sum.inl a)∈I,
      G-1 ≤ lo ⟨m (Sum.inl a),hm⟩ ∧ hi ⟨m (Sum.inl a),hm⟩ ≤ G+1)
    (z : I → ℝ) (hz : z∈logRectangle lo hi) :
    SourceDomain b k G center h (fun i => insert I background (fun j => Real.exp (z j)) (m i)) := by
  constructor
  · intro i
    unfold insert
    split_ifs with hm
    · exact Real.exp_pos _
    · exact hbackground.positive i
  · intro i q hiq hq
    by_cases hm : m i∈I
    · have hs := hsource i q hiq hq hm
      have hzi := hz ⟨m i,hm⟩ (Set.mem_univ _)
      simp only [insert,dite_eq_left hm,Real.log_exp]
      exact abs_le.mpr ⟨by linarith [hs.1,hzi.1],by linarith [hs.2,hzi.2]⟩
    · simpa only [insert,dite_eq_right hm] using hbackground.source i q hiq hq
  · intro a
    by_cases hm : m (Sum.inl a)∈I
    · have hs := hgiant a hm
      have hzi := hz ⟨m (Sum.inl a),hm⟩ (Set.mem_univ _)
      simp only [insert,dite_eq_left hm,Real.log_exp]
      exact abs_le.mpr ⟨by linarith [hs.1,hzi.1],by linarith [hs.2,hzi.2]⟩
    · simpa only [insert,dite_eq_right hm] using hbackground.giant a
  · exact hbackground.leaves

structure SourceBounds (b k : ℕ) (G : ℝ) (center : ℕ → ℝ)
    {l : ℕ} (h : History l) (m : Key h → κ) (I : Finset κ)
    (background : κ → ℝ) (lo hi : I → ℝ) : Prop where
  background_source : SourceDomain b k G center h (fun i => background (m i))
  source : ∀ i q, independentSlot h i=some q → q.role≠.bulk → ∀ hm : m i∈I,
    center q.origin-1 ≤ lo ⟨m i,hm⟩ ∧ hi ⟨m i,hm⟩ ≤ center q.origin+1
  giant : ∀ a : Bool, ∀ hm : m (Sum.inl a)∈I,
    G-1 ≤ lo ⟨m (Sum.inl a),hm⟩ ∧ hi ⟨m (Sum.inl a),hm⟩ ≤ G+1

omit [Fintype κ] in
theorem SourceBounds.sourceDomain {b k : ℕ} {G : ℝ} {center : ℕ → ℝ}
    {l : ℕ} {h : History l} {m : Key h → κ} {I : Finset κ}
    {background : κ → ℝ} {lo hi : I → ℝ}
    (hh : SourceBounds b k G center h m I background lo hi)
    (z : I → ℝ) (hz : z∈logRectangle lo hi) :
    SourceDomain b k G center h (fun i => insert I background (fun j => Real.exp (z j)) (m i)) :=
  sourceDomain_insert_exp b k G center h m I background lo hi hh.background_source hh.source hh.giant z hz

end Ostmann.Arithmetic.HistoryActiveCoordinates

end

end OAI
