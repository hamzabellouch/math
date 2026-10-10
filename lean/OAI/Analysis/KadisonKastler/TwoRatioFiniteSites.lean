import OAI.Analysis.KadisonKastler.TwoRatioReindex
import Mathlib.Data.List.Range
import Mathlib.Data.List.Nodup

namespace OAI

/-! # Finite stages and unused sites in the two-ratio product -/

namespace KadisonKastler

def twoRatioFiniteSites (n : ℕ) : List TwoRatioSite :=
  (List.range n).map Sum.inl ++ (List.range n).map Sum.inr

@[simp] theorem inl_mem_twoRatioFiniteSites (i n : ℕ) :
    Sum.inl i ∈ twoRatioFiniteSites n ↔ i < n := by
  simp [twoRatioFiniteSites]

@[simp] theorem inr_mem_twoRatioFiniteSites (i n : ℕ) :
    Sum.inr i ∈ twoRatioFiniteSites n ↔ i < n := by
  simp [twoRatioFiniteSites]

theorem twoRatioFiniteSites_nodup (n : ℕ) : (twoRatioFiniteSites n).Nodup := by
  apply List.Nodup.append
  · exact (show (List.range n).Nodup from List.nodup_range).map Sum.inl_injective
  · exact (show (List.range n).Nodup from List.nodup_range).map Sum.inr_injective
  · apply List.disjoint_left.mpr
    intro i hi hj
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hi
    simp at hj

theorem twoRatioFiniteSites_mono {n m : ℕ} (h : n ≤ m) :
    ∀ i ∈ twoRatioFiniteSites n, i ∈ twoRatioFiniteSites m := by
  intro i hi
  cases i <;> simp only [inl_mem_twoRatioFiniteSites, inr_mem_twoRatioFiniteSites] at hi ⊢
  all_goals exact hi.trans_le h

theorem twoRatioFiniteSites_exhausts (i : TwoRatioSite) :
    ∃ n, i ∈ twoRatioFiniteSites n := by
  cases i with
  | inl i => exact ⟨i + 1, by simp⟩
  | inr i => exact ⟨i + 1, by simp⟩

def twoRatioSiteShift (q : ℕ) : TwoRatioSite → TwoRatioSite :=
  Sum.map (q + ·) (q + ·)

theorem twoRatioSiteShift_injective (q : ℕ) : Function.Injective (twoRatioSiteShift q) := by
  intro i j h
  cases i <;> cases j <;> simp_all [twoRatioSiteShift]

@[simp] theorem twoRatioSiteShift_parameter (q : ℕ) (i : TwoRatioSite) :
    twoRatioSiteParameter (twoRatioSiteShift q i) = twoRatioSiteParameter i := by
  cases i <;> rfl

theorem twoRatioSiteShift_disjoint {n q : ℕ} (hn : n ≤ q) (k : ℕ) :
    List.Disjoint (twoRatioFiniteSites n)
      ((twoRatioFiniteSites k).map (twoRatioSiteShift q)) := by
  apply List.disjoint_left.mpr
  intro i hi hj
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hj
  cases j with
  | inl j =>
    have : q + j < n := (inl_mem_twoRatioFiniteSites _ _).mp hi
    omega
  | inr j =>
    have : q + j < n := (inr_mem_twoRatioFiniteSites _ _).mp hi
    omega

end KadisonKastler

end OAI
