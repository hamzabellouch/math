import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.WindowEnclosureGeometry

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section WindowEnclosureChains

structure WindowBracket (n : ℕ) (q : ℤ) (t : ℝ) where
  lower : CutRing
  upper : CutRing
  lower_label : q ≤ endpointLabel lower ∧ endpointLabel lower < q+n
  upper_label : q ≤ endpointLabel upper ∧ endpointLabel upper < q+n
  lower_bound : t-201/(n:ℝ) ≤ ordinary lower
  lower_lt : ordinary lower < t
  upper_lt : t < ordinary upper
  upper_bound : ordinary upper ≤ t+201/(n:ℝ)

noncomputable def windowBracket (n : ℕ) (hn : 1 ≤ n) (q : ℤ) (t : ℝ) :
    WindowBracket n q t := Classical.choice (by
  obtain ⟨u,v,hu,hv,huL,huR,hvL,hvR⟩ := coordinate_window_brackets n hn q t
  exact ⟨⟨u,v,hu,hv,huL,huR,hvL,hvR⟩⟩)

noncomputable def lowerEnclosure (n : ℕ) (hn : 1 ≤ n) (q : ℕ → ℤ) (a : ℝ) :
    ℕ → CutRing
  | 0 => (windowBracket n hn (q 0) a).lower
  | k+1 => (windowBracket n hn (q (k+1)) (ordinary (lowerEnclosure n hn q a k))).lower

noncomputable def upperEnclosure (n : ℕ) (hn : 1 ≤ n) (q : ℕ → ℤ) (b : ℝ) :
    ℕ → CutRing
  | 0 => (windowBracket n hn (q 0) b).upper
  | k+1 => (windowBracket n hn (q (k+1)) (ordinary (upperEnclosure n hn q b k))).upper

theorem lowerEnclosure_label (n : ℕ) (hn : 1 ≤ n) (q : ℕ → ℤ) (a : ℝ) (k : ℕ) :
    q k ≤ endpointLabel (lowerEnclosure n hn q a k) ∧
      endpointLabel (lowerEnclosure n hn q a k) < q k+n := by
  cases k with
  | zero => exact (windowBracket n hn (q 0) a).lower_label
  | succ k => exact (windowBracket n hn (q (k+1)) _).lower_label

theorem upperEnclosure_label (n : ℕ) (hn : 1 ≤ n) (q : ℕ → ℤ) (b : ℝ) (k : ℕ) :
    q k ≤ endpointLabel (upperEnclosure n hn q b k) ∧
      endpointLabel (upperEnclosure n hn q b k) < q k+n := by
  cases k with
  | zero => exact (windowBracket n hn (q 0) b).upper_label
  | succ k => exact (windowBracket n hn (q (k+1)) _).upper_label

theorem lowerEnclosure_step (n : ℕ) (hn : 1 ≤ n) (q : ℕ → ℤ) (a : ℝ) (k : ℕ) :
    ordinary (lowerEnclosure n hn q a k) - 201/(n:ℝ) ≤
        ordinary (lowerEnclosure n hn q a (k+1)) ∧
      ordinary (lowerEnclosure n hn q a (k+1)) < ordinary (lowerEnclosure n hn q a k) :=
  ⟨(windowBracket n hn (q (k+1)) _).lower_bound,
    (windowBracket n hn (q (k+1)) _).lower_lt⟩

theorem upperEnclosure_step (n : ℕ) (hn : 1 ≤ n) (q : ℕ → ℤ) (b : ℝ) (k : ℕ) :
    ordinary (upperEnclosure n hn q b k) < ordinary (upperEnclosure n hn q b (k+1)) ∧
      ordinary (upperEnclosure n hn q b (k+1)) ≤
        ordinary (upperEnclosure n hn q b k) + 201/(n:ℝ) :=
  ⟨(windowBracket n hn (q (k+1)) _).upper_lt,
    (windowBracket n hn (q (k+1)) _).upper_bound⟩

theorem lowerEnclosure_bounds (n : ℕ) (hn : 1 ≤ n) (q : ℕ → ℤ) (a : ℝ) (k : ℕ) :
    a - ((k:ℝ)+1)*201/(n:ℝ) ≤ ordinary (lowerEnclosure n hn q a k) ∧
      ordinary (lowerEnclosure n hn q a k) < a := by
  induction k with
  | zero =>
    simpa [lowerEnclosure] using And.intro (windowBracket n hn (q 0) a).lower_bound
      (windowBracket n hn (q 0) a).lower_lt
  | succ k ih =>
    have hs := lowerEnclosure_step n hn q a k
    constructor
    · simp only [Nat.cast_add,Nat.cast_one]
      have he : ((k:ℝ)+1+1)*201/(n:ℝ) = ((k:ℝ)+1)*201/(n:ℝ) + 201/(n:ℝ) := by ring
      rw [he]
      linarith [ih.1,hs.1]
    · exact lt_trans hs.2 ih.2

theorem upperEnclosure_bounds (n : ℕ) (hn : 1 ≤ n) (q : ℕ → ℤ) (b : ℝ) (k : ℕ) :
    b < ordinary (upperEnclosure n hn q b k) ∧
      ordinary (upperEnclosure n hn q b k) ≤ b + ((k:ℝ)+1)*201/(n:ℝ) := by
  induction k with
  | zero =>
    simpa [upperEnclosure] using And.intro (windowBracket n hn (q 0) b).upper_lt
      (windowBracket n hn (q 0) b).upper_bound
  | succ k ih =>
    have hs := upperEnclosure_step n hn q b k
    constructor
    · exact lt_trans ih.1 hs.1
    · simp only [Nat.cast_add,Nat.cast_one]
      have he : ((k:ℝ)+1+1)*201/(n:ℝ) = ((k:ℝ)+1)*201/(n:ℝ) + 201/(n:ℝ) := by ring
      rw [he]
      linarith [ih.2,hs.2]

theorem window_enclosure_chain (n : ℕ) (hn : 1 ≤ n) (q : ℕ → ℤ) (a b : ℝ)
    (_hab : a ≤ b) :
    ∃ u v : ℕ → CutRing,
      (∀ k, (q k ≤ endpointLabel (u k) ∧ endpointLabel (u k) < q k+n) ∧
        (q k ≤ endpointLabel (v k) ∧ endpointLabel (v k) < q k+n)) ∧
      (∀ k, Set.Icc a b ⊆ Set.Ioo (ordinary (u k)) (ordinary (v k))) ∧
      (∀ k, Set.Icc (ordinary (u k)) (ordinary (v k)) ⊆
        Set.Ioo (ordinary (u (k+1))) (ordinary (v (k+1)))) ∧
      ∀ k : ℕ, a-((k:ℝ)+1)*201/(n:ℝ) ≤ ordinary (u k) ∧
        ordinary (v k) ≤ b+((k:ℝ)+1)*201/(n:ℝ) := by
  refine ⟨lowerEnclosure n hn q a,upperEnclosure n hn q b,?_,?_,?_,?_⟩
  · intro k
    exact ⟨lowerEnclosure_label n hn q a k,upperEnclosure_label n hn q b k⟩
  · intro k x hx
    exact ⟨lt_of_lt_of_le (lowerEnclosure_bounds n hn q a k).2 hx.1,
      lt_of_le_of_lt hx.2 (upperEnclosure_bounds n hn q b k).1⟩
  · intro k x hx
    exact ⟨lt_of_lt_of_le (lowerEnclosure_step n hn q a k).2 hx.1,
      lt_of_le_of_lt hx.2 (upperEnclosure_step n hn q b k).1⟩
  · intro k
    exact ⟨(lowerEnclosure_bounds n hn q a k).1,(upperEnclosure_bounds n hn q b k).2⟩

end WindowEnclosureChains

end SimpleAmenable
end
end

end OAI
