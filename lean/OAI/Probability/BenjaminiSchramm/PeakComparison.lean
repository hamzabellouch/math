import OAI.Probability.BenjaminiSchramm.ExponentialDecay

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.decEq Classical.propDecidable

theorem bk_avoiding_increasing [Countable E] (p : unitInterval)
    (A B D : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B) (hD : IsUpperSet D)
    (hfA : FiniteWitness A) (hfB : FiniteWitness B) (hfD : FiniteWitness D) :
    (law p).real (DisjointOccurrence A B \ D) ≤
      (law p).real A * (law p).real B * (1 - (law p).real D) := by
  let F := DisjointOccurrence A B
  have hF : IsUpperSet F := disjointOccurrence_upper A B
  have hfF : FiniteWitness F := finiteWitness_disjointOccurrence A B
  have hh := association_finiteWitness p F D hF hD hfF hfD
  have hd := measureReal_sdiff_add_inter (μ := law p) (s := F)
    (measurableSet_finiteWitness D hD hfD)
  have h1 : (law p).real D ≤ 1 := by
    simp
  have ha : (law p).real (F \ D) ≤ (law p).real F * (1 - (law p).real D) := by
    nlinarith
  exact ha.trans (mul_le_mul_of_nonneg_right (bk p A B hA hB hfA hfB) (by linarith))

def aboveConnection (G : BondGraph V E) (h : V → ℝ) (x : V) : Set (Set E) :=
  {ω | ∃ y, Conn G ω x y ∧ h x < h y}

theorem aboveConnection_upper (G : BondGraph V E) (h : V → ℝ) (x : V) :
    IsUpperSet (aboveConnection G h x) := by
  rintro ω η hωη ⟨y,hy,hh⟩
  exact ⟨y,conn_mono G hωη hy,hh⟩

theorem aboveConnection_finiteWitness (G : BondGraph V E) (h : V → ℝ) (x : V) :
    FiniteWitness (aboveConnection G h x) := by
  rintro ω ⟨y,hy,hh⟩
  obtain ⟨s,hs,hsy⟩ := finiteWitness_conn G x y ω hy
  exact ⟨s,hs,y,hsy,hh⟩

theorem bk_on_peak [Countable E] (G : BondGraph V E) (h : V → ℝ) (x : V)
    (p : unitInterval) (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hfA : FiniteWitness A) (hfB : FiniteWitness B) :
    (law p).real (DisjointOccurrence A B \ aboveConnection G h x) ≤
      (law p).real A * (law p).real B * (1 - (law p).real (aboveConnection G h x)) :=
  bk_avoiding_increasing p A B _ hA hB (aboveConnection_upper G h x) hfA hfB
    (aboveConnection_finiteWitness G h x)

end Percolation.BenjaminiSchramm

end OAI
