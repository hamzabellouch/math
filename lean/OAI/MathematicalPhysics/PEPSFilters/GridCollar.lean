import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.EnergyOptimizer

namespace OAI

/-! Separated rectangular contours and lattice perimeter bounds. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix
open Set Filter
open scoped Topology
open scoped BigOperators
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open scoped BigOperators Topology
open Filter Set
open scoped BigOperators Matrix.Norms.L2Operator
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
open scoped BigOperators InnerProductSpace
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder Topology

open scoped BigOperators Matrix.Norms.L2Operator
namespace PolynomialPEPS.PinnedEntropy.NestedFilter.Energy

def enlargedRectangle (L x y w h d : ℕ) : Finset (Vertex L) :=
  Finset.univ.filter (fun v => x ≤ v.1.val+d ∧ v.1.val ≤ x+w+d ∧
    y ≤ v.2.val+d ∧ v.2.val ≤ y+h+d)

lemma mem_enlargedRectangle {L x y w h d : ℕ} {v : Vertex L} :
    v ∈ enlargedRectangle L x y w h d ↔
      x ≤ v.1.val+d ∧ v.1.val ≤ x+w+d ∧ y ≤ v.2.val+d ∧ v.2.val ≤ y+h+d := by
  simp [enlargedRectangle]

lemma enlargedRectangle_monotone (L x y w h : ℕ) : Monotone (enlargedRectangle L x y w h) := by
  intro d e hde v hv
  rw [mem_enlargedRectangle] at hv ⊢
  omega

lemma adjacent_mem_enlargedRectangle {L x y w h d : ℕ} {v z : Vertex L}
    (hadj : ForwardAdjacent v z) :
    (v ∈ enlargedRectangle L x y w h d → z ∈ enlargedRectangle L x y w h (d+1)) ∧
    (z ∈ enlargedRectangle L x y w h d → v ∈ enlargedRectangle L x y w h (d+1)) := by
  rcases hadj with ⟨hx,hy⟩ | ⟨hx,hy⟩
  · have hy' := congrArg Fin.val hy
    simp only [mem_enlargedRectangle]
    omega
  · have hx' := congrArg Fin.val hx
    simp only [mem_enlargedRectangle]
    omega

lemma crossing_enlargedRectangle_unique {L x y w h : ℕ} (e : Edge L) {d k : ℕ}
    (hd : Crosses (enlargedRectangle L x y w h d) e)
    (hk : Crosses (enlargedRectangle L x y w h k) e) : d = k := by
  have aux {d k : ℕ} (hd : Crosses (enlargedRectangle L x y w h d) e) (hdk : d < k) :
      ¬ Crosses (enlargedRectangle L x y w h k) e := by
    have ht := enlargedRectangle_monotone L x y w h (Nat.succ_le_of_lt hdk)
    have hboth : e.val.1 ∈ enlargedRectangle L x y w h k ∧ e.val.2 ∈ enlargedRectangle L x y w h k := by
      rcases hd with ⟨hp,hq⟩ | ⟨hq,hp⟩
      · exact ⟨enlargedRectangle_monotone L x y w h hdk.le hp,
          ht ((adjacent_mem_enlargedRectangle e.property).1 hp)⟩
      · exact ⟨ht ((adjacent_mem_enlargedRectangle e.property).2 hq),
          enlargedRectangle_monotone L x y w h hdk.le hq⟩
    rintro (⟨_,hn⟩ | ⟨_,hn⟩)
    · exact hn hboth.2
    · exact hn hboth.1
  rcases lt_trichotomy d k with hd' | hd' | hd'
  · exact False.elim (aux hd hd' hk)
  · exact hd'
  · exact False.elim (aux hk hd' hd)

theorem rectangle_contours_separated (L x y w h m : ℕ) :
    let X : Fin m → Finset (Vertex L) := fun j => enlargedRectangle L x y w h j.val
    Monotone X ∧ ∀ e : Edge L, ∀ j k, Crosses (X j) e → Crosses (X k) e → j = k := by
  refine ⟨fun j k hjk => enlargedRectangle_monotone L x y w h hjk, ?_⟩
  intro e j k hj hk
  exact Fin.ext (crossing_enlargedRectangle_unique e hj hk)

theorem exists_rectangle_maximizer_energy {L q m : ℕ} [NeZero q]
    (x y w h : ℕ) (a : Fin m → ℝ) (ha : ∀ j, 0 < a j) (ha1 : ∀ j, a j ≤ 1)
    (hv : Vertex L → Operator L q) (he : Edge L → Operator L q)
    (J : ℝ) (hH : IsGridHamiltonian J hv he)
    (Ω : State L q) (E Δ : ℝ) (hg : UniqueGround (Hamiltonian hv he) Ω E)
    (hgap : FullSystemGap (Hamiltonian hv he) Ω E Δ) :
    let X : Fin m → Finset (Vertex L) := fun j => enlargedRectangle L x y w h j.val
    ∃ F : FilterFamily q m X, IsMaximizer Ω a F ∧ 0 < ‖output F Ω‖ ∧
      (|expectation (normalizedOutput F Ω) (Hamiltonian hv he) - E| ≤
        (q:ℝ)^2 * J * ∑ j, (crossingCount (X j):ℝ) * (a j)^2) ∧
      Δ * (1 - ‖inner ℂ Ω (normalizedOutput F Ω)‖^2) ≤
        (q:ℝ)^2 * J * ∑ j, (crossingCount (X j):ℝ) * (a j)^2 := by
  exact exists_maximizer_energy _ (rectangle_contours_separated L x y w h m).1
    (rectangle_contours_separated L x y w h m).2 a ha ha1 hv he J hH Ω E Δ hg hgap

end PolynomialPEPS.PinnedEntropy.NestedFilter.Energy

open scoped BigOperators Matrix.Norms.L2Operator
namespace PolynomialPEPS.PinnedEntropy.NestedFilter.Energy

private def horizontalBand (L t y h d : ℕ) : Finset (Edge L) :=
  Finset.univ.filter (fun e => e.val.1.1.val = t ∧ e.val.1.2 = e.val.2.2 ∧
    y ≤ e.val.1.2.val+d ∧ e.val.1.2.val ≤ y+h+d)

private def verticalBand (L t x w d : ℕ) : Finset (Edge L) :=
  Finset.univ.filter (fun e => e.val.1.2.val = t ∧ e.val.1.1 = e.val.2.1 ∧
    x ≤ e.val.1.1.val+d ∧ e.val.1.1.val ≤ x+w+d)

lemma horizontalBand_card_le (L t y h d : ℕ) : (horizontalBand L t y h d).card ≤ h+2*d+1 := by
  classical
  rw [← Finset.card_range (h+2*d+1)]
  apply Finset.card_le_card_of_injOn (fun e : Edge L => e.val.1.2.val+d-y)
  · intro e he
    change e ∈ horizontalBand L t y h d at he
    change e.val.1.2.val+d-y ∈ Finset.range (h+2*d+1)
    simp only [horizontalBand, Finset.mem_filter, Finset.mem_univ, true_and] at he
    simp only [Finset.mem_range]
    omega
  · intro e he f hf heq
    change e ∈ horizontalBand L t y h d at he
    change f ∈ horizontalBand L t y h d at hf
    change e.val.1.2.val+d-y = f.val.1.2.val+d-y at heq
    simp only [horizontalBand, Finset.mem_filter, Finset.mem_univ, true_and] at he hf
    have ep := e.property
    have fp := f.property
    have ehor : e.val.1.1.val+1 = e.val.2.1.val := by
      rcases ep with ha | ha
      · exact ha.1
      · have hh := congrArg Fin.val he.2.1; omega
    have fhor : f.val.1.1.val+1 = f.val.2.1.val := by
      rcases fp with ha | ha
      · exact ha.1
      · have hh := congrArg Fin.val hf.2.1; omega
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext
      · apply Fin.ext; omega
      · apply Fin.ext; omega
    · apply Prod.ext
      · apply Fin.ext; omega
      · rw [← he.2.1, ← hf.2.1]
        apply Fin.ext; omega

lemma verticalBand_card_le (L t x w d : ℕ) : (verticalBand L t x w d).card ≤ w+2*d+1 := by
  classical
  rw [← Finset.card_range (w+2*d+1)]
  apply Finset.card_le_card_of_injOn (fun e : Edge L => e.val.1.1.val+d-x)
  · intro e he
    change e ∈ verticalBand L t x w d at he
    change e.val.1.1.val+d-x ∈ Finset.range (w+2*d+1)
    simp only [verticalBand, Finset.mem_filter, Finset.mem_univ, true_and] at he
    simp only [Finset.mem_range]
    omega
  · intro e he f hf heq
    change e ∈ verticalBand L t x w d at he
    change f ∈ verticalBand L t x w d at hf
    change e.val.1.1.val+d-x = f.val.1.1.val+d-x at heq
    simp only [verticalBand, Finset.mem_filter, Finset.mem_univ, true_and] at he hf
    have ever : e.val.1.2.val+1 = e.val.2.2.val := by
      rcases e.property with ha | ha
      · have hh := congrArg Fin.val he.2.1; omega
      · exact ha.2
    have fver : f.val.1.2.val+1 = f.val.2.2.val := by
      rcases f.property with ha | ha
      · have hh := congrArg Fin.val hf.2.1; omega
      · exact ha.2
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext
      · apply Fin.ext; omega
      · apply Fin.ext; omega
    · apply Prod.ext
      · rw [← he.2.1, ← hf.2.1]
        apply Fin.ext; omega
      · apply Fin.ext; omega

theorem crossingCount_enlargedRectangle (L x y w h d : ℕ) :
    crossingCount (enlargedRectangle L x y w h d) ≤ 2*(w+1)+2*(h+1)+8*d := by
  classical
  let H₀ := horizontalBand L (x+w+d) y h d
  let H₁ := horizontalBand L (x-(d+1)) y h d
  let V₀ := verticalBand L (y+h+d) x w d
  let V₁ := verticalBand L (y-(d+1)) x w d
  have hsub : Finset.univ.filter (Crosses (enlargedRectangle L x y w h d)) ⊆
      (H₀ ∪ H₁) ∪ (V₀ ∪ V₁) := by
    intro e he
    have hc := (Finset.mem_filter.mp he).2
    simp only [Crosses, mem_enlargedRectangle] at hc
    simp only [Finset.mem_union, H₀,H₁,V₀,V₁,horizontalBand,verticalBand,
      Finset.mem_filter, Finset.mem_univ, true_and]
    rcases e.property with ⟨hx,hy⟩ | ⟨hx,hy⟩
    · have hy' := congrArg Fin.val hy
      left
      rcases hc with hc | hc
      · left; refine ⟨?_,hy,?_,?_⟩ <;> omega
      · right; refine ⟨?_,hy,?_,?_⟩ <;> omega
    · have hx' := congrArg Fin.val hx
      right
      rcases hc with hc | hc
      · left; refine ⟨?_,hx,?_,?_⟩ <;> omega
      · right; refine ⟨?_,hx,?_,?_⟩ <;> omega
  have hb := Finset.card_le_card hsub
  have hU := Finset.card_union_le (H₀ ∪ H₁) (V₀ ∪ V₁)
  have hHU := Finset.card_union_le H₀ H₁
  have hVU := Finset.card_union_le V₀ V₁
  have hH₀ := horizontalBand_card_le L (x+w+d) y h d
  have hH₁ := horizontalBand_card_le L (x-(d+1)) y h d
  have hV₀ := verticalBand_card_le L (y+h+d) x w d
  have hV₁ := verticalBand_card_le L (y-(d+1)) x w d
  change _ ≤ _
  dsimp only [H₀,H₁,V₀,V₁] at hb hU hHU hVU
  unfold crossingCount
  omega

theorem crossingCount_enlargedRectangle_scale (L x y w h d r : ℕ)
    (hw : w+1 ≤ r) (hh : h+1 ≤ r) :
    crossingCount (enlargedRectangle L x y w h d) ≤ 8*(r+d) := by
  have ht := crossingCount_enlargedRectangle L x y w h d
  omega

end PolynomialPEPS.PinnedEntropy.NestedFilter.Energy

end

end OAI
