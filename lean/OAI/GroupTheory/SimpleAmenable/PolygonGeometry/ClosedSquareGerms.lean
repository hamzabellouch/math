import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.FiniteArrangementGerms

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ClosedSquareGerms

theorem finite_arrangement_germ_square {ι : Type*} [Finite ι] (a : ℕ)
    (j : ι → Fin 4) (c : ι → ℝ) (z : ℝ × ℝ) (y : GenericSquare a) (σ : ι → Bool)
    (hz₁ : z.1 ∈ Set.Icc (0:ℝ) 1) (hz₂ : z.2 ∈ Set.Icc (0:ℝ) 1)
    (hactive : ∀ i, cutForm a (j i) z=c i →
      if σ i then cutForm a (j i) y.val < c i else c i < cutForm a (j i) y.val)
    (hinactive : ∀ i, cutForm a (j i) z≠c i →
      if σ i then cutForm a (j i) z < c i else c i < cutForm a (j i) z)
    (N : Set (ℝ × ℝ)) (hN : IsOpen N) (hz : z ∈ N) :
    ∃ p : GenericSquare a, p.val ∈ N ∧ p.val ∈ strictLineCell a j c σ := by
  classical
  let J : Sum ι (Fin 2 × Bool) → Fin 4 := Sum.elim j (fun d => Fin.castLE (by omega) d.1)
  let C : Sum ι (Fin 2 × Bool) → ℝ := Sum.elim c (fun d => if d.2 then 1 else 0)
  let S : Sum ι (Fin 2 × Bool) → Bool := Sum.elim σ Prod.snd
  have hyv := generic_coordinates_pos y
  have ha : ∀ i, cutForm a (J i) z=C i →
      if S i then cutForm a (J i) y.val < C i else C i < cutForm a (J i) y.val := by
    intro i hi
    cases i with
    | inl i => exact hactive i hi
    | inr d =>
      rcases d with ⟨d,b⟩
      fin_cases d <;> cases b
      · exact hyv.1
      · exact y.property.1.2
      · exact hyv.2
      · exact y.property.2.1.2
  have hn : ∀ i, cutForm a (J i) z≠C i →
      if S i then cutForm a (J i) z < C i else C i < cutForm a (J i) z := by
    intro i hi
    cases i with
    | inl i => exact hinactive i hi
    | inr d =>
      rcases d with ⟨d,b⟩
      fin_cases d <;> cases b <;>
        simp [J,C,S,cutForm] at hi ⊢
      · exact lt_of_le_of_ne hz₁.1 (Ne.symm hi)
      · exact lt_of_le_of_ne hz₁.2 hi
      · exact lt_of_le_of_ne hz₂.1 (Ne.symm hi)
      · exact lt_of_le_of_ne hz₂.2 hi
  obtain ⟨p,hp,hcell,hgeneric⟩ := finite_arrangement_germ a J C z y.val S ha hn N hN hz
  have hp₁ : p.1 ∈ Set.Ioo (0:ℝ) 1 := ⟨hcell (.inr (0,false)),hcell (.inr (0,true))⟩
  have hp₂ : p.2 ∈ Set.Ioo (0:ℝ) 1 := ⟨hcell (.inr (1,false)),hcell (.inr (1,true))⟩
  exact ⟨⟨p,⟨hp₁.1.le,hp₁.2⟩,⟨hp₂.1.le,hp₂.2⟩,hgeneric⟩,hp,fun i => hcell (.inl i)⟩

end ClosedSquareGerms

end SimpleAmenable
end
end

end OAI
