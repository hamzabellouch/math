import Mathlib
import OAI.Computability.VertexCover.Reduction.CompatibleSingleton

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.LabelCover
namespace Decoding

variable (Φ : LabelCover) {d : ℕ}
variable (iU : Fin Φ.u → Φ.Query d) (iV : Fin Φ.v → Φ.Query d)
variable (pU : ∀ x, x ∈ (iU x).scopeU) (pV : ∀ y, y ∈ (iV y).scopeV)
variable (LU : ∀ x, List (iU x).LocalLabel) (LV : ∀ y, List (iV y).LocalLabel)

def leftAt (ρ : ℕ) (x : Fin Φ.u) : Fin Φ.qU :=
  if h : ρ < (LU x).length then ((LU x)[ρ]).1.1 ⟨x, pU x⟩ else ⟨0, Φ.qU_pos⟩

def rightAt (τ : ℕ) (y : Fin Φ.v) : Fin Φ.qV :=
  if h : τ < (LV y).length then ((LV y)[τ]).1.2 ⟨y, pV y⟩ else ⟨0, Φ.qV_pos⟩

def PairHit (c : Fin Φ.M) : Prop :=
  ∃ labU ∈ LU (Φ.left c), ∃ labV ∈ LV (Φ.right c),
    Φ.Compatible {⟨iU (Φ.left c), labU⟩, ⟨iV (Φ.right c), labV⟩}

noncomputable def pairHits : Finset (Fin Φ.M) := by
  classical
  exact Finset.univ.filter (PairHit Φ iU iV LU LV)

theorem pairHit_of_selection (c : Fin Φ.M) (I : Finset (Φ.Coordinate d))
    (hI : Φ.Compatible I)
    (labU : (iU (Φ.left c)).LocalLabel) (hlabU : labU ∈ LU (Φ.left c))
    (labV : (iV (Φ.right c)).LocalLabel) (hlabV : labV ∈ LV (Φ.right c))
    (hlabUI : ⟨iU (Φ.left c), labU⟩ ∈ I) (hlabVI : ⟨iV (Φ.right c), labV⟩ ∈ I) :
    PairHit Φ iU iV LU LV c := by
  classical
  refine ⟨labU, hlabU, labV, hlabV, Φ.compatible_mono hI ?_⟩
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  · exact hlabUI
  · exact hlabVI

theorem pairHit_decodes {ell : ℕ}
    (hLU : ∀ x, (LU x).length ≤ ell) (hLV : ∀ y, (LV y).length ≤ ell)
    (c : Fin Φ.M) (hc : PairHit Φ iU iV LU LV c) :
    ∃ ρ : Fin ell, ∃ τ : Fin ell,
      Φ.Satisfies (leftAt Φ iU pU LU ρ, rightAt Φ iV pV LV τ) c := by
  classical
  obtain ⟨labU, hlabU, labV, hlabV, hcompat⟩ := hc
  obtain ⟨ρ, hρ, eρ⟩ := List.mem_iff_getElem.mp hlabU
  obtain ⟨τ, hτ, eτ⟩ := List.mem_iff_getElem.mp hlabV
  refine ⟨⟨ρ, lt_of_lt_of_le hρ (hLU _)⟩, ⟨τ, lt_of_lt_of_le hτ (hLV _)⟩, ?_⟩
  have hs := hcompat.2.2.2 ⟨iU (Φ.left c), labU⟩ (by simp)
    ⟨iV (Φ.right c), labV⟩ (by simp) c (pU _) (pV _)
  simpa only [Satisfies, leftAt, rightAt, dite_eq_left hρ, dite_eq_left hτ, eρ, eτ] using hs

include pU pV

theorem pairHits_card_le {ell : ℕ} {σ : ℝ}
    (hval : Φ.value ≤ σ)
    (hLU : ∀ x, (LU x).length ≤ ell) (hLV : ∀ y, (LV y).length ≤ ell) :
    ((pairHits Φ iU iV LU LV).card : ℝ) ≤ (ell : ℝ)^2 * σ * Φ.M := by
  classical
  let good : (Fin ell × Fin ell) → Finset (Fin Φ.M) := fun a =>
    Finset.univ.filter (Φ.Satisfies (leftAt Φ iU pU LU a.1, rightAt Φ iV pV LV a.2))
  have hs : pairHits Φ iU iV LU LV ⊆ Finset.univ.biUnion good := by
    intro c hc
    have hh : PairHit Φ iU iV LU LV c := (Finset.mem_filter.mp hc).2
    obtain ⟨ρ, τ, ha⟩ := pairHit_decodes Φ iU iV pU pV LU LV hLU hLV c hh
    exact Finset.mem_biUnion.mpr ⟨(ρ, τ), Finset.mem_univ _, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ha⟩⟩
  have hcard := (Finset.card_le_card hs).trans Finset.card_biUnion_le
  calc
    ((pairHits Φ iU iV LU LV).card : ℝ) ≤
        ((∑ a : Fin ell × Fin ell, (good a).card : ℕ) : ℝ) := Nat.cast_le.mpr hcard
    _ = ∑ a : Fin ell × Fin ell, ((good a).card : ℝ) := by simp
    _ ≤ ∑ _a : Fin ell × Fin ell, σ * Φ.M := by
      apply Finset.sum_le_sum
      intro a _
      exact Φ.count_le_of_value_le hval _
    _ = (ell : ℝ)^2 * σ * Φ.M := by
      simp [Fintype.card_prod, pow_two]
      ring

theorem pairHits_probability_le {ell : ℕ} {σ : ℝ}
    (hval : Φ.value ≤ σ)
    (hLU : ∀ x, (LU x).length ≤ ell) (hLV : ∀ y, (LV y).length ≤ ell) :
    ((pairHits Φ iU iV LU LV).card : ℝ) / Φ.M ≤ (ell : ℝ)^2 * σ := by
  apply (div_le_iff₀ (Nat.cast_pos.mpr Φ.M_pos)).mpr
  exact pairHits_card_le Φ iU iV pU pV LU LV hval hLU hLV

end Decoding
end VertexCover.LabelCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
