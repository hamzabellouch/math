import Mathlib
import OAI.Combinatorics.SharpRamsey.Learning.PreparedDecoder
import OAI.Combinatorics.SharpRamsey.Learning.PreparedVariance

namespace OAI

section
namespace SharpLogRamsey.GreedyPreparation
open Finset
open scoped Classical
noncomputable section
variable {A B : Type*}

lemma own_empty_or_index (S : Finset A) (U : B→Finset A) (bs : List B) (x : A) :
    own S U bs x=∅ ∨ ∃ i : Fin bs.length,own S U bs x=indexedCell S U bs i := by
  rcases own_empty_or_cell S U bs x with he|he
  · exact Or.inl he
  · right
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp he
    have hil : i.val<bs.length := by simpa only [cells_length] using i.isLt
    refine ⟨⟨i.val,hil⟩,?_⟩
    rw [indexedCell_eq]
    exact hi.symm

end
end SharpLogRamsey.GreedyPreparation

namespace SharpLogRamsey.PreparedGeometry
open Finset PreparedRow PreparedTypical PreparedVariance RegularPencils GreedyPreparation
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V J : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedPreparedGeometry_1 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedPreparedGeometry_2 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _
local instance flat_JoinedPreparedGeometry_3 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _

def badHyperplanes (S : Finset (Projectivization K V))
    (U : J→Finset (Projectivization K V)) (bs : List J) (c : ℝ≥0) :
    Finset (Projectivization K (Module.Dual K V)) :=
  exceptional (mass S c) (fun i : Fin bs.length => mass (indexedCell S U bs i) c)
    (fun i => ((indexedCell S U bs i).card:ℝ)/(S.card:ℝ))

lemma not_bad (S : Finset (Projectivization K V))
    (U : J→Finset (Projectivization K V)) (bs : List J) (c : ℝ≥0)
    (H : Projectivization K (Module.Dual K V)) (hH : H∉badHyperplanes S U bs c)
    (x : Projectivization K V) :
    |mass S c H-1|≤1/10 ∧
    |mass (own S U bs x) c H-((own S U bs x).card:ℝ)/(S.card:ℝ)|≤1/50 := by
  have hh : ¬(1/10 < |mass S c H-1| ∨ ∃ i : Fin bs.length,
      1/50 < |mass (indexedCell S U bs i) c H-((indexedCell S U bs i).card:ℝ)/(S.card:ℝ)|) := by
    simpa only [badHyperplanes,exceptional,mem_filter,mem_univ,true_and] using hH
  obtain ⟨hl,hc⟩ := not_or.mp hh
  refine ⟨le_of_not_gt hl,?_⟩
  rcases own_empty_or_index S U bs x with he|⟨i,he⟩
  · simp [he,mass]
  · rw [he]
    exact le_of_not_gt (fun hi => hc ⟨i,hi⟩)

omit [Finite K] [FiniteDimensional K V] in
lemma cell_sum_le (S : Finset (Projectivization K V))
    (U : J→Finset (Projectivization K V)) (bs : List J) :
    (∑ i : Fin bs.length,(indexedCell S U bs i).card)≤S.card := by
  rw [indexedCell_sum]
  exact card_le_card (removed_subset S U bs)

lemma pencil_exception_count (S : Finset (Projectivization K V))
    (U : J→Finset (Projectivization K V)) (bs : List J) (c : ℝ≥0)
    (x : Projectivization K V) :
    (∑ H∈pencil x,weights S (indexedCell S U bs) c (some none) H)=
      ((pencil x∩badHyperplanes S U bs c).card:ℝ) := by
  simp only [weights,←sum_filter]
  change (∑ H∈(pencil x).filter (fun H => H∈badHyperplanes S U bs c),(1:ℝ))=_
  rw [filter_mem_eq_inter]
  simp

theorem regular_preparation {n : ℕ} (hdim : Module.finrank K V=n+3)
    (S : Finset (Projectivization K V)) (hS : S.Nonempty)
    (U : J→Finset (Projectivization K V)) (bs : List J) (c : ℝ≥0)
    (hc : (c:ℝ)=(Nat.card K:ℝ)/(S.card:ℝ)) (hcsmall : (c:ℝ)≤1/100)
    (hcell : ∀ i : Fin bs.length,((indexedCell S U bs i).card:ℝ)/(S.card:ℝ)≤1/25)
    (T : ℝ) (hT : 0≤T)
    (hmean : (∑ k∈range (n+2),(Nat.card K:ℝ)^k)/(∑ k∈range (n+3),(Nat.card K:ℝ)^k)*
      (10408*((Nat.card K:ℝ)^(n+3)/(S.card:ℝ)))≤T/2) :
    let E := badHyperplanes S U bs c
    ∃ D : Finset (Projectivization K V),
      (D.card:ℝ)*(T/2)^2≤10408*(Nat.card K:ℝ)^(2*n+4)/(S.card:ℝ) ∧
      (E.card:ℝ)≤10400*((Nat.card K:ℝ)^(n+3)/(S.card:ℝ)) ∧
      (∑ H∈E,mass S c H)≤20804*((Nat.card K:ℝ)^(n+3)/(S.card:ℝ)) ∧
      (∀ x,((own S U bs x).card:ℝ)/(S.card:ℝ)≤1/25) ∧
      ∀ x,x∉D →
        ((pencil x∩E).card:ℝ)<T ∧
        (∀ H∈pencil x\E,
          3/4≤outsideMass S (own S U bs x) x c H ∧
          outsideMass S (own S U bs x) x c H≤2 ∧
          |outsideMass S (own S U bs x) x c H-
            (1-((own S U bs x).card:ℝ)/(S.card:ℝ))|≤13/100) ∧
        (∑ H∈pencil x\E,(outsideMass S (own S U bs x) x c H-
          (1-((own S U bs x).card:ℝ)/(S.card:ℝ)))^2)≤
            3*(T+T+((pencil x\E).card:ℝ)*(c:ℝ)^2) := by
  dsimp only
  obtain ⟨D,hD,hr⟩ := exists_regular hdim S hS (indexedCell S U bs) (cell_sum_le S U bs) c hc T hT hmean
  have he := actual_exceptions hdim S hS (indexedCell S U bs) (cell_sum_le S U bs) c hc
  dsimp only at he
  have hf (x : Projectivization K V) : ((own S U bs x).card:ℝ)/(S.card:ℝ)≤1/25 := by
    rcases own_empty_or_index S U bs x with he|⟨i,he⟩
    · simp [he]
    · rw [he]; exact hcell i
  refine ⟨D,hD,he.2.2.1,he.2.2.2,hf,?_⟩
  intro x hx
  have hO : own S U bs x⊆S := (own_subset_removed S U bs x).trans (removed_subset S U bs)
  have hfull : (∑ H∈pencil x,min 1 ((mass S c H-1)^2))≤T := (hr x hx none).le
  have hown : (∑ H∈pencil x,min 1 ((mass (own S U bs x) c H-
      ((own S U bs x).card:ℝ)/(S.card:ℝ))^2))≤T := by
    rcases own_empty_or_index S U bs x with hh|⟨i,hh⟩
    · simpa [hh,mass] using hT
    · rw [hh]
      exact (hr x hx (some (some i))).le
  have hn (H : Projectivization K (Module.Dual K V)) (hH : H∈pencil x\badHyperplanes S U bs c) :=
    not_bad S U bs c H (mem_sdiff.mp hH).2 x
  refine ⟨?_,?_,?_⟩
  · rw [←pencil_exception_count]
    exact hr x hx (some none)
  · intro H hH
    exact typical_point S _ hO x c H _ hcsmall (by positivity) (hf x) (hn H hH).1 (hn H hH).2
  · exact typical_squares S _ hO x c _ sdiff_subset _ T T
      (fun H hH => (hn H hH).1) (fun H hH => (hn H hH).2) hfull hown

end
end SharpLogRamsey.PreparedGeometry

end

end OAI
