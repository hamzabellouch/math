import Mathlib
import OAI.Analysis.SymmetricDomains.SortedFiberSelection

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set
open scoped Classical

abbrev VerticalPiece (r : ℕ) := Fin r ⊕ (Option (Fin r) × Option (Fin r))

def verticalPieceSet {r : ℕ} (v : Fin r → ℝ) : VerticalPiece r → Set ℝ
  | .inl i => {v i}
  | .inr (none,none) => univ
  | .inr (some i,none) => Ioi (v i)
  | .inr (none,some j) => Iio (v j)
  | .inr (some i,some j) => Ioo (v i) (v j)

lemma verticalPiece_preconnected {r : ℕ} (v : Fin r → ℝ) (p : VerticalPiece r) :
    IsPreconnected (verticalPieceSet v p) := by
  rcases p with i | ⟨l,u⟩
  · exact isPreconnected_singleton
  · cases l <;> cases u
    · exact isPreconnected_univ
    · exact isPreconnected_Iio
    · exact isPreconnected_Ioi
    · exact isPreconnected_Ioo

lemma verticalPiece_lower {r : ℕ} (v : Fin r → ℝ) (i : Fin r) (u : Option (Fin r))
    {y : ℝ} (hy : y ∈ verticalPieceSet v (.inr (some i,u))) : v i < y := by
  cases u with
  | none => exact hy
  | some j => exact hy.1

lemma verticalPiece_upper {r : ℕ} (v : Fin r → ℝ) (j : Fin r) (l : Option (Fin r))
    {y : ℝ} (hy : y ∈ verticalPieceSet v (.inr (l,some j))) : y < v j := by
  cases l with
  | none => exact hy
  | some i => exact hy.2

lemma verticalPiece_polynomialSignSet {r : ℕ} (p : VerticalPiece r) :
    PolynomialSignSet (fun z : (Fin r → ℝ) × ℝ => fun o => Option.elim o z.2 z.1)
      {z | z.2 ∈ verticalPieceSet z.1 p} := by
  rcases p with i | ⟨l,u⟩
  · convert PolynomialSignSet.zero (c := fun z : (Fin r → ℝ) × ℝ => fun o =>
      Option.elim o z.2 z.1) (MvPolynomial.X none - MvPolynomial.X (some i)) using 1
    ext z
    simp [verticalPieceSet,sub_eq_zero]
  · cases l with
    | none =>
      cases u with
      | none => simpa only [verticalPieceSet,mem_univ,ofPred_true] using
          (PolynomialSignSet.univ (c := fun z : (Fin r → ℝ) × ℝ => fun o => Option.elim o z.2 z.1))
      | some j =>
        convert PolynomialSignSet.positive (c := fun z : (Fin r → ℝ) × ℝ => fun o =>
          Option.elim o z.2 z.1) (MvPolynomial.X (some j) - MvPolynomial.X none) using 1
        ext z
        simp [verticalPieceSet,sub_pos]
    | some i =>
      have hl := PolynomialSignSet.positive (c := fun z : (Fin r → ℝ) × ℝ => fun o =>
          Option.elim o z.2 z.1) (MvPolynomial.X none - MvPolynomial.X (some i))
      cases u with
      | none =>
        convert hl using 1
        ext z
        simp [verticalPieceSet,sub_pos]
      | some j =>
        have hu := PolynomialSignSet.positive (c := fun z : (Fin r → ℝ) × ℝ => fun o =>
          Option.elim o z.2 z.1) (MvPolynomial.X (some j) - MvPolynomial.X none)
        convert hl.inter hu using 1
        ext z
        simp [verticalPieceSet,sub_pos]

lemma verticalPieces_cover {r : ℕ} (v : Fin r → ℝ) (S : Set ℝ)
    (H : ∀ I, IsPreconnected I → (∀ z ∈ I, ∀ i, z ≠ v i) →
      ∀ y ∈ I, ∀ z ∈ I, (y ∈ S ↔ z ∈ S)) :
    ∀ y ∈ S, ∃ p : VerticalPiece r, y ∈ verticalPieceSet v p ∧ verticalPieceSet v p ⊆ S := by
  intro y hyS
  by_cases he : ∃ i, y = v i
  · obtain ⟨i,rfl⟩ := he
    exact ⟨.inl i,mem_singleton _,by simpa only [verticalPieceSet,singleton_subset_iff] using hyS⟩
  have hleft : ∃ l : Option (Fin r),
      (∀ i, l = some i → v i < y) ∧
      (∀ j, v j < y → ∃ i, l = some i ∧ v j ≤ v i) := by
    let L := Finset.univ.filter (fun i : Fin r => v i < y)
    by_cases hL : L.Nonempty
    · obtain ⟨i,hi,him⟩ := L.exists_max_image v hL
      refine ⟨some i,?_,?_⟩
      · intro j hj
        cases Option.some.inj hj
        exact (Finset.mem_filter.mp hi).2
      · intro j hj
        exact ⟨i,rfl,him j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩)⟩
    · refine ⟨none,by simp,?_⟩
      intro j hj
      exact (hL ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩⟩).elim
  have hright : ∃ u : Option (Fin r),
      (∀ i, u = some i → y < v i) ∧
      (∀ j, y < v j → ∃ i, u = some i ∧ v i ≤ v j) := by
    let U := Finset.univ.filter (fun i : Fin r => y < v i)
    by_cases hU : U.Nonempty
    · obtain ⟨i,hi,him⟩ := U.exists_min_image v hU
      refine ⟨some i,?_,?_⟩
      · intro j hj
        cases Option.some.inj hj
        exact (Finset.mem_filter.mp hi).2
      · intro j hj
        exact ⟨i,rfl,him j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩)⟩
    · refine ⟨none,by simp,?_⟩
      intro j hj
      exact (hU ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩⟩).elim
  obtain ⟨l,hl,hlmax⟩ := hleft
  obtain ⟨u,hu,humin⟩ := hright
  have hy : y ∈ verticalPieceSet v (.inr (l,u)) := by
    cases l <;> cases u <;> simp only [verticalPieceSet,mem_univ,mem_Ioi,mem_Iio,mem_Ioo]
    · exact hu _ rfl
    · exact hl _ rfl
    · exact ⟨hl _ rfl,hu _ rfl⟩
  have hfree : ∀ z ∈ verticalPieceSet v (.inr (l,u)), ∀ i, z ≠ v i := by
    intro z hz i hzi
    rcases lt_or_gt_of_ne (show v i ≠ y from fun h => he ⟨i,h.symm⟩) with hi | hi
    · obtain ⟨j,hlj,hij⟩ := hlmax i hi
      subst l
      have hjz := verticalPiece_lower v j u hz
      exact (not_lt_of_ge hij) (hzi ▸ hjz)
    · obtain ⟨j,huj,hji⟩ := humin i hi
      subst u
      have hzj := verticalPiece_upper v j l hz
      exact (not_lt_of_ge hji) (hzi ▸ hzj)
  refine ⟨.inr (l,u),hy,fun z hz => ?_⟩
  exact (H _ (verticalPiece_preconnected v _) hfree y hy z hz).mp hyS

namespace SemialgebraicOn
lemma predicate {ι κ : Type*} [Finite κ] {B : Set (ι → ℝ)} {f : (ι → ℝ) → (κ → ℝ)}
    (hf : SemialgebraicOn B f) {P : Set ((ι → ℝ) × (κ → ℝ))}
    (hP : PolynomialSignSet (fun z : (ι → ℝ) × (κ → ℝ) => Sum.elim z.1 z.2) P) :
    PolynomialSignSet id {x | x ∈ B ∧ (x,f x) ∈ P} := by
  have hh := SignElimination.polynomialSignSet_projection_finite (c := id) (hf.inter hP)
  convert hh using 1
  ext x
  simp only [mem_ofPred_eq,mem_inter_iff]
  constructor
  · rintro ⟨hx,hp⟩
    exact ⟨f x,⟨hx,rfl⟩,hp⟩
  · rintro ⟨y,⟨hx,rfl⟩,hp⟩
    exact ⟨hx,hp⟩
end SemialgebraicOn

lemma verticalPiece_base_polynomialSignSet {n r : ℕ}
    {S : Set ((Fin n → ℝ) × ℝ)}
    (hS : PolynomialSignSet (fun z : (Fin n → ℝ) × ℝ => fun o => Option.elim o z.2 z.1) S)
    (p : VerticalPiece r) :
    PolynomialSignSet (fun z : (Fin n → ℝ) × (Fin r → ℝ) => Sum.elim z.1 z.2)
      {z | (verticalPieceSet z.2 p).Nonempty ∧ ∀ y ∈ verticalPieceSet z.2 p, (z.1,y) ∈ S} := by
  let c := fun z : (Fin n → ℝ) × (Fin r → ℝ) => Sum.elim z.1 z.2
  let d := fun z : ((Fin n → ℝ) × (Fin r → ℝ)) × ℝ => fun o => Option.elim o z.2 (c z.1)
  have hp := (verticalPiece_polynomialSignSet p).coordinate_preimage
    (fun z : ((Fin n → ℝ) × (Fin r → ℝ)) × ℝ => (z.1.2,z.2))
    (Option.map Sum.inr) (d := d) (by intro z o; cases o <;> rfl)
  have hs := hS.coordinate_preimage
    (fun z : ((Fin n → ℝ) × (Fin r → ℝ)) × ℝ => (z.1.1,z.2))
    (Option.map Sum.inl) (d := d) (by intro z o; cases o <;> rfl)
  exact (SignElimination.polynomialSignSet_projection_one hp).inter
    (SignElimination.polynomialSignSet_forall_one (hp.implies hs))

end Release061

end

end OAI
