import Mathlib
import OAI.Computability.MinUncut.Estimates.ArraySum

namespace OAI

variable {m n : ℕ}

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
namespace MinUncut.Inner
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def hermiteSupport (I : Point m n → ℕ) : Finset (Point m n) := Finset.univ.filter (fun u => 0 < I u)

def matchingAxes (x u : Point m n) : Finset (Fin m) :=
  Finset.univ.filter (fun i => face u i = face x i)

def forbiddenAxes (x : Point m n) (I : Point m n → ℕ) : Finset (Fin m) :=
  (hermiteSupport I).biUnion (matchingAxes x)

def goodAxes (x : Point m n) (I : Point m n → ℕ) : Finset (Fin m) :=
  Finset.univ \ forbiddenAxes x I

lemma eq_of_two_faces {x u : Point m n} {i j : Fin m} (hij : i ≠ j)
    (hi : face u i = face x i) (hj : face u j = face x j) : u=x := by
  funext t
  by_cases ht : t=i
  · subst t; exact congrFun hj ⟨i,hij⟩
  · exact congrFun hi ⟨t,ht⟩

lemma matchingAxes_card {x u : Point m n} (hux : u ≠ x) : (matchingAxes x u).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  by_contra hij
  exact hux (eq_of_two_faces hij (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2)

lemma hermiteSupport_card (I : Point m n → ℕ) : (hermiteSupport I).card ≤ ∑ u, I u := by
  calc
    _ = ∑ u ∈ hermiteSupport I, 1 := by simp
    _ ≤ ∑ u ∈ hermiteSupport I, I u := Finset.sum_le_sum (fun u hu => (Finset.mem_filter.mp hu).2)
    _ ≤ ∑ u, I u := Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)

lemma forbiddenAxes_card (x : Point m n) (I : Point m n → ℕ) (hx : I x=0) :
    (forbiddenAxes x I).card ≤ ∑ u, I u := by
  have h := Finset.card_biUnion_le_card_mul (hermiteSupport I) (matchingAxes x) 1 (by
    intro u hu
    apply matchingAxes_card
    intro he; subst u
    have := (Finset.mem_filter.mp hu).2
    simp [hx] at this)
  exact (h.trans (by simpa using hermiteSupport_card I))

lemma goodAxes_card (x : Point m n) (I : Point m n → ℕ) (hx : I x=0) :
    m-(∑ u, I u) ≤ (goodAxes x I).card := by
  have h := forbiddenAxes_card x I hx
  rw [goodAxes, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
  omega

lemma goodAxis_no_support (x : Point m n) (I : Point m n → ℕ) {i : Fin m}
    (hi : i ∈ goodAxes x I) (u : Point m n) (hu : 0 < I u) : face u i ≠ face x i := by
  intro hf
  exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_biUnion.mpr
    ⟨u,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hf⟩⟩)

lemma face_rowFill (x : Point m n) (r : Row m n) : face (rowFill x r) r.1 = r.2 := by
  funext t
  simp [face, rowFill, t.property]

lemma rowFill_axis (x : Point m n) (r : Row m n) : rowFill x r r.1 = x r.1 := by
  simp [rowFill]

def rowObstructions (x : Point m n) (r : Row m n) : Finset (Fin m) :=
  Finset.univ.filter (fun j => r.1 ≠ j ∧ r.2 ≠ face x r.1 ∧ doubleMatch r.1 j x (rowFill x r))

lemma obstruction_matching (x : Point m n) (r : Row m n) {j : Fin m}
    (hj : j ∈ rowObstructions x r) : j ∈ matchingAxes x (rowFill x r) := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  funext t
  by_cases ht : t.1=r.1
  · change rowFill x r t.1 = x t.1
    rw [ht, rowFill_axis]
  · exact (Finset.mem_filter.mp hj).2.2.2 t.1 ht t.property

lemma rowObstructions_card (x : Point m n) (r : Row m n) : (rowObstructions x r).card ≤ 1 := by
  by_cases hlocal : r.2 = face x r.1
  · simp [rowObstructions, hlocal]
  · refine (Finset.card_le_card (fun _ hj => obstruction_matching x r hj)).trans (matchingAxes_card ?_)
    intro he
    have hh := congrArg (fun u => face u r.1) he
    rw [face_rowFill] at hh
    exact hlocal hh

def forbiddenPairs (x : Point m n) (S : Finset (Row m n)) : Finset (Finset (Fin m)) :=
  S.biUnion (fun r => (rowObstructions x r).image (fun j => {r.1,j}))

lemma forbiddenPairs_card (x : Point m n) (S : Finset (Row m n)) :
    (forbiddenPairs x S).card ≤ S.card := by
  have h := Finset.card_biUnion_le_card_mul S
    (fun r => (rowObstructions x r).image (fun j => ({r.1,j} : Finset (Fin m)))) 1
    (fun r _ => Finset.card_image_le.trans (rowObstructions_card x r))
  simpa [forbiddenPairs] using h

lemma pair_not_forbidden_local (x : Point m n) (S : Finset (Row m n))
    {i j : Fin m} (hij : i ≠ j) (hp : ({i,j} : Finset (Fin m)) ∉ forbiddenPairs x S)
    (y : {t : Fin m // t ≠ i} → Fin n) (hy : (⟨i,y⟩ : Row m n) ∈ S)
    (hc : doubleMatch i j x (rowFill x ⟨i,y⟩)) : y = face x i := by
  by_contra hn
  apply hp
  apply Finset.mem_biUnion.mpr
  refine ⟨⟨i,y⟩,hy,Finset.mem_image.mpr ⟨j,?_,rfl⟩⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hij,hn,hc⟩

theorem admissible_pair (x : Point m n) (I : Point m n → ℕ) (S : Finset (Row m n))
    (hx : I x=0) (hsize : S.card < (m-(∑ u, I u)).choose 2) :
    ∃ i j : Fin m, i ≠ j ∧
      (∀ u, 0 < I u → face u i ≠ face x i ∧ face u j ≠ face x j) ∧
      (∀ y, (⟨i,y⟩ : Row m n) ∈ S → doubleMatch i j x (rowFill x ⟨i,y⟩) → y=face x i) ∧
      (∀ y, (⟨j,y⟩ : Row m n) ∈ S → doubleMatch j i x (rowFill x ⟨j,y⟩) → y=face x j) := by
  have hcard : (forbiddenPairs x S).card < ((goodAxes x I).powersetCard 2).card := by
    calc
      _ ≤ S.card := forbiddenPairs_card x S
      _ < (m-(∑ u, I u)).choose 2 := hsize
      _ ≤ _ := by rw [Finset.card_powersetCard]; exact Nat.choose_le_choose 2 (goodAxes_card x I hx)
  have hn : ¬ (goodAxes x I).powersetCard 2 ⊆ forbiddenPairs x S := by
    intro hh; exact (Nat.not_le_of_lt hcard) (Finset.card_le_card hh)
  obtain ⟨p,hp,hpn⟩ := Finset.not_subset.mp hn
  obtain ⟨i,j,hij,he⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hp).2
  subst p
  have hi := (Finset.mem_powersetCard.mp hp).1 (by simp : i ∈ ({i,j} : Finset (Fin m)))
  have hj := (Finset.mem_powersetCard.mp hp).1 (by simp : j ∈ ({i,j} : Finset (Fin m)))
  refine ⟨i,j,hij,?_,?_,?_⟩
  · intro u hu
    exact ⟨goodAxis_no_support x I hi u hu,goodAxis_no_support x I hj u hu⟩
  · exact fun y hy hc => pair_not_forbidden_local x S hij hpn y hy hc
  · exact fun y hy hc => pair_not_forbidden_local x S hij.symm (by simpa [Finset.pair_comm] using hpn) y hy hc
end MinUncut.Inner

end

end OAI
