import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.SubspacePointsEquiv

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence
open scoped LinearAlgebra.Projectivization Classical BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (ℙ K (Dual K V))]

noncomputable def upperSet (W : ℙ K (Dual K V) → Submodule K (Dual K V)) (l : ℕ) :=
  Finset.univ.filter fun y => finrank K (W y)≤l

noncomputable def levelSet (W : ℙ K (Dual K V) → Submodule K (Dual K V)) (l : ℕ) :=
  Finset.univ.filter fun y => finrank K (W y)=l

noncomputable def nextState (W : ℙ K (Dual K V) → Submodule K (Dual K V))
    (a : ℙ K V) (b : ℙ K (Dual K V)) (y : ℙ K (Dual K V)) :=
  if Incident a y then b.submodule ⊔ W y else W y

omit [FiniteDimensional K V] [Fintype (ℙ K (Dual K V))] in
lemma nextState_mono (W : ℙ K (Dual K V) → Submodule K (Dual K V))
    (a : ℙ K V) (b y : ℙ K (Dual K V)) : W y≤ nextState W a b y := by
  unfold nextState
  split_ifs
  · exact le_sup_right
  · exact le_rfl

lemma nextState_upper_subset (W : ℙ K (Dual K V) → Submodule K (Dual K V))
    (a : ℙ K V) (b : ℙ K (Dual K V)) (l : ℕ) :
    upperSet (nextState W a b) l⊆upperSet W l := by
  intro y hy
  apply Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
  exact (Submodule.finrank_mono (nextState_mono W a b y)).trans (Finset.mem_filter.mp hy).2

lemma leaves_upper (W : ℙ K (Dual K V) → Submodule K (Dual K V))
    (a : ℙ K V) (b y : ℙ K (Dual K V)) (l : ℕ)
    (hlevel : y∈levelSet W l) (hhit : Incident a y) (hnew : ¬b.submodule≤W y) :
    y∈upperSet W l ∧ y∉upperSet (nextState W a b) l := by
  have hl := (Finset.mem_filter.mp hlevel).2
  have hr : l<finrank K (nextState W a b y) := by
    rw [←hl,nextState,ite_eq_left hhit]
    apply Submodule.finrank_lt_finrank_of_lt
    exact lt_of_le_of_ne le_sup_right (fun h => hnew (h ▸ le_sup_left))
  constructor
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl.le⟩
  · exact fun hy => (not_lt_of_ge (Finset.mem_filter.mp hy).2) hr

theorem expensive_contraction (W : ℙ K (Dual K V) → Submodule K (Dual K V))
    (a : ℙ K V) (b : ℙ K (Dual K V)) (l : ℕ) (q : ℝ) (hq : 0<q)
    (hmax : (upperSet W l).card≤5*(levelSet W l).card)
    (hpoor : ((levelSet W l).card:ℝ)/(8*q)≤
      (((levelSet W l).filter fun y => Incident a y).card:ℝ))
    (hpop : (((levelSet W l).filter fun y => b.submodule≤W y).card:ℝ)≤
      ((levelSet W l).card:ℝ)/(16*q)) :
    ((upperSet (nextState W a b) l).card:ℝ)≤
      (1-1/(80*q))*((upperSet W l).card:ℝ) := by
  let U:=upperSet W l
  let U':=upperSet (nextState W a b) l
  let Z:=levelSet W l
  let H:=Z.filter fun y => Incident a y
  let B:=Z.filter fun y => b.submodule≤W y
  have hsub : H⊆(U\U')∪B := by
    intro y hy
    by_cases hb : y∈B
    · exact Finset.mem_union_right _ hb
    · have hyZ := (Finset.mem_filter.mp hy).1
      have hh := (Finset.mem_filter.mp hy).2
      have hn : ¬b.submodule≤W y := fun h => hb (Finset.mem_filter.mpr ⟨hyZ,h⟩)
      obtain ⟨hu,hu'⟩:=leaves_upper W a b y l hyZ hh hn
      exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hu,hu'⟩)
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have husub : U'⊆U := nextState_upper_subset W a b l
  have hdiff : (U\U').card=U.card-U'.card := Finset.card_sdiff_of_subset husub
  have hule := Finset.card_le_card husub
  have hcount : (H.card:ℝ)≤(U.card:ℝ)-U'.card+B.card := by
    have h := hc
    rw [hdiff] at h
    exact_mod_cast h
  have hzU : (U.card:ℝ)≤5*Z.card := by exact_mod_cast hmax
  change (Z.card:ℝ)/(8*q)≤(H.card:ℝ) at hpoor
  change (B.card:ℝ)≤(Z.card:ℝ)/(16*q) at hpop
  change (U'.card:ℝ)≤(1-1/(80*q))*(U.card:ℝ)
  have hid : (Z.card:ℝ)/(8*q)=2*((Z.card:ℝ)/(16*q)) := by field_simp; ring
  have huZ : (U.card:ℝ)/(80*q)≤(Z.card:ℝ)/(16*q) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  rw [hid] at hpoor
  have heq : (1-1/(80*q))*(U.card:ℝ)=U.card-(U.card:ℝ)/(80*q) := by ring
  rw [heq]
  linarith

end SharpRamseyFive.Marking

end OAI
