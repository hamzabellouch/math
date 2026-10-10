import OAI.Probability.FirstPassage.BKDyadicPaths
import Mathlib.Combinatorics.Colex

namespace OAI

namespace PlanarFPP
open Finset

noncomputable def dyadicPositions (t : ℕ) (x : Finset (Edge × Fin t)) (e : Edge) : Finset ℕ :=
  ((univ : Finset (Fin t)).filter (fun h => (e,h) ∈ x)).image (fun h => t-(h.val+1))

noncomputable def dyadicRank (t : ℕ) (x : Finset (Edge × Fin t)) (e : Edge) : ℕ :=
  ∑ a ∈ dyadicPositions t x e, 2^a

lemma dyadicPositions_subset (t : ℕ) (x : Finset (Edge × Fin t)) (e : Edge) :
    dyadicPositions t x e ⊆ range t := by
  intro a ha
  obtain ⟨h,_,rfl⟩ := mem_image.mp ha
  rw [mem_range]
  have := h.isLt
  omega

lemma mem_dyadicPositions (t : ℕ) (x : Finset (Edge × Fin t)) (e : Edge) (h : Fin t) :
    t-(h.val+1) ∈ dyadicPositions t x e ↔ (e,h) ∈ x := by
  constructor
  · intro hm
    obtain ⟨a,ha,he⟩ := mem_image.mp hm
    have heq : a=h := by apply Fin.ext; have := a.isLt; have := h.isLt; omega
    subst a
    exact (mem_filter.mp ha).2
  · intro hm
    exact mem_image.mpr ⟨h,mem_filter.mpr ⟨mem_univ _,hm⟩,rfl⟩

lemma sum_two_powers_range (t : ℕ) : (∑ a ∈ range t, 2^a)+1=2^t := by
  induction t with
  | zero => simp
  | succ t ih => rw [sum_range_succ,pow_succ]; omega

lemma dyadicRank_lt (t : ℕ) (x : Finset (Edge × Fin t)) (e : Edge) :
    dyadicRank t x e < 2^t := by
  have h := sum_le_sum_of_subset_of_nonneg (f := fun a : ℕ => 2^a) (dyadicPositions_subset t x e)
    (fun _ _ _ => Nat.zero_le _)
  have hg := sum_two_powers_range t
  unfold dyadicRank
  omega

lemma dyadicRank_eq_iff (t : ℕ) (x y : Finset (Edge × Fin t)) (e : Edge) :
    dyadicRank t x e = dyadicRank t y e ↔ ∀ h : Fin t, (e,h) ∈ x ↔ (e,h) ∈ y := by
  constructor
  · intro he
    have hp : dyadicPositions t x e = dyadicPositions t y e := by
      have hh := congrArg (fun n : ℕ => n.bitIndices.toFinset) he
      simpa [dyadicRank] using hh
    intro h
    rw [← mem_dyadicPositions t x e h,← mem_dyadicPositions t y e h,hp]
  · intro he
    have hp : dyadicPositions t x e = dyadicPositions t y e := by
      unfold dyadicPositions
      congr 1
      ext h
      simp [he h]
    simp [dyadicRank,hp]

lemma dyadicRanks_injective (S : Finset Edge) (t : ℕ) {x y : Finset (Edge × Fin t)}
    (hx : x ⊆ S ×ˢ univ) (hy : y ⊆ S ×ˢ univ)
    (h : ∀ e ∈ S, dyadicRank t x e = dyadicRank t y e) : x=y := by
  ext ⟨e,a⟩
  by_cases he : e ∈ S
  · exact (dyadicRank_eq_iff t x y e).mp (h e he) a
  · have hn : (e,a) ∉ x := fun hm => he (mem_product.mp (hx hm)).1
    have hn' : (e,a) ∉ y := fun hm => he (mem_product.mp (hy hm)).1
    simp [hn,hn']

lemma dyadicRank_sum (t : ℕ) (x : Finset (Edge × Fin t)) (e : Edge) :
    dyadicRank t x e = ∑ h : Fin t, if (e,h) ∈ x then 2^(t-(h.val+1)) else 0 := by
  unfold dyadicRank dyadicPositions
  rw [sum_image]
  · simp only [sum_filter]
  · intro a _ b _ hab
    change t-(a.val+1)=t-(b.val+1) at hab
    apply Fin.ext
    have := a.isLt
    have := b.isLt
    omega

lemma dyadicSurvival_eq_rank (t : ℕ) (x : Finset (Edge × Fin t)) (e : Edge) :
    dyadicSurvival t x e = (dyadicRank t x e : ℝ)/(2:ℝ)^t := by
  rw [dyadicRank_sum]
  simp only [Nat.cast_sum,Nat.cast_ite,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_zero]
  rw [Finset.sum_div]
  unfold dyadicSurvival
  apply sum_congr rfl
  intro h _
  by_cases hm : (e,h) ∈ x
  · simp only [hm,↓reduceIte]
    have hh : t=(t-(h.val+1))+(h.val+1) := by omega
    have hp : (2:ℝ)^t = 2^(t-(h.val+1))*2^(h.val+1) := by rw [← pow_add,← hh]
    rw [hp]
    field_simp
  · simp [hm]

end PlanarFPP

end OAI
