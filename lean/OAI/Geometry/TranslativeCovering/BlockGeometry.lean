import OAI.Geometry.TranslativeCovering.BlockTerminal

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1

namespace BlockGeometry
open Finset
variable {I : Type u_1}
noncomputable def radius (d : I → I → ℝ) (S : Finset I) : ℝ :=
  if h : S.Nonempty then S.inf' h (fun j => S.sup' h (fun i => d j i ^ 2)) else 0

lemma radius_nonneg (d : I → I → ℝ) (S : Finset I) : 0 ≤ radius d S := by
  classical
  unfold radius
  split_ifs with h
  · apply le_inf'
    intro j _
    obtain ⟨i,hi⟩ := h
    exact (sq_nonneg _).trans (le_sup' (fun i => d j i ^ 2) hi)
  · rfl

lemma radius_le (d : I → I → ℝ) {S : Finset I} {j : I} (hj : j ∈ S)
    {R : ℝ} (hR : ∀ i ∈ S, d j i ^ 2 ≤ R) : radius d S ≤ R := by
  classical
  have hS : S.Nonempty := ⟨j,hj⟩
  rw [radius, dite_eq_left hS]
  exact (inf'_le _ hj).trans (sup'_le _ _ hR)

lemma exists_center (d : I → I → ℝ) {S : Finset I} (hS : S.Nonempty) :
    ∃ j ∈ S, ∀ i ∈ S, d j i ^ 2 ≤ radius d S := by
  classical
  obtain ⟨j,hj,he⟩ := exists_mem_eq_inf' hS (fun j => S.sup' hS (fun i => d j i ^ 2))
  refine ⟨j,hj,fun i hi => ?_⟩
  rw [radius, dite_eq_left hS, he]
  exact le_sup' (fun i => d j i ^ 2) hi

lemma radius_singleton (d : I → I → ℝ) (hd : ∀ i, d i i = 0) (i : I) :
    radius d {i} = 0 := by
  exact le_antisymm (radius_le d (mem_singleton_self _) (by simp [hd]))
    (radius_nonneg d _)

lemma anchor_distance (d : I → I → ℝ) (hn : ∀ i j, 0 ≤ d i j)
    (hs : ∀ i j, d i j = d j i)
    (ht : ∀ i j k, d i k ≤ d i j + d j k)
    {S : Finset I} {a i : I} (ha : a ∈ S) (hi : i ∈ S) :
    d a i ≤ 2*Real.sqrt (radius d S) := by
  obtain ⟨j,_,hj⟩ := exists_center d ⟨a,ha⟩
  have hja : d j a ≤ Real.sqrt (radius d S) :=
    (Real.le_sqrt (hn j a) (radius_nonneg d S)).mpr (hj a ha)
  have hji : d j i ≤ Real.sqrt (radius d S) :=
    (Real.le_sqrt (hn j i) (radius_nonneg d S)).mpr (hj i hi)
  have := ht a j i
  rw [hs a j] at this
  linarith

noncomputable def loss (L : ℝ) (d : I → I → ℝ) (S : Finset I) : ℝ :=
  if S.card ≤ 1 then 0 else L*(1+radius d S+Real.log S.card)

lemma loss_nonneg {L : ℝ} (hL : 0 ≤ L) (d : I → I → ℝ) (S : Finset I) :
    0 ≤ loss L d S := by
  unfold loss
  split_ifs with h
  · rfl
  · apply mul_nonneg hL
    have hc : (1:ℝ) ≤ S.card := by exact_mod_cast (by omega : 1 ≤ S.card)
    have := Real.log_nonneg hc
    have := radius_nonneg d S
    linarith

lemma radius_le_loss {L : ℝ} (hL : 0 < L) (d : I → I → ℝ)
    (hd : ∀ i, d i i = 0) (S : Finset I) : radius d S ≤ loss L d S / L := by
  classical
  unfold loss
  split_ifs with h
  · by_cases he : S = ∅
    · simp [he, radius]
    · have hc : S.card = 1 := by have := card_pos.mpr (nonempty_iff_ne_empty.mpr he); omega
      obtain ⟨i,rfl⟩ := card_eq_one.mp hc
      simp [radius_singleton d hd]
  · rw [mul_div_cancel_left₀ _ hL.ne']
    have hc : (1:ℝ) ≤ S.card := by exact_mod_cast (by omega : 1 ≤ S.card)
    have := Real.log_nonneg hc
    linarith

lemma loss_singleton (L : ℝ) (d : I → I → ℝ) (i : I) : loss L d {i} = 0 := by
  simp [loss]

lemma exists_terminal [Fintype I] [DecidableEq I] {L ζ R : ℝ} (hR : 0 ≤ R) (hζ : 0 ≤ ζ)
    (d : I → I → ℝ) (hd : ∀ i, d i i = 0) :
    ∃ P : Finpartition (univ : Finset I),
      (∀ S ∈ P.parts, radius d S ≤ R ∧ loss L d S ≤ ζ*S.card) ∧
      ∀ H ⊆ P.parts, 2 ≤ H.card →
        ¬(radius d (H.biUnion id) ≤ R ∧ loss L d (H.biUnion id) ≤ ζ*(H.biUnion id).card) := by
  apply BlockTerminal.exists_terminal
  intro i
  simp only [radius_singleton d hd, loss_singleton, Finset.card_singleton, Nat.cast_one, mul_one]
  exact ⟨hR,hζ⟩

lemma nearby_union_radius [DecidableEq I] {L t u : ℝ} (hL : 0 < L) (ht : 0 ≤ t) (hu : 0 ≤ u)
    (d : I → I → ℝ) (hn : ∀ i j, 0 ≤ d i j) (hd : ∀ i, d i i = 0)
    (hs : ∀ i j, d i j = d j i) (htri : ∀ i j k, d i k ≤ d i j+d j k)
    (H : Finset (Finset I)) (hH : H.Nonempty) (a : Finset I → I) (z : I)
    (ha : ∀ S ∈ H, a S ∈ S)
    (hclose : ∀ S ∈ H, d z (a S)^2 ≤ t)
    (hloss : ∀ S ∈ H, loss L d S ≤ u) :
    radius d (H.biUnion id) ≤ 8*t+8*u/L := by
  obtain ⟨S0,hS0⟩ := hH
  have ha0 : a S0 ∈ H.biUnion id := mem_biUnion.mpr ⟨S0,hS0,ha S0 hS0⟩
  apply radius_le d ha0
  intro i hi
  obtain ⟨S,hS,hiS⟩ := mem_biUnion.mp hi
  have h0 : d (a S0) z ≤ Real.sqrt t := by
    rw [hs]
    exact (Real.le_sqrt (hn _ _) ht).mpr (hclose _ hS0)
  have h1 : d z (a S) ≤ Real.sqrt t :=
    (Real.le_sqrt (hn _ _) ht).mpr (hclose _ hS)
  have h2 : d (a S) i ≤ 2*Real.sqrt (u/L) := by
    apply (anchor_distance d hn hs htri (ha S hS) hiS).trans
    apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt _) (by norm_num)
    exact (radius_le_loss hL d hd S).trans ((div_le_div_iff_of_pos_right hL).mpr (hloss S hS))
  have h3 := htri (a S0) z i
  have h4 := htri z (a S) i
  have hb : d (a S0) i ≤ 2*Real.sqrt t+2*Real.sqrt (u/L) := by linarith
  have hz := hn (a S0) i
  have hsqt := Real.sq_sqrt ht
  have hsqu := Real.sq_sqrt (div_nonneg hu hL.le)
  have hab := sq_nonneg (Real.sqrt t-Real.sqrt (u/L))
  have he : d (a S0) i ^ 2 ≤ (2*Real.sqrt t+2*Real.sqrt (u/L))^2 :=
    pow_le_pow_left₀ hz hb 2
  calc
    _ ≤ (2*Real.sqrt t+2*Real.sqrt (u/L))^2 := he
    _ ≤ 8*t+8*(u/L) := by nlinarith [hab]
    _ = _ := by ring

end BlockGeometry

end OAI
