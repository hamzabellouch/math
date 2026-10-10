import OAI.NumberTheory.DirichletL.Moments.Local

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentHeterogeneousCRT
open CenteredMomentCorrelation

theorem fullCorrelation_heterogeneous_pi {ι : Type*} [Fintype ι]
    {X Y R : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    [∀ i, CommRing (R i)]
    (left : ∀ i, X i → R i) (right : ∀ i, Y i → R i)
    (f : ∀ i, X i → ℂ) (g : ∀ i, Y i → ℂ) (k : ∀ i, R i) :
    fullCorrelation (fun (x : ∀ i, X i) i => left i (x i)) (fun (y : ∀ i, Y i) i => right i (y i))
        (fun x => ∏ i, f i (x i)) (fun y => ∏ i, g i (y i)) k =
      ∏ i, fullCorrelation (left i) (right i) (f i) (g i) (k i) := by
  have hterm (x : ∀ i, X i) (y : ∀ i, Y i) :
      (if (fun i => left i (x i)) - (fun i => right i (y i)) = k
       then (∏ i, f i (x i)) * star (∏ i, g i (y i)) else 0) =
      ∏ i, if left i (x i) - right i (y i) = k i then f i (x i) * star (g i (y i)) else 0 := by
    by_cases h : ∀ i, left i (x i) - right i (y i) = k i
    · have he : (fun i => left i (x i)) - (fun i => right i (y i)) = k := funext h
      simp only [he, ite_true, h, star_prod, Finset.prod_mul_distrib]
    · obtain ⟨i, hi⟩ := not_forall.mp h
      have he : (fun i => left i (x i)) - (fun i => right i (y i)) ≠ k :=
        fun h => hi (congrFun h i)
      rw [ite_eq_right he]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp only [hi, ite_false]
  simp only [fullCorrelation]
  simp_rw [hterm]
  calc
    _ = ∑ x : ∀ i, X i, ∏ i, ∑ y : Y i,
        if left i (x i) - right i y = k i then f i (x i) * star (g i y) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      exact (Fintype.prod_sum (fun i (y : Y i) =>
        if left i (x i) - right i y = k i then f i (x i) * star (g i y) else (0 : ℂ))).symm
    _ = _ := (Fintype.prod_sum (fun i (x : X i) => ∑ y : Y i,
      if left i x - right i y = k i then f i x * star (g i y) else (0 : ℂ))).symm

theorem fullCorrelation_three_equiv {ι X Y R : Type*} [Fintype ι]
    [Fintype X] [Fintype Y] [CommRing R]
    {Xi Yi Ri : ι → Type*} [∀ i, Fintype (Xi i)] [∀ i, Fintype (Yi i)]
    [∀ i, CommRing (Ri i)]
    (eX : X ≃ ∀ i, Xi i) (eY : Y ≃ ∀ i, Yi i) (eR : R ≃+* ∀ i, Ri i)
    (left : X → R) (right : Y → R)
    (li : ∀ i, Xi i → Ri i) (ri : ∀ i, Yi i → Ri i)
    (hl : ∀ x i, eR (left x) i = li i (eX x i))
    (hr : ∀ y i, eR (right y) i = ri i (eY y i))
    (f : ∀ i, Xi i → ℂ) (g : ∀ i, Yi i → ℂ) (k : R) :
    fullCorrelation left right (fun x => ∏ i, f i (eX x i))
      (fun y => ∏ i, g i (eY y i)) k =
      ∏ i, fullCorrelation (li i) (ri i) (f i) (g i) (eR k i) := by
  rw [← fullCorrelation_heterogeneous_pi li ri f g (eR k)]
  unfold fullCorrelation
  apply Fintype.sum_equiv eX
  intro x
  apply Fintype.sum_equiv eY
  intro y
  have he : left x - right y = k ↔
      (fun i => li i (eX x i)) - (fun i => ri i (eY y i)) = eR k := by
    rw [← eR.injective.eq_iff, map_sub]
    have hleft : eR (left x) = fun i => li i (eX x i) := funext (hl x)
    have hright : eR (right y) = fun i => ri i (eY y i) := funext (hr y)
    rw [hleft, hright]
  simp only [he]

end SevenEighths.CenteredMomentHeterogeneousCRT

end

end OAI
