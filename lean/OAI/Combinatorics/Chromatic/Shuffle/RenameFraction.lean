import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.Diagonal

namespace OAI

section
namespace ElementaryPositivity.ShufflePolynomiality
open MvPolynomial
variable {α : Type*} [DecidableEq α]
section FractionRename
variable {α : Type*} [DecidableEq α]

noncomputable def renameFraction (σ : Equiv.Perm α) :
    FractionRing (MvPolynomial α ℚ) →+* FractionRing (MvPolynomial α ℚ) :=
  IsFractionRing.lift (g := (algebraMap (MvPolynomial α ℚ)
    (FractionRing (MvPolynomial α ℚ))).comp (rename σ).toRingHom)
      ((IsFractionRing.injective (MvPolynomial α ℚ)
        (FractionRing (MvPolynomial α ℚ))).comp (rename_injective σ σ.injective))

omit [DecidableEq α] in
@[simp] lemma renameFraction_algebraMap (σ : Equiv.Perm α) (f : MvPolynomial α ℚ) :
    renameFraction σ (algebraMap (MvPolynomial α ℚ) (FractionRing (MvPolynomial α ℚ)) f) =
      algebraMap (MvPolynomial α ℚ) (FractionRing (MvPolynomial α ℚ)) (rename σ f) :=
  IsFractionRing.lift_algebraMap _ _

end FractionRename

section RationalAverage
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (n : I → ℕ) (E : I → Prop) [DecidablePred E]
local notation "P" => MvPolynomial (Σ i, Fin (n i)) ℚ
local notation "K" => FractionRing P

omit [DecidableEq I] in
lemma naturalVandermonde_ne_zero : naturalVandermonde n E ≠ 0 := by
  rw [naturalVandermonde_product, Finset.prod_ne_zero_iff]
  rintro ⟨i,a,b⟩ ha
  simp only [naturalPairs, Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter,
    Finset.mem_product, true_and] at ha
  apply diagonal_ne_zero
  simpa [finPackPair] using ha.2.ne

theorem rational_pack_sum_polynomial (N C : P)
    (hC : C ∣ naturalVandermonde n E) :
    ∃ q : P, (∑ g : ∀i, Equiv.Perm (Fin (n i)),
        renameFraction (packAction (fun i => Fin (n i)) g)
          (algebraMap P K N / algebraMap P K C)) = algebraMap P K q := by
  let D := naturalVandermonde n E
  let ρ := packAction (fun i => Fin (n i))
  let χ := packSign (fun i => Fin (n i)) E
  have hD : D ≠ 0 := naturalVandermonde_ne_zero n E
  obtain ⟨r,hr⟩ := hC
  have hC0 : C ≠ 0 := by intro h; rw [h,zero_mul] at hr; exact hD hr
  have hr0 : r ≠ 0 := by intro h; rw [h,mul_zero] at hr; exact hD hr
  have hrK : algebraMap P K r ≠ 0 := by
    exact fun h => hr0 ((IsFractionRing.injective P K) (by simpa using h))
  have hDK : algebraMap P K D ≠ 0 := by
    exact fun h => hD ((IsFractionRing.injective P K) (by simpa using h))
  obtain ⟨q,hq⟩ := naturalVandermonde_dvd_alternate n E (N*r)
  refine ⟨q, ?_⟩
  have hseed : algebraMap P K N / algebraMap P K C =
      algebraMap P K (N*r) / algebraMap P K D := by
    dsimp [D]
    rw [hr, map_mul, map_mul, mul_div_mul_right _ _ hrK]
  rw [hseed]
  calc
    (∑ g, renameFraction (ρ g) (algebraMap P K (N*r) / algebraMap P K D)) =
        (∑ g, algebraMap P K ((χ g : ℤ) • rename (ρ g) (N*r))) /
          algebraMap P K D := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro g _
      rw [map_div₀, renameFraction_algebraMap, renameFraction_algebraMap]
      change algebraMap P K (rename (ρ g) (N*r)) /
        algebraMap P K (rename (ρ g) (naturalVandermonde n E)) = _
      rw [rename_naturalVandermonde]
      change algebraMap P K (rename (ρ g) (N*r)) /
        algebraMap P K ((χ g : ℤ) • D) = _
      rcases Int.units_eq_one_or (χ g) with h|h <;> simp [h, div_neg_eq_neg_div, neg_div]
    _ = algebraMap P K q := by
      rw [← map_sum]
      change algebraMap P K (alternate ρ χ (N*r)) / algebraMap P K D = _
      rw [hq, map_mul]
      exact mul_div_cancel_left₀ _ hDK

noncomputable def crossDenominator (d e : I → ℕ) :
    MvPolynomial (Σ i, Fin (d i + e i)) ℚ :=
  ∏ a ∈ (naturalPairs (fun i => d i + e i) (fun _ => True)).filter
      (fun a => a.2.1.val < d a.1 ∧ d a.1 ≤ a.2.2.val),
    diagonal (finPackPair (fun i => d i + e i) a).1
      (finPackPair (fun i => d i + e i) a).2

omit [DecidableEq I] in
lemma crossDenominator_dvd (d e : I → ℕ) :
    crossDenominator d e ∣ naturalVandermonde (fun i => d i + e i) (fun _ => True) := by
  rw [naturalVandermonde_product]
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)

theorem shuffle_denominator_sum_polynomial (d e : I → ℕ)
    (N : MvPolynomial (Σ i, Fin (d i + e i)) ℚ) :
    ∃ q : MvPolynomial (Σ i, Fin (d i + e i)) ℚ,
      (∑ g : ∀i, Equiv.Perm (Fin (d i + e i)),
        renameFraction (packAction (fun i => Fin (d i + e i)) g)
          (algebraMap _ (FractionRing (MvPolynomial (Σ i, Fin (d i + e i)) ℚ)) N /
            algebraMap _ _ (crossDenominator d e))) = algebraMap _ _ q :=
  rational_pack_sum_polynomial (fun i => d i + e i) (fun _ => True) N
    (crossDenominator d e) (crossDenominator_dvd d e)

end RationalAverage

section InvariantPoles
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (n : I → ℕ)
local notation "P" => MvPolynomial (Σ i, Fin (n i)) ℚ
local notation "K" => FractionRing P

lemma packed_pairs_product_dvd
    (s : ∀ i, Finset (Fin (n i) × Fin (n i))) (f : P)
    (hne : ∀ i ab, ab ∈ s i → ab.1 ≠ ab.2)
    (hrev : ∀ i ab, ab ∈ s i → (ab.2, ab.1) ∉ s i)
    (hf : ∀ i ab, ab ∈ s i → diagonal ⟨i,ab.1⟩ ⟨i,ab.2⟩ ∣ f) :
    (∏ i, ∏ ab ∈ s i, diagonal ⟨i,ab.1⟩ ⟨i,ab.2⟩) ∣ f := by
  suffices h : (∏ a ∈ Finset.univ.sigma s,
      diagonal (finPackPair n a).1 (finPackPair n a).2) ∣ f by
    simpa only [Finset.prod_sigma, finPackPair] using h
  apply Finset.prod_dvd_of_isRelPrime
  · rintro ⟨i,a,b⟩ hi ⟨j,c,d⟩ hj hdiff
    change (⟨i,(a,b)⟩ : Σ i, Fin (n i) × Fin (n i)) ∈ Finset.univ.sigma s at hi
    change (⟨j,(c,d)⟩ : Σ i, Fin (n i) × Fin (n i)) ∈ Finset.univ.sigma s at hj
    simp only [Finset.mem_sigma, Finset.mem_univ, true_and] at hi hj
    apply independent_diagonals
      (by simpa [finPackPair] using hne i (a,b) hi) (by simpa [finPackPair] using hne j (c,d) hj)
    · exact fun h => hdiff (finPackPair_injective n h)
    · intro hr
      have hij : i = j := congrArg (fun p => p.1.1) hr
      subst j
      simp only [finPackPair, Prod.mk.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at hr
      obtain ⟨rfl,rfl⟩ := hr
      exact hrev i (a,b) hi hj
  · rintro ⟨i,a,b⟩ hi
    exact hf i (a,b) (Finset.mem_sigma.mp hi).2

omit [DecidableEq I] in
lemma diagonal_dvd_naturalVandermonde (i : I) (a b : Fin (n i)) (hab : a ≠ b) :
    diagonal ⟨i,a⟩ ⟨i,b⟩ ∣ naturalVandermonde n (fun _ => True) := by
  have hlt (x y : Fin (n i)) (hxy : x < y) :
      diagonal ⟨i,x⟩ ⟨i,y⟩ ∣ naturalVandermonde n (fun _ => True) := by
    rw [naturalVandermonde_product]
    exact Finset.dvd_prod_of_mem
      (fun a : Σ i,Fin (n i) × Fin (n i) => diagonal (finPackPair n a).1 (finPackPair n a).2)
      (a := ⟨i,(x,y)⟩) (by simp only [naturalPairs, Finset.mem_sigma, Finset.mem_univ,
        Finset.mem_filter, Finset.mem_product, true_and]; exact hxy)
  rcases lt_or_gt_of_ne hab with h|h
  · exact hlt a b h
  · have hd := hlt b a h
    have he : diagonal (⟨i,a⟩ : Σi,Fin (n i)) ⟨i,b⟩ = -diagonal ⟨i,b⟩ ⟨i,a⟩ := by
      simp only [diagonal]; ring
    rw [he]
    exact neg_dvd.mpr hd

theorem invariant_fraction_regular (F : K)
    (hsym : ∀ g : ∀i, Equiv.Perm (Fin (n i)),
      renameFraction (packAction (fun i => Fin (n i)) g) F = F)
    (hreg : ∃ N : P, algebraMap P K (naturalVandermonde n (fun _ => True)) * F =
      algebraMap P K N) :
    ∃ q : P, F = algebraMap P K q := by
  obtain ⟨N,hN⟩ := hreg
  let V := fun i => Fin (n i)
  let D := naturalVandermonde n (fun _ => True)
  have hDK : algebraMap P K D ≠ 0 := by
    intro h
    apply naturalVandermonde_ne_zero n (fun _ => True)
    exact (IsFractionRing.injective P K) (by simpa using h)
  have hanti (i : I) (a b : Fin (n i)) (hab : a ≠ b) :
      rename (Equiv.swap (⟨i,a⟩ : Σi,Fin (n i)) ⟨i,b⟩) N = -N := by
    let t : ∀i, Equiv.Perm (V i) := Function.update 1 i (Equiv.swap a b)
    have ht := congrArg (renameFraction (packAction V t)) hN
    rw [map_mul, renameFraction_algebraMap, renameFraction_algebraMap, hsym] at ht
    have hsign : packSign V (fun _ => True) t = -1 :=
      packSign_transposition V (fun _ => True) i a b trivial hab
    rw [rename_naturalVandermonde, hsign] at ht
    simp only [Units.val_neg, Units.val_one, neg_smul, one_smul, map_neg, neg_mul] at ht
    rw [hN] at ht
    have hpoly : rename (packAction V t) N = -N :=
      (IsFractionRing.injective P K) (by simpa using ht.symm)
    simpa only [t, V, packAction_transposition] using hpoly
  have hd : D ∣ N := by
    change naturalVandermonde n (fun _ => True) ∣ N
    rw [naturalVandermonde_product]
    apply Finset.prod_dvd_of_isRelPrime
    · rintro ⟨i,a,b⟩ hi ⟨j,c,d⟩ hj hdiff
      change (⟨i,(a,b)⟩ : Σ i,Fin (n i) × Fin (n i)) ∈ naturalPairs n (fun _ => True) at hi
      change (⟨j,(c,d)⟩ : Σ i,Fin (n i) × Fin (n i)) ∈ naturalPairs n (fun _ => True) at hj
      simp only [naturalPairs, Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter,
        Finset.mem_product, true_and] at hi hj
      apply independent_diagonals (by simpa [finPackPair] using hi.ne) (by simpa [finPackPair] using hj.ne)
      · exact fun h => hdiff (finPackPair_injective n h)
      · intro hr
        have hij : i = j := congrArg (fun p => p.1.1) hr
        subst j
        simp only [finPackPair, Prod.mk.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at hr
        obtain ⟨rfl,rfl⟩ := hr
        exact lt_asymm hi hj
    · rintro ⟨i,a,b⟩ hi
      simp only [naturalPairs, Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter,
        Finset.mem_product, true_and] at hi
      exact diagonal_dvd_of_antisymmetric _ _ N (hanti i a b hi.ne)
  obtain ⟨q,hq⟩ := hd
  refine ⟨q, ?_⟩
  apply mul_left_cancel₀ hDK
  change algebraMap P K D * F = _
  rw [hN, hq, map_mul]

end InvariantPoles

end ElementaryPositivity.ShufflePolynomiality

end

end OAI
