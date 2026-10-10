import OAI.Probability.ContinuumTransition.PhysicalMoments

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem cellLowerBound_ge_negative {t : ℝ} {σ R : ℕ → ℝ} {V : Space → Space → ℝ}
    (hV : CellLowerBound t σ R V) (x y : Space) :
    -physicalCoupling t σ R (cellIndex x) (cellIndex y) ≤ V x y := by
  have hc : 0 ≤ if cellIndex x = cellIndex y then coreProfile t ‖x-y‖ else 0 := by
    split_ifs; exact coreProfile_nonneg _ _; rfl
  calc
    _ ≤ (if cellIndex x = cellIndex y then coreProfile t ‖x-y‖ else 0)-
        physicalCoupling t σ R (cellIndex x) (cellIndex y) := by linarith only [hc]
    _ ≤ _ := hV x y

theorem cellLowerBound_energy_insertion {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n)
    {V : Space → Space → ℝ} (hV : CellLowerBound t σ R V) (hVsym : ∀ x y, V x y = V y x)
    {ι κ : Type} [Fintype ι] [Fintype κ] (x : ι → Space) (s : Finset ι) (z : Lattice)
    (hx : ∀ i ∈ s, x i ∈ latticeCell z)
    (c : {i : ι // i ∉ s} → κ) (e : κ → Lattice) (he : Function.Injective e)
    (hc : ∀ i : {i : ι // i ∉ s}, cellIndex (x i) = e (c i)) :
    (t^2/8-physicalCoupling t σ R z z/2)*(s.card : ℝ)^2-t^2/2*s.card-
      s.card*(∑ k, physicalCoupling t σ R z (e k)*
        occupation (latticeCell (e k)) (fun i : {i : ι // i ∉ s} => x i)) ≤
      gibbsEnergy V x-gibbsEnergy V (fun i : {i : ι // i ∉ s} => x i) := by
  have hfi : Subtype.fintype (fun i : ι => i ∈ s) = Finset.Subtype.fintype s := Subsingleton.elim _ _
  have hsplit := gibbsEnergy_split V hVsym (fun i : ι => i ∈ s) x
  rw [hfi] at hsplit
  have hcore := core_gibbsEnergy_one_cell t (fun i : s => x i) z (fun i => hx i i.property)
  let W : Space → Space → ℝ := fun _ _ => physicalCoupling t σ R z z
  have hw := gibbsEnergy_le_card_sq W (fun i : s => x i)
    (physicalCoupling_nonneg ht hσ hR z z) (fun _ _ => le_refl _)
  have hlo := gibbsEnergy_mono (U := fun x y => coreProfile t ‖x-y‖-W x y) (V := V)
    (fun i : s => x i) (fun i j => by
      have hh := hV (x i) (x j)
      rw [show cellIndex (x i) = z from hx i i.property,
        show cellIndex (x j) = z from hx j j.property, ite_eq_left rfl] at hh
      exact hh)
  rw [gibbsEnergy_sub] at hlo
  have hin : (t^2/8-physicalCoupling t σ R z z/2)*(s.card : ℝ)^2-t^2/2*s.card ≤
      gibbsEnergy V (fun i : s => x i) := by
    simp only [Fintype.card_coe] at hcore hw
    linarith only [hcore, hw, hlo]
  have hcross : -(s.card : ℝ)*(∑ k, physicalCoupling t σ R z (e k)*
      occupation (latticeCell (e k)) (fun i : {i : ι // i ∉ s} => x i)) ≤
      ∑ i : s, ∑ j : {i : ι // i ∉ s}, V (x i) (x j) := by
    have hpoint (i : s) (j : {i : ι // i ∉ s}) :
        -physicalCoupling t σ R z (cellIndex (x j)) ≤ V (x i) (x j) := by
      have hh := cellLowerBound_ge_negative hV (x i) (x j)
      rw [show cellIndex (x i) = z from hx i i.property] at hh
      exact hh
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset s)) =>
      Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset {i : ι // i ∉ s})) => hpoint i j))
    simp only [Finset.sum_neg_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_coe, nsmul_eq_mul] at hh
    rw [sum_physicalCoupling_occupations t σ R z (fun i : {i : ι // i ∉ s} => x i) c e he hc] at hh
    simpa only [neg_mul, mul_neg] using hh
  linarith only [hin, hcross, hsplit]

theorem cellLowerBound_insertion_half_moments {t β : ℝ} (ht : 0 < t) (hβ : 0 ≤ β)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n) ≤ (t^2/8)/8)
    {V : Space → Space → ℝ} (hV : CellLowerBound t σ R V) (hVsym : ∀ x y, V x y = V y x)
    (h : ℝ) {D : Set Space} {ι κ : Type} [Fintype ι] [Fintype κ]
    (x : ι → Space) (s : Finset ι) (z : Lattice)
    (hx : x ∈ binaryRegion (D ∩ latticeCell z) (D \ latticeCell z) s)
    (e : κ → Lattice) (he : Function.Injective e)
    (c : {i : ι // i ∉ s} → κ) (hc : ∀ i : {i : ι // i ∉ s}, cellIndex (x i) = e (c i)) :
    momentFamily (gibbsFamily V β h) (latticeCell z) (β*(t^2/8)/4) ι x ≤
      Real.exp ((h+β*(t^2/2))*s.card)*
        (gibbsFamily V β h {i : ι // i ∉ s} (fun i => x i)+
        ∑ k, (physicalCoupling t σ R z (e k)/(t^2/8))*
          momentFamily (gibbsFamily V β h) (latticeCell (e k)) ((β*(t^2/8)/4)/2)
            {i : ι // i ∉ s} (fun i => x i)) := by
  have hA : 0 < t^2/8 := by positivity
  have hi := gibbs_moment_insertion V (h := h) hA hsmall
    (physicalCoupling_self_le ht.le hσ hR hs z) hβ (latticeCell z) s x
    (∑ k, physicalCoupling t σ R z (e k)*occupation (latticeCell (e k))
      (fun i : {i : ι // i ∉ s} => x i))
    (occupation_card_binary D (latticeCell z) s x hx)
    (cellLowerBound_energy_insertion ht.le hσ hR hV hVsym x s z
      (fun i hi => by
        have hh := hx i
        simp only [ite_eq_left hi] at hh
        exact hh.2) c e he hc)
  have hh := exp_exterior_field_le (fun k => physicalCoupling t σ R z (e k))
    (fun k => occupation (latticeCell (e k)) (fun i : {i : ι // i ∉ s} => x i))
    hA hβ (fun k => physicalCoupling_nonneg ht.le hσ hR z (e k))
    ((physicalCoupling_row ht.le hσ hR hs e he z).trans hsmall)
  apply hi.trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply (mul_le_mul_of_nonneg_left hh (gibbsFamily_nonneg _ β h _ _)).trans_eq
  rw [mul_add, mul_one, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  dsimp only [momentFamily]
  have hec : β*(t^2/8)/8 = β*(t^2/8)/4/2 := by ring
  rw [hec]
  ring

end ContinuumTemperature
end

end OAI
