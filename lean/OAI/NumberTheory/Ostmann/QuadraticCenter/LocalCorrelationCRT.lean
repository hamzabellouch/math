import OAI.NumberTheory.Ostmann.QuadraticCenter.LocalCorrelationPhase
import OAI.NumberTheory.Ostmann.Supply.CRTPrimitiveEnergy

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem crt_phase_product {q : ℕ} [NeZero q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) (e : ZMod q ≃+* (∀ i, ZMod (p i))) (h : ZMod q)
    (x : ∀ i, ZMod (p i)) :
    ZMod.stdAddChar (-(e.symm x * h)) =
      ∏ i, ZMod.stdAddChar (-(e.symm (Pi.single i (x i)) * h)) := by
  have he : e.symm x = ∑ i, e.symm (Pi.single i (x i)) := by
    rw [← map_sum, Finset.univ_sum_single]
  rw [he, Finset.sum_mul, ← Finset.sum_neg_distrib]
  exact Supply.addChar_sum_eq_prod _ _ _

theorem dft_crt_product {q : ℕ} [NeZero q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)] (e : ZMod q ≃+* (∀ i, ZMod (p i)))
    (f : ∀ i, ZMod (p i) → ℂ) (h : ZMod q) :
    ZMod.dft (fun x => ∏ i, f i (e x i)) h =
      ∏ i, ∑ x : ZMod (p i), f i x *
        ZMod.stdAddChar (-(e.symm (Pi.single i x) * h)) := by
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul]
  calc
    _ = ∑ x : (∀ i, ZMod (p i)),
        ZMod.stdAddChar (-(e.symm x * h)) * ∏ i, f i (x i) := by
      apply Fintype.sum_equiv e.toEquiv
      intro x
      simp
    _ = ∑ x : (∀ i, ZMod (p i)),
        ∏ i, (f i (x i) * ZMod.stdAddChar (-(e.symm (Pi.single i (x i)) * h))) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [crt_phase_product, Finset.prod_mul_distrib, mul_comm]
    _ = _ := (Fintype.prod_sum (κ := fun i => ZMod (p i))
      (fun i (x : ZMod (p i)) => f i x *
        ZMod.stdAddChar (-(e.symm (Pi.single i x) * h)))).symm

theorem dft_crt_product_eq_zero_of_coordinate_zero {q : ℕ} [NeZero q]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℕ) [∀ i, NeZero (p i)]
    (e : ZMod q ≃+* (∀ i, ZMod (p i))) (f : ∀ i, ZMod (p i) → ℂ)
    (hmean : ∀ i, ∑ x, f i x = 0) (h : ZMod q) (i : ι) (hi : e h i = 0) :
    ZMod.dft (fun x => ∏ j, f j (e x j)) h = 0 := by
  rw [dft_crt_product]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  have hm (x : ZMod (p i)) : e.symm (Pi.single i x) * h = 0 := by
    apply e.injective
    simp only [map_mul, e.apply_symm_apply, map_zero]
    ext j
    by_cases hji : j = i
    · subst j
      simp [hi]
    · simp [Pi.single_eq_of_ne hji]
  simp_rw [hm, neg_zero, AddChar.map_zero_eq_one, mul_one]
  exact hmean i

theorem exists_crt_zero_coordinate_of_not_isUnit {q : ℕ} [NeZero q]
    {ι : Type*} [Fintype ι] (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (e : ZMod q ≃+* (∀ i, ZMod (p i))) (h : ZMod q) (hh : ¬ IsUnit h) :
    ∃ i, e h i = 0 := by
  classical
  let : ∀ i, Fact (p i).Prime := fun i => ⟨hp i⟩
  by_contra hn
  push Not at hn
  have hu : IsUnit (e h) := Pi.isUnit_iff.mpr (fun i => isUnit_iff_ne_zero.mpr (hn i))
  have hx := hu.map e.symm.toMonoidHom
  exact hh (by simpa using hx)

end Ostmann.QuadraticCenter

end

end OAI
