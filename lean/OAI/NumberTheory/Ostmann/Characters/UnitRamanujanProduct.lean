import OAI.NumberTheory.Ostmann.Characters.TupleCRTFourier
import OAI.NumberTheory.Ostmann.Characters.TensorRamanujanExpansion

namespace OAI

/-! # The reduced-frequency kernel factors over the actual CRT moduli -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def unitRamanujanKernel (q : ℕ) [NeZero q] (z : ZMod q) : ℂ :=
  ∑ u : (ZMod q)ˣ, ZMod.stdAddChar ((u : ZMod q) * z)

theorem unitRamanujanKernel_int_congr {q r : ℕ} [NeZero q] [NeZero r]
    (h : q = r) (z : ℤ) :
    unitRamanujanKernel q (z : ZMod q) = unitRamanujanKernel r (z : ZMod r) := by
  subst r
  rfl

theorem unitRamanujanKernel_scale (q : ℕ) [NeZero q] (c : (ZMod q)ˣ) (z : ZMod q) :
    (∑ u : (ZMod q)ˣ, ZMod.stdAddChar ((c : ZMod q) * (u : ZMod q) * z)) =
      unitRamanujanKernel q z := by
  exact (Equiv.mulLeft c).bijective.sum_comp (fun u : (ZMod q)ˣ =>
    ZMod.stdAddChar ((u : ZMod q) * z))

theorem unitRamanujanKernel_prime {p : ℕ} [Fact p.Prime] (z : ZMod p) :
    unitRamanujanKernel p z =
      ∑ h ∈ Finset.univ.erase (0 : ZMod p), ZMod.stdAddChar (h * z) := by
  apply Finset.sum_bij (fun (u : (ZMod p)ˣ) _ => (u : ZMod p))
  · intro u _
    exact Finset.mem_erase.mpr ⟨Units.ne_zero u, Finset.mem_univ _⟩
  · intro u _ v _ huv
    exact Units.val_injective huv
  · intro x hx
    exact ⟨Units.mk0 x (Finset.mem_erase.mp hx).1, Finset.mem_univ _, rfl⟩
  · intro _ _
    rfl

theorem unitRamanujanKernel_product {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j))) (n : ℤ) :
    unitRamanujanKernel (∏ i, p i) (n : ZMod (∏ i, p i)) =
      ∏ i, unitRamanujanKernel (p i) (n : ZMod (p i)) := by
  have he (u : (ZMod (∏ i, p i))ˣ) :
      ZMod.stdAddChar ((u : ZMod (∏ i, p i)) * (n : ZMod (∏ i, p i))) =
        ∏ i, ZMod.stdAddChar ((tupleCofactor p i : ZMod (p i))⁻¹ *
          (crtUnitEquiv p hc u i : ZMod (p i)) * (n : ZMod (p i))) := by
    rw [tuple_stdAddChar p hc]
    apply Finset.prod_congr rfl
    intro i _
    simp only [map_mul, map_intCast, Pi.mul_apply, Pi.intCast_apply]
    change ZMod.stdAddChar ((tupleCofactor p i : ZMod (p i))⁻¹ *
      ((crtUnitEquiv p hc u i : ZMod (p i)) * (n : ZMod (p i)))) = _
    congr 1
    ring
  unfold unitRamanujanKernel
  simp_rw [he]
  have hh := (crtUnitEquiv p hc).toEquiv.sum_comp (fun u : ∀ i, (ZMod (p i))ˣ =>
    ∏ i, ZMod.stdAddChar ((tupleCofactor p i : ZMod (p i))⁻¹ *
      (u i : ZMod (p i)) * (n : ZMod (p i))))
  calc
    _ = ∑ u : (∀ i, (ZMod (p i))ˣ), ∏ i,
        ZMod.stdAddChar ((tupleCofactor p i : ZMod (p i))⁻¹ *
          (u i : ZMod (p i)) * (n : ZMod (p i))) := hh
    _ = ∏ i, ∑ u : (ZMod (p i))ˣ,
        ZMod.stdAddChar ((tupleCofactor p i : ZMod (p i))⁻¹ *
          (u : ZMod (p i)) * (n : ZMod (p i))) := (Fintype.prod_sum (fun i (u : (ZMod (p i))ˣ) =>
            ZMod.stdAddChar ((tupleCofactor p i : ZMod (p i))⁻¹ *
              (u : ZMod (p i)) * (n : ZMod (p i))))).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      let c := ZMod.unitOfCoprime (tupleCofactor p i) (tupleCofactor_coprime p hc i)
      have hcval : ((c⁻¹ : (ZMod (p i))ˣ) : ZMod (p i)) =
          (tupleCofactor p i : ZMod (p i))⁻¹ := by
        rw [← ZMod.inv_coe_unit]
        simp only [c, ZMod.coe_unitOfCoprime]
      rw [← hcval]
      exact unitRamanujanKernel_scale (p i) c⁻¹ (n : ZMod (p i))

end Ostmann

end OAI
