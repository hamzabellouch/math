import OAI.NumberTheory.Ostmann.Characters.ConcreteQuartetFourier

namespace OAI

/-! # Reflection and conjugation preserve the hypotheses for every local row -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

noncomputable local instance quartetTestSymmetriesFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

theorem orientedPairBase_zero {p : ℕ} (g : ZMod p → ℂ) (hg : g 0 = 0) (friendly : Bool) :
    orientedPairBase g friendly 0 = 0 := by
  cases friendly <;> simp [orientedPairBase, hg]

theorem orientedPairBase_energy {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (friendly : Bool) :
    (∑ x : ZMod p, ‖orientedPairBase g friendly x‖ ^ 2) = ∑ x : ZMod p, ‖g x‖ ^ 2 := by
  cases friendly
  · simp only [orientedPairBase, Bool.false_eq_true, ite_false, Complex.norm_conj]
    exact (Equiv.neg (ZMod p)).bijective.sum_comp (fun x => ‖g x‖ ^ 2)
  · rfl

theorem MixedFourierBound.orientedPairBase {p : ℕ} [Fact p.Prime]
    {g : ZMod p → ℂ} {ε : ℝ} (hg : MixedFourierBound g ε) (friendly : Bool) :
    MixedFourierBound (orientedPairBase g friendly) ε := by
  cases friendly
  · simpa only [Ostmann.orientedPairBase, Bool.false_eq_true, ite_false,
      Units.val_neg, Units.val_one, neg_one_mul] using hg.conj.unit_mul (-1)
  · exact hg

theorem sum_units_neg {p : ℕ} [Fact p.Prime] (f : ZMod p → ℝ) :
    (∑ y : (ZMod p)ˣ, f (-(y : ZMod p))) = ∑ y : (ZMod p)ˣ, f y := by
  simpa only [Equiv.neg_apply, Units.val_neg] using
    (Equiv.neg (ZMod p)ˣ).bijective.sum_comp (fun y => f y)

theorem conjugated_crossPairMajorant_mean_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (ε : ℝ) (hε : 0 ≤ ε) (hflat : MixedFourierBound g ε)
    (cL cR left right : Bool) (ρ : MulChar (ZMod p) ℂ) :
    (∑ y : (ZMod p)ˣ,
      crossPairMajorant (orientedPairBase (pairConjugate g cL) left)
        (orientedPairBase (pairConjugate g cR) right) left right ρ y) /
          (Fintype.card (ZMod p)ˣ : ℝ) ≤
      2 * (((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) *
        (friendlyQuartetError p ε + twoBadQuartetError p ε)) := by
  have he (c friendly : Bool) :
      (∑ x : ZMod p, ‖orientedPairBase (pairConjugate g c) friendly x‖ ^ 2) ≤ (p : ℝ) := by
    rw [orientedPairBase_energy]
    simpa only [norm_pairConjugate] using henergy
  apply crossPairMajorant_mean_le _ _ left right _
    (add_nonneg (friendlyQuartetError_nonneg p ε) (twoBadQuartetError_nonneg p ε))
  intro ν
  exact concrete_quartet_fourier_le _ _
    (orientedPairBase_zero _ (pairConjugate_zero g hg cL) left)
    (orientedPairBase_zero _ (pairConjugate_zero g hg cR) right)
    (he cL left) (he cR right) ε hε
    ((hflat.pairConjugate cL).orientedPairBase left)
    ((hflat.pairConjugate cR).orientedPairBase right) left right ν

theorem conjugated_crossPairMajorant_total_mean_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ)) (cL cR left right : Bool) :
    (∑ ρ : MulChar (ZMod p) ℂ, (∑ y : (ZMod p)ˣ,
      crossPairMajorant (orientedPairBase (pairConjugate g cL) left)
        (orientedPairBase (pairConjugate g cR) right) left right ρ y) /
          (Fintype.card (ZMod p)ˣ : ℝ)) ≤
      ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2 := by
  have he (c friendly : Bool) :
      (∑ x : ZMod p, ‖orientedPairBase (pairConjugate g c) friendly x‖ ^ 2) ≤ (p : ℝ) := by
    rw [orientedPairBase_energy]
    simpa only [norm_pairConjugate] using henergy
  exact crossPairMajorant_total_mean_le _ _
    (orientedPairBase_zero _ (pairConjugate_zero g hg cL) left)
    (orientedPairBase_zero _ (pairConjugate_zero g hg cR) right)
    (he cL left) (he cR right) left right

end Ostmann

end OAI
