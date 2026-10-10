import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceTestShells
import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceTypicalScale
import OAI.NumberTheory.Ostmann.Characters.HigherBiasValue

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters
open Preliminaries Construction HigherBiasSource Filter
open scoped BigOperators

lemma higherSource_top_cutoff (k : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    Real.exp (u+1) ≤ Real.log (higherSourceX k u:ℝ)/4 := by
  have hX := (higherSourceX_log_bounds k u hu).2.1
  have hp : (1:ℝ) ≤ 4^k := one_le_pow₀ (by norm_num)
  have he := Real.exp_one_lt_three
  have ht := Real.exp_pos u
  rw [Real.exp_add]
  nlinarith

lemma higherSource_interval_mass {k : ℕ} {u : ℝ} (hu : 0 ≤ u)
    (E : Finset ℕ) (hprime : ∀ p∈E,p.Prime)
    (hcut : ∀ p : ℕ,Real.log p ≤ Real.log (higherSourceX k u:ℝ)/4 →
      p ≤ collisionScale 10 (higherSourceX k u))
    (a b : ℝ) (hb : b ≤ u+1) :
    primeShellMass (boundedInterval (boundedPrimeSet (collisionScale 10 (higherSourceX k u)) E) a b)
      = harmonicIntervalMass E a b := by
  apply boundedInterval_mass_of_cutoff
  · exact hprime
  intro p hp _ hlog
  apply hcut
  have hlp : 0 < Real.log (p:ℝ) := Real.log_pos (by exact_mod_cast (hprime p hp).one_lt)
  have hle := Real.exp_le_exp.mpr (hlog.trans hb)
  rw [Real.exp_log hlp] at hle
  exact hle.trans (higherSource_top_cutoff k u hu)

theorem eventually_higherSource_actual_typical_shells (d : Decomposition)
    (δ c₀ : ℝ) (hδ : 0 < δ) (hc₀ : 0 < c₀) :
    ∃ cA : ℝ,0 < cA ∧ ∀ (k : ℕ) (α β : ℝ),0 < α →
      ∀ᶠ L : ℝ in atTop,∀ u : ℝ,α*L-1 ≤ u → u ≤ β*L →
      ∀ E : Finset ℕ,(∀ p∈E,p.Prime) →
      (∀ p∈E,α*L ≤ Real.log (Real.log p)) →
      (∀ p∈E,δ ≤ higherPrimeBias d p) →
      ∀ a b : Fin 3 → ℝ,(∀ i,b i ≤ u+1) →
      (∀ i,c₀ ≤ harmonicIntervalMass E (a i) (b i)) →
      ∀ U : ℝ,
      let X := higherSourceX k u
      let E' := boundedPrimeSet (collisionScale 10 X) E
      let base := fun i : Fin 3 => boundedInterval E' (a i) (b i)
      let G := testedShellFamily E' base c₀ U (Real.log X) k
      ∃ hm : ∀ i,0 < primeShellMass (G i),
      ∃ F : HigherBiasSourceFamily d (collisionScale 10 X) E' δ,
      ∃ H : Finset ℕ,H ⊆ upperWindow d.A X ∧
        cA*Real.sqrt X/(Real.log (X:ℝ))^3 ≤ H.card ∧
        ∀ n∈H,∀ i,δ/2 ≤
          ((primeShellPrior (G i) (hm i)).cmean (fun p => F.test p (n:ZMod p.val))).re := by
  obtain ⟨cA,hcA,htyp⟩ := eventually_higherSourceTypical_at_scale d δ c₀ hδ hc₀
  refine ⟨cA,hcA,?_⟩
  intro k α β hα
  have hL : ∀ᶠ L : ℝ in atTop,1 ≤ α*L := by
    exact (Filter.tendsto_id.const_mul_atTop hα).eventually_ge_atTop 1
  filter_upwards [htyp k (5*k+3) α β hα,
    eventually_higherSource_collisionScale10 k α hα,hL] with L ht hc hL
  intro u hul huu E hprime hband hbias a b hb hm U
  dsimp only
  have hu : 0 ≤ u := by linarith
  let X := higherSourceX k u
  let E' := boundedPrimeSet (collisionScale 10 X) E
  let base := fun i : Fin 3 => boundedInterval E' (a i) (b i)
  let G := testedShellFamily E' base c₀ U (Real.log X) k
  have hbasem : ∀ i,c₀ ≤ primeShellMass (base i) := by
    intro i
    rw [show primeShellMass (base i)=harmonicIntervalMass E (a i) (b i) from
      higherSource_interval_mass hu E hprime (hc u hul) (a i) (b i) (hb i)]
    exact hm i
  have hmass : ∀ i,c₀ ≤ primeShellMass (G i) := testedShellFamily_mass E' base c₀ U (Real.log X) k hbasem
  have hpos : ∀ i,0 < primeShellMass (G i) := fun i => hc₀.trans_le (hmass i)
  have hsub : ∀ i,G i ⊆ E' := testedShellFamily_subset E' base c₀ U (Real.log X) k
    (fun i => boundedInterval_subset E' (a i) (b i))
  obtain ⟨F⟩ := exists_higherBiasSourceFamily d (collisionScale 10 X) E' δ hδ (by
    intro p hp
    rw [← higherPrimeBias_prime]
    exact hbias p.val (mem_boundedPrimeSet.mp hp))
  obtain ⟨H,hH,hcard,hmean⟩ := ht u hul huu (Fin (5*k+3)) (by simp) E' F G hsub hpos hmass (by
    intro i p hp
    have hpp := mem_boundedPrimeSet.mp (hsub i hp)
    have he := Real.exp_le_exp.mpr (hband p.val hpp)
    have hlog : 0 < Real.log p.val := Real.log_pos (by exact_mod_cast (primeUpTo_prime p).one_lt)
    simpa only [Real.exp_log hlog] using he)
  exact ⟨hpos,F,H,hH,hcard,hmean⟩

end Ostmann.Characters

end

end OAI
