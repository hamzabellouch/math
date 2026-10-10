import OAI.NumberTheory.Jacobsthal.Estimates.SmallModelSourceScales
import OAI.NumberTheory.Jacobsthal.Primes.PrimeExceptionalMean

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseFrozen
open ErdosInverseSpectrum ErdosHyperbolaIdentities

noncomputable def frozenIntegers (N : ℕ) (w : ℝ) (p q : ℕ) (b v : ℤ)
    (a : ℕ → ℕ) : Finset ℤ :=
  (frozenCoordinates N w p q b v a).image (fun j : ℕ => (j : ℤ))

theorem frozenIntegers_card (N : ℕ) (w : ℝ) (p q : ℕ) (b v : ℤ) (a : ℕ → ℕ) :
    (frozenIntegers N w p q b v a).card = (frozenCoordinates N w p q b v a).card := by
  unfold frozenIntegers
  exact Finset.card_image_of_injective _ Int.ofNat_injective

theorem frozenIntegers_subset (N : ℕ) (w : ℝ) (p q : ℕ) (b v : ℤ) (a : ℕ → ℕ) :
    frozenIntegers N w p q b v a ⊆ Finset.Ico (0 : ℤ) (N : ℤ) := by
  intro x hx
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
  have hjN := (mem_frozenCoordinates N w p q b v a j).mp hj |>.1
  exact Finset.mem_Ico.mpr ⟨Int.natCast_nonneg _,by exact_mod_cast hjN⟩

theorem frozen_residueCount (N : ℕ) (w : ℝ) (p q : ℕ) (b v : ℤ) (a : ℕ → ℕ)
    (u : ℕ) [NeZero u] (e : ZMod u) :
    residueCount u (frozenIntegers N w p q b v a) e =
      ((frozenCoordinates N w p q b v a).filter (fun j : ℕ => (j : ZMod u) = e)).card := by
  classical
  unfold residueCount integerFibre frozenIntegers
  simp only [Finset.filter_image,Int.cast_natCast]
  exact Finset.card_image_of_injective _ Int.ofNat_injective

noncomputable def frozenExceptional (N : ℕ) (w : ℝ) (p q : ℕ) (b v : ℤ) (a : ℕ → ℕ)
    (u : ℕ) (delta V0 : ℝ) : Finset (ZMod u) :=
  exceptionalResidues u (frozenIntegers N w p q b v a) (delta*(N : ℝ)*V0)

theorem mem_frozenExceptional (N : ℕ) (w : ℝ) (p q : ℕ) (b v : ℤ) (a : ℕ → ℕ)
    (u : ℕ) [NeZero u] (delta V0 : ℝ) (e : ZMod u) :
    e ∈ frozenExceptional N w p q b v a u delta V0 ↔
      delta*(N : ℝ)*V0/u <
        |(((frozenCoordinates N w p q b v a).filter (fun j : ℕ => (j : ZMod u) = e)).card : ℝ)-
          ((frozenCoordinates N w p q b v a).card : ℝ)/u| := by
  rw [frozenExceptional,mem_exceptionalResidues,frozen_residueCount,frozenIntegers_card]

end ErdosInverseFrozen

end

section

namespace ErdosInverseFrozen
open NumberTheoryLean ErdosInverseSpectrum

theorem frozen_upper (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ,0 < C ∧ ∃ w0 : ℝ,2 ≤ w0 ∧
      ∀ (N : ℕ) (w : ℝ) (p q : ℕ) (b v : ℤ) (a : ℕ → ℕ),w0 ≤ w → w^eta ≤ (N : ℝ) →
        (∀ t : ℕ,t.Prime → (t : ℝ) ≤ w → (p*q).Coprime t) →
        ((frozenCoordinates N w p q b v a).card : ℝ) ≤ C*(N : ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊ := by
  obtain ⟨C,hC,w0,hw0,hupper⟩ := SmallSieveUpper.progression_small_upper eta heta
  refine ⟨C,hC,w0,hw0,?_⟩
  intro N w p q b v a hw hN hcop
  exact hupper N w N (b+(q : ℤ)*v) (p*q) a hw hN (by simp) hcop

theorem frozen_exceptional_mean (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ,0 < C ∧ ∃ w0 : ℝ,2 ≤ w0 ∧
      ∀ (N Q : ℕ) (w : ℝ) (p q : ℕ) (b v : ℤ) (a : ℕ → ℕ)
        (U : Finset ℕ) (delta : ℝ),
        w0 ≤ w → w^eta ≤ (N : ℝ) →
        (∀ t : ℕ,t.Prime → (t : ℝ) ≤ w → (p*q).Coprime t) →
        (∀ u ∈ U,u.Prime) → (∀ u ∈ U,u ≤ Q) → 0 < U.card → 0 < delta →
        (∑ u ∈ U,((frozenExceptional N w p q b v a u delta (SmallSieveFinite.smallEuler ⌊w⌋₊)).card : ℝ)/(u : ℝ))/(U.card : ℝ) ≤
          (4+8*Real.pi^2)*C*((N : ℝ)+(Q : ℝ)^2)/
            ((U.card : ℝ)*delta^2*(N : ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊) := by
  obtain ⟨C,hC,w0,hw0,hupper⟩ := frozen_upper eta heta
  refine ⟨C,hC,w0,hw0,?_⟩
  intro N Q w p q b v a U delta hw hN hcop hU hQ hn hd
  have hw2 : 2 ≤ w := hw0.trans hw
  have hwpos : 0 < w := by linarith
  have hNpos : 0 < N := by
    exact_mod_cast (Real.rpow_pos_of_pos hwpos eta).trans_le hN
  have hV : 0 < SmallSieveFinite.smallEuler ⌊w⌋₊ :=
    (inv_pos.mpr hwpos).trans_le (SmallSieveFinite.smallEuler_floor_ge_inv w hw2)
  have hm : ((frozenIntegers N w p q b v a).card : ℝ) ≤ C*(N : ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊ := by
    rw [frozenIntegers_card]
    exact hupper N w p q b v a hw hN hcop
  exact exceptional_average_of_survivor_upper U hU hn Q N hNpos 0 _
    (by simpa only [zero_add] using frozenIntegers_subset N w p q b v a) hQ
    delta _ C hd hV hm

end ErdosInverseFrozen

end

end Erdos970

end OAI
