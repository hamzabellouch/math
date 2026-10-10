import OAI.Combinatorics.PolynomialVacuum.Algebra.ZeroFiltration
import OAI.Combinatorics.PolynomialVacuum.Algebra.LastPolynomial

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

def MinusZero {n : ℕ} (ψ : State n) : Prop :=
  ∀ s i, s i=Spin.minus → killSite i (ψ s)=0

theorem initialCup_spectator_zero {n : ℕ} (ψ : State n) (hz : MinusZero ψ)
    (i j : Fin (n+1)) (hji : j≠i) (s : Fin (n+2) → Spin)
    (hs : s (spectatorSlot j (pairRight i))=Spin.minus) : killSite j (initialCup ψ i s)=0 := by
  obtain ⟨l,rfl⟩:=Fin.exists_succAbove_eq hji
  rw [omitPair_spectatorSlot] at hs
  simp only [initialCup,map_mul,killSite_C]
  rw [killSite_rename_injective _ Fin.succAbove_right_injective,hz _ _ hs,map_zero,mul_zero]

theorem cupPrescription_spectator_zero {n : ℕ} (ψ : State n) (hz : MinusZero ψ)
    (i j : Fin (n+1)) (hji : j≠i) (s : Fin (n+2) → Spin)
    (hs : s j.castSucc=Spin.minus) : killSite j (cupPrescription ψ i s)=0 := by
  have ht:=transportCup_spectator_zero i j (rightSpectators i) _ _ (rightSpectators_path i)
    (initialCup ψ i) (fun s hs => initialCup_spectator_zero ψ hz i j hji s hs) s
      (by simpa only [spectatorSlot_last] using hs)
  simp only [cupPrescription,map_mul,ht,mul_zero]

theorem dividedCupPrescription_spectator_zero {n : ℕ} (ψ : State n) (hz : MinusZero ψ)
    (i j : Fin (n+1)) (hji : j≠i) (s : Fin (n+2) → Spin)
    (hs : s j.castSucc=Spin.minus) : killSite j (dividedCupPrescription ψ i s)=0 := by
  have h := cupPrescription_spectator_zero ψ hz i j hji s hs
  rw [cupPrescription_factor,map_mul,killSite_X,ite_eq_right (Ne.symm hji)] at h
  exact (mul_eq_zero.mp h).resolve_left (X_ne_zero i)

theorem interpolateState_spectator_zero {n : ℕ} (ψ : State n) (χ : State (n+1))
    (hψ : LowerExchange (liftState ψ) n) (hz : MinusZero ψ) (hχ : MinusZero χ)
    (s : Fin (n+2) → Spin) (j : Fin (n+1)) (hs : s j.castSucc=Spin.minus) :
    killSite j.castSucc (interpolateState ψ χ s)=0 := by
  have hv : ∀ i, killSite j (cupPrescription ψ i s)=0 := by
    intro i
    by_cases hij : i=j
    · subst i; simp [cupPrescription_factor]
    · exact cupPrescription_spectator_zero ψ hz i j (Ne.symm hij) s hs
  by_cases hl : s (Fin.last (n+1))=Spin.plus
  · simp only [interpolateState,ite_eq_left hl]
    exact canonicalInterpolant_killSite _ (cupPrescription_collision ψ hψ s) j hv
  · have hw : ∀ i, killSite j (dividedCupPrescription ψ i s)=0 := by
      intro i
      by_cases hij : i=j
      · subst i; exact dividedCupPrescription_marked_zero ψ j s hs hl
      · exact dividedCupPrescription_spectator_zero ψ hz i j (Ne.symm hij) s hs
    have hc := canonicalInterpolant_killSite _ (dividedCupPrescription_collision ψ hψ s) j hw
    simp only [interpolateState,ite_eq_right hl,map_add,map_mul,hc,mul_zero,zero_add]
    split_ifs
    · rw [map_mul,killSite_rename,hχ _ _ hs,map_zero,mul_zero]
    · exact map_zero _

theorem interpolateState_last_minus_zero {n : ℕ} (ψ : State n) (χ : State (n+1))
    (s : Fin (n+2) → Spin) (hs : s (Fin.last (n+1))=Spin.minus) :
    killSite (Fin.last (n+1)) (interpolateState ψ χ s)=0 := by
  simp [interpolateState,hs]

theorem interpolateState_minusZero {n : ℕ} (ψ : State n) (χ : State (n+1))
    (hψ : LowerExchange (liftState ψ) n) (hz : MinusZero ψ) (hχ : MinusZero χ) :
    MinusZero (interpolateState ψ χ) := by
  intro s j hs
  refine Fin.lastCases ?_ (fun k hk => ?_) j hs
  · exact interpolateState_last_minus_zero ψ χ s
  · exact interpolateState_spectator_zero ψ χ hψ hz hχ s k hk

end PolynomialVacuumAlgebra

end OAI
