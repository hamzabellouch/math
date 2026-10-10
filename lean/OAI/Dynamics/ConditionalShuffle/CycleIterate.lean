import OAI.Dynamics.ConditionalShuffle.OverlayDistance

namespace OAI

noncomputable section
open scoped Classical
namespace Thorp.Conditional.OverlayEnergy

def cycles (g : ℕ) (v : RawState (g+3)) : (n : ℕ) → (Fin n → CycleCoins g) → RawState (g+3)
  | 0, _ => v
  | n+1, ω => cycle g (cycles g v n (Fin.init ω)) (ω (Fin.last n))

def cyclesPerm (g : ℕ) : (n : ℕ) → (Fin n → CycleCoins g) → State (g+3)
  | 0, _ => 1
  | n+1, ω => cyclePerm g (ω (Fin.last n)) * cyclesPerm g n (Fin.init ω)

lemma cycles_free (g : ℕ) (v : RawState (g+3)) (n : ℕ) (ω : Fin n → CycleCoins g) (y) :
    (cycles g v n ω).free y = v.free ((cyclesPerm g n ω).symm y) := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih =>
      rw [cycles, cycle_free, ih]
      rfl

lemma cycles_count (g : ℕ) (v : RawState (g+3)) (n : ℕ) (ω : Fin n → CycleCoins g) :
    freeCount (cycles g v n ω).free = freeCount v.free := by
  induction n with
  | zero => rfl
  | succ n ih => exact (cycle_count g _ _).trans (ih (Fin.init ω))

lemma cycles_mass (g : ℕ) (v : RawState (g+3)) (n : ℕ) (ω : Fin n → CycleCoins g) :
    (∑ x, (cycles g v n ω).weight x) = ∑ x, v.weight x := by
  induction n with
  | zero => rfl
  | succ n ih => exact (cycle_mass g _ _).trans (ih (Fin.init ω))

lemma cycles_support (g : ℕ) (v : RawState (g+3))
    (hw : ∀ x, v.free x = false → v.weight x = 0) (n : ℕ) (ω : Fin n → CycleCoins g) :
    ∀ x, (cycles g v n ω).free x = false → (cycles g v n ω).weight x = 0 := by
  induction n with
  | zero => exact hw
  | succ n ih => exact cycle_support g _ (ih (Fin.init ω)) _

lemma cycles_energy_le (g : ℕ) (v : RawState (g+3)) (n : ℕ) (ω : Fin n → CycleCoins g) :
    rawEnergy (cycles g v n ω) ≤ rawEnergy v := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact (cycle_energy_le g _ _).trans (ih (Fin.init ω))

lemma cycles_expected_energy (g : ℕ) (v : RawState (g+3))
    (hw : ∀ x, v.free x = false → v.weight x = 0) (hz : ∑ x, v.weight x = 0)
    (hf : Fintype.card (Position (g+3)) ≤ 64 * freeCount v.free)
    (hk : freeCount v.free ≤ 2^g)
    (hs : 256*(g+4) ≤ Fintype.card (Position (g+3))) (n : ℕ) :
    mean (fun ω : Fin n → CycleCoins g => rawEnergy (cycles g v n ω)) ≤
      rawEnergy v * coefficient g ^ n := by
  induction n with
  | zero => simp only [cycles, mean_const, pow_zero, mul_one, le_refl]
  | succ n ih =>
      rw [mean_function_snoc]
      simp only [cycles, Fin.init_snoc, Fin.snoc_last]
      have hh := mean_le_mean (fun ω : Fin n → CycleCoins g => cycle_expected_energy g
        (cycles g v n ω) (cycles_support g v hw n ω) ((cycles_mass g v n ω).trans hz)
        (by rwa [cycles_count]) (by rwa [cycles_count]) hs)
      rw [mean_mul_const] at hh
      exact hh.trans ((mul_le_mul_of_nonneg_right ih (coefficient_nonneg g)).trans_eq (by
        rw [pow_succ, mul_assoc]))

end Thorp.Conditional.OverlayEnergy

end

end OAI
