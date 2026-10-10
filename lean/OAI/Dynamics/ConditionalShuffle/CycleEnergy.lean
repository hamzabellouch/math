import OAI.Dynamics.ConditionalShuffle.PrepEnergy

namespace OAI

noncomputable section
open scoped Classical
namespace Thorp.Conditional

lemma mean_fintype_irrel {Ω : Type*} (A B : Fintype Ω) (f : Ω → ℝ) :
    @mean Ω A f = @mean Ω B f := by
  have h : A = B := Subsingleton.elim _ _
  cases h
  rfl

lemma rawPermute_mass {d : ℕ} (v : RawState d) (g : State d) :
    (∑ x, (rawPermute v g).weight x) = ∑ x, v.weight x := Equiv.sum_comp g.symm v.weight

lemma rawPermute_support {d : ℕ} (v : RawState d)
    (hw : ∀ x, v.free x = false → v.weight x = 0) (g : State d) :
    ∀ x, (rawPermute v g).free x = false → (rawPermute v g).weight x = 0 :=
  fun x hx => hw (g.symm x) hx

lemma rawPermute_count {d : ℕ} (v : RawState d) (g : State d) :
    freeCount (rawPermute v g).free = freeCount v.free := freeCount_comp_equiv v.free g.symm

lemma rawIterate_mass (d : ℕ) (v : RawState (d+1)) (t : ℕ) (ω : SweepHistory d t) :
    (∑ x, (rawIterate d v t ω).weight x) = ∑ x, v.weight x := by
  induction t with
  | zero => rfl
  | succ t ih => exact (physicalFlow_sum d _ _ _).trans (ih (Fin.init ω))

lemma rawIterate_support (d : ℕ) (v : RawState (d+1))
    (hw : ∀ x, v.free x = false → v.weight x = 0) (t : ℕ) (ω : SweepHistory d t) :
    ∀ x, (rawIterate d v t ω).free x = false → (rawIterate d v t ω).weight x = 0 := by
  induction t with
  | zero => exact hw
  | succ t ih => exact physicalFlow_support d _ _ (ih (Fin.init ω)) _

lemma rawIterate_count (d : ℕ) (v : RawState (d+1)) (t : ℕ) (ω : SweepHistory d t) :
    freeCount (rawIterate d v t ω).free = freeCount v.free := by
  have hf : (rawIterate d v t ω).free = v.free ∘ (run (d+1) t ω).symm := by
    funext x; exact rawIterate_free d v t ω x
  rw [hf]
  exact freeCount_comp_equiv _ _

namespace OverlayEnergy

abbrev Bits (g : ℕ) := Position (g+2) → Bool
abbrev Prep9 (g : ℕ) := Fin (9*(g+3)) → Bits g
abbrev Prep200 (g : ℕ) := Fin (200*(g+3)) → Bits g
abbrev Active (g : ℕ) := Fin (g+3) → Bits g
abbrev CycleCoins (g : ℕ) := (Prep9 g × Prep200 g) × Active g

def cycle (g : ℕ) (v : RawState (g+3)) (ω : CycleCoins g) : RawState (g+3) :=
  rawIterate (g+2)
    (rawPermute (rawPermute v (run (g+3) (9*(g+3)) ω.1.1))
      (run (g+3) (200*(g+3)) ω.1.2)) (g+3) ω.2

def cyclePerm (g : ℕ) (ω : CycleCoins g) : State (g+3) :=
  run (g+3) (g+3) ω.2 * run (g+3) (200*(g+3)) ω.1.2 * run (g+3) (9*(g+3)) ω.1.1

lemma cycle_free (g : ℕ) (v : RawState (g+3)) (ω : CycleCoins g) (y) :
    (cycle g v ω).free y = v.free ((cyclePerm g ω).symm y) := by
  unfold cycle
  erw [rawIterate_free]
  simp only [cyclePerm, ← Equiv.Perm.inv_def, mul_inv_rev, Equiv.Perm.coe_mul, Function.comp_apply, rawPermute]

lemma cycle_count (g : ℕ) (v : RawState (g+3)) (ω : CycleCoins g) :
    freeCount (cycle g v ω).free = freeCount v.free := by
  exact (rawIterate_count (g+2) _ _ _).trans
    ((rawPermute_count _ _).trans (rawPermute_count v _))

lemma cycle_mass (g : ℕ) (v : RawState (g+3)) (ω : CycleCoins g) :
    (∑ x, (cycle g v ω).weight x) = ∑ x, v.weight x := by
  unfold cycle
  rw [rawIterate_mass, rawPermute_mass, rawPermute_mass]

lemma cycle_support (g : ℕ) (v : RawState (g+3))
    (hw : ∀ x, v.free x = false → v.weight x = 0) (ω : CycleCoins g) :
    ∀ x, (cycle g v ω).free x = false → (cycle g v ω).weight x = 0 :=
  rawIterate_support (g+2) _ (rawPermute_support _ (rawPermute_support _ hw _) _) _ _

lemma cycle_energy_le (g : ℕ) (v : RawState (g+3)) (ω : CycleCoins g) :
    rawEnergy (cycle g v ω) ≤ rawEnergy v := by
  refine (rawIterate_energy_le (g+2) _ _ _).trans_eq ?_
  rw [rawPermute_energy, rawPermute_energy]

def coefficient (g : ℕ) : ℝ := (255/256 : ℝ)^(g+3) + (2^g : ℝ) *
  Real.sqrt ((Fintype.card (Position (g+3)) : ℝ) *
    ((1/2 : ℝ)^(8*(g+3)) + 32*(9/10 : ℝ)^(2^g)) )

lemma coefficient_nonneg (g : ℕ) : 0 ≤ coefficient g := by unfold coefficient; positivity

lemma cycle_expected_energy (g : ℕ) (v : RawState (g+3))
    (hw : ∀ x, v.free x = false → v.weight x = 0) (hz : ∑ x, v.weight x = 0)
    (hf : Fintype.card (Position (g+3)) ≤ 64 * freeCount v.free)
    (hk : freeCount v.free ≤ 2^g)
    (hs : 256*(g+4) ≤ Fintype.card (Position (g+3))) :
    mean (fun ω : CycleCoins g => rawEnergy (cycle g v ω)) ≤
      rawEnergy v * coefficient g := by
  rw [mean_prod]
  change mean (fun ω : Prep9 g × Prep200 g => mean (fun η : Active g =>
    rawEnergy (cycle g v (ω,η)))) ≤ _
  rw [mean_prod]
  apply mean_le_const; intro ω
  let u := rawPermute v (run (g+3) (9*(g+3)) ω)
  have hN : Fintype.card (Position (g+3)) = 8*2^g := by simp [pow_add]; omega
  have hh := prep_sweep_energy (g+1) (2^g) (g+3) (by omega) u
    (rawPermute_support v hw _) ((rawPermute_mass v _).trans hz)
    (by simpa only [show g+1+2 = g+3 by omega, hN] using (le_refl (8*2^g)))
    (by rw [rawPermute_count, hN]; omega)
    (by rwa [rawPermute_count]) hs
  have he : rawEnergy u = rawEnergy v := rawPermute_energy _ _
  have hc : (freeCount u.free : ℝ) ≤ (2^g : ℝ) := by
    rw [rawPermute_count]; exact_mod_cast hk
  have hE := rawEnergy_nonneg v
  have hr : 0 ≤ Real.sqrt ((Fintype.card (Position (g+3)) : ℝ) *
      ((1/2 : ℝ)^(8*(g+3)) + 32*(9/10 : ℝ)^(2^g))) := Real.sqrt_nonneg _
  change mean (fun c : Prep200 g => mean (fun η : Active g =>
    rawEnergy (rawIterate (g+2) (rawPermute u (run (g+3) (200*(g+3)) c)) (g+3) η))) ≤ _
  change _ ≤ rawEnergy v * ((255/256 : ℝ)^(g+3) + (2^g : ℝ) * _)
  have hh' : mean (fun c : Prep200 g => mean (fun η : Active g =>
    rawEnergy (rawIterate (g+2) (rawPermute u (run (g+3) (200*(g+3)) c)) (g+3) η))) ≤
      rawEnergy v * ((255/256 : ℝ)^(g+3) + (freeCount u.free : ℝ)*
        Real.sqrt ((Fintype.card (Position (g+3)) : ℝ) *
          ((1/2 : ℝ)^(8*(g+3)) + 32*(9/10 : ℝ)^(2^g)))) := by
    have heq : mean (fun c : Prep200 g => mean (fun η : Active g =>
        rawEnergy (rawIterate (g+2) (rawPermute u (run (g+3) (200*(g+3)) c)) (g+3) η))) =
        mean (fun c : History (g+1+2) (200*(g+1+2)) =>
          mean (fun η : SweepHistory (g+1+1) (g+3) =>
            rawEnergy (rawIterate (g+1+1) (rawPermute u (run (g+1+2) (200*(g+1+2)) c)) (g+3) η))) := by
      exact mean_fintype_irrel _ _ _
    rw [heq]
    simpa only [show g+1+2 = g+3 by omega, he] using hh
  exact hh'.trans (mul_le_mul_of_nonneg_left
    (add_le_add_right (mul_le_mul_of_nonneg_right hc hr) _) hE)

end OverlayEnergy
end Thorp.Conditional

end

end OAI
