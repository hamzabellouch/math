import OAI.MeasureTheory.Falconer.Recursion.ProfileExcess
import OAI.MeasureTheory.Falconer.Recursion.Entry

namespace OAI

/-! # Entry depth for two actual regularized classes -/

namespace Falconer
open Set MeasureTheory

 theorem regularized_profiles_entry {d : ℕ} (hd : 0 < d)
    (Q : Fin 2 → DyadicCube d) (ρ : Fin 2 → Measure (Space d))
    (m : Fin 2 → ℝ → ℝ) (N q : ℕ) {χ β lam : ℝ}
    (hreg : ∀ i, Regularization.RegularizedProfileData (Q i) (ρ i) N
      ((d:ℝ)/2+χ) lam (m i))
    (hχ : 0 < χ) (hβ : 0 < β) (hlam : 0 ≤ lam)
    (hsmall : β+((d:ℝ)+4)*lam < χ/4)
    (hN : 0 < N) (hlarge : 2*(d:ℝ) ≤ β*N) (hq : 0 < q) (hqsmall : 4*q ≤ N) :
    let A := fun i => profileExcess (d := d) (m i) N
    ∃ c : ℕ, c < N ∧ β*N/(2*(d:ℝ)) ≤ (c:ℝ) ∧ (c:ℝ) < N/4 ∧
      c+q ≤ N ∧
      (∀ i n, c ≤ n → n ≤ N → β-(d:ℝ)/N ≤ A i n) ∧
      min (PlanarFalconer.height (A 0) 0 c) (PlanarFalconer.height (A 1) 0 c) ≤
        β+((d:ℝ)+4)*lam ∧
      (∀ i, 2*β-2*(d:ℝ)/N ≤ PlanarFalconer.potential (A i) c N q) ∧
      -A 0 c-A 1 c+
        min (PlanarFalconer.height (A 0) 0 c) (PlanarFalconer.height (A 1) 0 c)+
        ((2*A 0 c-PlanarFalconer.potential (A 0) c N q)+
          (2*A 1 c-PlanarFalconer.potential (A 1) c N q))/2 ≤
        -β+((d:ℝ)+4)*lam+2*(d:ℝ)/N := by
  apply exists_assembly_entry (fun i => profileExcess (d := d) (m i) N) N q
    (Nat.cast_pos.mpr hd) hχ hβ (by positivity) hsmall hN hlarge hq hqsmall
  · intro i
    exact profileExcess_zero (Q i) (ρ i) (hreg i)
  · intro i n hn
    simpa only [add_sub_cancel_left] using
      profileExcess_envelope (Q i) (ρ i) (hreg i) hN hn
  · intro i a b ha hb
    exact profileExcess_lipschitz (Q i) (ρ i) (hreg i) hN b a hb ha

end Falconer

end OAI
