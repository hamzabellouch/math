import OAI.Probability.ContinuumTransition.MomentEnergy

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

noncomputable def physicalCoupling (t : ℝ) (σ R : ℕ → ℝ) (z w : Lattice) : ℝ :=
  (t*kernelHeight)*mixedEnvelope σ R z w

theorem physicalCoupling_nonneg {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (z w : Lattice) :
    0 ≤ physicalCoupling t σ R z w := mul_nonneg (mul_nonneg ht kernelHeight_pos.le)
      (mixedEnvelope_nonneg hσ (fun n => le_trans zero_le_one (hR n)) z w)

theorem physicalCoupling_row {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    {κ : Type} [Fintype κ] (e : κ → Lattice) (he : Function.Injective e) (z : Lattice) :
    ∑ j, physicalCoupling t σ R z (e j) ≤ 2197*t*kernelHeight*(∑' n, σ n) := by
  simp only [physicalCoupling, ← Finset.mul_sum]
  have hh := mul_le_mul_of_nonneg_left (sum_mixedEnvelope_le e he hσ hR hs z)
    (mul_nonneg ht kernelHeight_pos.le)
  nlinarith only [hh]

theorem physicalCoupling_self_le {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ) (z : Lattice) :
    physicalCoupling t σ R z z ≤ 2197*t*kernelHeight*(∑' n, σ n) := by
  simpa only [Finset.univ_unique, Finset.sum_singleton] using
    physicalCoupling_row ht hσ hR hs (fun _ : Unit => z) (fun _ _ _ => Subsingleton.elim _ _) z

theorem occupation_eq_fiber {ι κ : Type} [Fintype ι] [Fintype κ]
    (x : ι → Space) (c : ι → κ) (e : κ → Lattice) (he : Function.Injective e)
    (hc : ∀ i, cellIndex (x i) = e (c i)) (k : κ) :
    occupation (latticeCell (e k)) x = (Fintype.card {i : ι // c i = k} : ℝ) := by
  unfold occupation
  congr 1
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro i
  change cellIndex (x i) = e k ↔ c i = k
  rw [hc i, he.eq_iff]

theorem sum_physicalCoupling_occupations {ι κ : Type} [Fintype ι] [Fintype κ]
    (t : ℝ) (σ R : ℕ → ℝ) (z : Lattice)
    (x : ι → Space) (c : ι → κ) (e : κ → Lattice) (he : Function.Injective e)
    (hc : ∀ i, cellIndex (x i) = e (c i)) :
    ∑ j, physicalCoupling t σ R z (cellIndex (x j)) =
      ∑ k, physicalCoupling t σ R z (e k)*occupation (latticeCell (e k)) x := by
  simp_rw [hc, occupation_eq_fiber x c e he hc]
  rw [sum_comp_eq_sum_fibres c (fun k => physicalCoupling t σ R z (e k))]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

end ContinuumTemperature
end

end OAI
