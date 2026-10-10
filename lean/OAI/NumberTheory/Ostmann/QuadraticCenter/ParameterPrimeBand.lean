import OAI.NumberTheory.Ostmann.QuadraticCenter.ParameterSelectionBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Ostmann.Preliminaries
open scoped BigOperators

def logarithmicPrimeBand (y : ℝ) : Finset ℕ :=
  (⌊Real.exp (2 * y)⌋₊).primesLE \ (⌊Real.exp y⌋₊).primesLE

lemma mem_logarithmicPrimeBand {y : ℝ} {p : ℕ} :
    0 ≤ y → (p ∈ logarithmicPrimeBand y ↔ p.Prime ∧ y < Real.log p ∧ Real.log p ≤ 2 * y) := by
  intro _
  classical
  simp only [logarithmicPrimeBand, Finset.mem_sdiff, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hpu, hp⟩, hpl⟩
    have hpu' : (p : ℝ) ≤ Real.exp (2 * y) :=
      (by exact_mod_cast hpu : (p : ℝ) ≤ ⌊Real.exp (2 * y)⌋₊).trans
        (Nat.floor_le (Real.exp_pos _).le)
    have hpl' : Real.exp y < (p : ℝ) := by
      apply (Nat.floor_lt (Real.exp_pos y).le).mp
      exact lt_of_not_ge (fun h => hpl ⟨h, hp⟩)
    exact ⟨hp, (Real.lt_log_iff_exp_lt (by exact_mod_cast hp.pos)).mpr hpl',
      (Real.log_le_iff_le_exp (by exact_mod_cast hp.pos)).mpr hpu'⟩
  · rintro ⟨hp, hlo, hhi⟩
    have hu : p ≤ ⌊Real.exp (2 * y)⌋₊ := Nat.le_floor
      ((Real.log_le_iff_le_exp (by exact_mod_cast hp.pos)).mp hhi)
    refine ⟨⟨hu, hp⟩, ?_⟩
    rintro ⟨hle, _⟩
    have hl : (p : ℝ) ≤ Real.exp y :=
      (by exact_mod_cast hle : (p : ℝ) ≤ ⌊Real.exp y⌋₊).trans
        (Nat.floor_le (Real.exp_pos _).le)
    exact not_lt_of_ge ((Real.log_le_iff_le_exp (by exact_mod_cast hp.pos)).mpr hl) hlo

lemma primeWeight_prime_interval_lower (m n : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) :
    Real.log n - Real.log m - 2 * (Real.log 4 + 4) ≤
      primeWeight (n.primesLE \ m.primesLE) := by
  have hs : m.primesLE ⊆ n.primesLE := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hp).1.trans hmn,
      (Nat.mem_primesLE.mp hp).2⟩
  have hn := mertens_prime_sum_lower n (hm.trans hmn)
  have hm' := (abs_le.mp (mertens_prime_sum m hm)).2
  have hid := Finset.sum_sdiff hs (f := fun p : ℕ => Real.log p / p)
  unfold primeWeight
  linarith

lemma logarithmicPrimeBand_weight_lower {y : ℝ} (hy : Real.log 2 ≤ y) :
    y - Real.log 2 - 2 * (Real.log 4 + 4) ≤ primeWeight (logarithmicPrimeBand y) := by
  have hy0 : 0 ≤ y := (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)).trans hy
  have hl := log_floor_exp_bounds hy
  have hu := log_floor_exp_bounds (show Real.log 2 ≤ 2 * y by linarith)
  have hmn : ⌊Real.exp y⌋₊ ≤ ⌊Real.exp (2 * y)⌋₊ :=
    Nat.floor_mono (Real.exp_le_exp.mpr (by linarith))
  have h := primeWeight_prime_interval_lower _ _ hl.1 hmn
  change y - Real.log 2 - 2 * (Real.log 4 + 4) ≤
    primeWeight ((⌊Real.exp (2 * y)⌋₊).primesLE \ (⌊Real.exp y⌋₊).primesLE)
  linarith [hl.2.2, hu.2.1]

def boundedLogarithmicPrimeBand (Q : ℕ) (y : ℝ) : Finset (PrimeUpTo Q) :=
  Finset.univ.filter (fun p => p.val ∈ logarithmicPrimeBand y)

lemma boundedLogarithmicPrimeBand_image (Q : ℕ) (y : ℝ)
    (hQ : ⌊Real.exp (2 * y)⌋₊ ≤ Q) :
    (boundedLogarithmicPrimeBand Q y).image Subtype.val = logarithmicPrimeBand y := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact (Finset.mem_filter.mp hq).2
  · intro hp
    have hpp := Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1
    have hpQ : p ∈ Q.primesLE := Nat.mem_primesLE.mpr ⟨hpp.1.trans hQ, hpp.2⟩
    exact Finset.mem_image.mpr ⟨⟨p, hpQ⟩, by simp [boundedLogarithmicPrimeBand, hp], rfl⟩

lemma boundedLogarithmicPrimeBand_weight_lower (Q : ℕ) {y : ℝ}
    (hy : Real.log 2 ≤ y) (hQ : ⌊Real.exp (2 * y)⌋₊ ≤ Q) :
    y - Real.log 2 - 2 * (Real.log 4 + 4) ≤ boundedPrimeWeight (boundedLogarithmicPrimeBand Q y) := by
  rw [← primeWeight_image_val, boundedLogarithmicPrimeBand_image Q y hQ]
  exact logarithmicPrimeBand_weight_lower hy

end Ostmann.QuadraticCenter

end

end OAI
