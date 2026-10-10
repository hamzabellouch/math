import OAI.NumberTheory.Ostmann.Construction.SupportedInitialLogSum
import OAI.NumberTheory.Ostmann.Construction.InitialHalfListWeights

namespace OAI

/-! # The actual two cutoff weights followed by balanced small cells -/

namespace Ostmann
open scoped Classical BigOperators

theorem balancedTupleSet_mass_one {A : Type*} [Fintype A] (n : ℕ)
    (μ : Fin n → A → ℝ) (good : Fin n → A → Prop)
    (hmass : ∀ i, ∑ p, μ i p = 1)
    (hgood : ∀ i p, μ i p ≠ 0 → good i p) :
    1 ≤ ∑ x ∈ balancedTupleSet n good, productPrior μ x := by
  have hi (i : Fin n) : (∑ p, if good i p then μ i p else 0) = 1 := by
    rw [← hmass i]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hg : good i p
    · simp only [ite_eq_left hg]
    · have hz : μ i p = 0 := by contrapose! hg; exact hgood i p hg
      simp only [ite_eq_right hg, hz]
  simpa only [one_pow] using balancedTupleSet_mass n μ good 1 (by norm_num) (fun i => (hi i).ge)

/-- The additional top and compensation cells cost no balanced mass when
all of their live primes were selected to be balanced. The two broad-shell
cutoffs keep their original weights and their separate small centers. -/
theorem exists_initial_balanced_cell_weights (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (b d r m : ℕ) (Tb Td : ℝ)
    (μb : Fin b → P → ℝ) (μd : Fin d → P → ℝ) (μc : Fin r → P → ℝ)
    (gb : Fin b → P → Prop) (gd : Fin d → P → Prop) (gc : Fin r → P → Prop)
    (hm : 1 ≤ m) (hb : b ≤ m) (hd : d ≤ m) (hTb : Tb ≤ m) (hTd : Td ≤ m)
    (hlogb : ∀ i (p : P), μb i p ≠ 0 → Real.log (p : ℝ) ≤ Real.exp Tb)
    (hlogd : ∀ i (p : P), μd i p ≠ 0 → Real.log (p : ℝ) ≤ Real.exp Td)
    (hmb : ∀ i, (1 / 2 : ℝ) ≤ ∑ p, if gb i p then μb i p else 0)
    (hmd : ∀ i, (1 / 2 : ℝ) ≤ ∑ p, if gd i p then μd i p else 0)
    (hmc : ∀ i, ∑ p, μc i p = 1)
    (hgc : ∀ i p, μc i p ≠ 0 → gc i p) :
    ∃ cb ∈ Finset.Icc (0 : ℤ) ⌈(b : ℝ) * Real.exp Tb⌉₊,
    ∃ cd ∈ Finset.Icc (0 : ℤ) ⌈(d : ℝ) * Real.exp Td⌉₊,
      Real.exp (-(2 * (Real.log 2 + 2)) * m) ≤
        ∑ x ∈ balancedTupleSet (b + (d + r)) (Fin.append gb (Fin.append gd gc)),
          productPrior (Fin.append μb (Fin.append μd μc)) x *
            (initialLogSumWeight (fun p : P => (p : ℕ)) cb (fun i => x (i.castAdd (d + r))) *
              initialLogSumWeight (fun p : P => (p : ℕ)) cd
                (fun i => x ((i.castAdd r).natAdd b))) := by
  obtain ⟨cb, hcb, hbmass⟩ := exists_supported_prime_log_sum_center P hP b m Tb μb gb
    hm hb hTb hlogb hmb
  obtain ⟨cd, hcd, hdmass⟩ := exists_supported_prime_log_sum_center P hP d m Td μd gd
    hm hd hTd hlogd hmd
  refine ⟨cb, hcb, cd, hcd, ?_⟩
  have hcmass := balancedTupleSet_mass_one r μc gc hmc hgc
  let Bmass := ∑ x ∈ balancedTupleSet b gb, productPrior μb x *
    initialLogSumWeight (fun p : P => (p : ℕ)) cb x
  let Dmass := ∑ x ∈ balancedTupleSet d gd, productPrior μd x *
    initialLogSumWeight (fun p : P => (p : ℕ)) cd x
  let Cmass := ∑ x ∈ balancedTupleSet r gc, productPrior μc x
  change Real.exp (-(Real.log 2 + 2) * m) ≤ Bmass at hbmass
  change Real.exp (-(Real.log 2 + 2) * m) ≤ Dmass at hdmass
  change 1 ≤ Cmass at hcmass
  have hCD := balancedHalfMass_append d r μd μc gd gc
    (initialLogSumWeight (fun p : P => (p : ℕ)) cd) (fun _ => 1)
  simp only [mul_one] at hCD
  have hfull := balancedHalfMass_append b (d + r) μb (Fin.append μd μc) gb (Fin.append gd gc)
    (initialLogSumWeight (fun p : P => (p : ℕ)) cb)
    (fun y => initialLogSumWeight (fun p : P => (p : ℕ)) cd (fun i => y (i.castAdd r)))
  rw [hCD] at hfull
  rw [hfull]
  change Real.exp (-(2 * (Real.log 2 + 2)) * m) ≤ Bmass * (Dmass * Cmass)
  have hb0 : 0 ≤ Bmass := (Real.exp_nonneg _).trans hbmass
  have hd0 : 0 ≤ Dmass := (Real.exp_nonneg _).trans hdmass
  calc
    _ = Real.exp (-(Real.log 2 + 2) * m) * Real.exp (-(Real.log 2 + 2) * m) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Bmass * Dmass := mul_le_mul hbmass hdmass (Real.exp_nonneg _) hb0
    _ ≤ Bmass * (Dmass * Cmass) := by nlinarith [mul_nonneg hb0 hd0]

end Ostmann

end OAI
