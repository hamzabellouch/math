import OAI.NumberTheory.Ostmann.Construction.InitialBalancedCellWeights
import OAI.NumberTheory.Ostmann.Construction.HalfPrimeInitialAmplitude

namespace OAI

/-! # The two selected original cutoff weights in the initial positive statistic -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem balanced_half_initial_statistic
    (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)] (hP : ∀ q ∈ P, q.Prime)
    (S : (q : P) → Finset (ZMod (q : ℕ))) (favorable : P → Bool)
    (b d r m : ℕ) (Tb Td : ℝ)
    (μ₀ : P → ℝ) (μb : Fin b → P → ℝ) (μd : Fin d → P → ℝ) (μc : Fin r → P → ℝ)
    (hμb : ∀ i q, 0 ≤ μb i q) (hμd : ∀ i q, 0 ≤ μd i q) (hμc : ∀ i q, 0 ≤ μc i q)
    (hm : 1 ≤ m) (hb : b ≤ m) (hd : d ≤ m) (hTb : Tb ≤ m) (hTd : Td ≤ m)
    (hlogb : ∀ i (q : P), μb i q ≠ 0 → Real.log (q : ℝ) ≤ Real.exp Tb)
    (hlogd : ∀ i (q : P), μd i q ≠ 0 → Real.log (q : ℝ) ≤ Real.exp Td)
    (hmb : ∀ i, (1 / 2 : ℝ) ≤ ∑ q, if (1 / 3 : ℝ) ≤ residueDensity (S q) ∧
      residueDensity (S q) ≤ 2 / 3 then μb i q else 0)
    (hmd : ∀ i, (1 / 2 : ℝ) ≤ ∑ q, if (1 / 3 : ℝ) ≤ residueDensity (S q) ∧
      residueDensity (S q) ≤ 2 / 3 then μd i q else 0)
    (hmc : ∀ i, ∑ q, μc i q = 1)
    (hgc : ∀ i q, μc i q ≠ 0 → (1 / 3 : ℝ) ≤ residueDensity (S q) ∧ residueDensity (S q) ≤ 2 / 3)
    (E : Finset ℤ) (δ c : ℝ) (hδ : 0 ≤ δ) (hc : 0 ≤ c)
    (hendpoint : ∀ a ∈ E, ∀ q : P, (a : ZMod (q : ℕ)) ∈ S q)
    (hmean : (E.card : ℝ) * δ ≤ ∑ a ∈ E,
      (∑ q : P, (μ₀ q : ℂ) * primePhysicalTest (S q) true (favorable q)
        (a : ZMod (q : ℕ))).re)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X)
    (hψ : ∀ x, 0 ≤ (ψ x).re) (hcE : ∀ a ∈ E, c ≤ (ψ ((a : ℝ) / X)).re) :
    ∃ cb ∈ Finset.Icc (0 : ℤ) ⌈(b : ℝ) * Real.exp Tb⌉₊,
    ∃ cd ∈ Finset.Icc (0 : ℤ) ⌈(d : ℝ) * Real.exp Td⌉₊,
      let n := b + (d + r)
      let μ := Fin.append μb (Fin.append μd μc)
      let w := fun x : Fin n → P =>
        initialLogSumWeight (fun q : P => (q : ℕ)) cb (fun i => x (i.castAdd (d + r))) *
        initialLogSumWeight (fun q : P => (q : ℕ)) cd (fun i => x ((i.castAdd r).natAdd b))
      let ν := Fin.cons μ₀ μ
      let F : Fin (n + 1) → (q : P) → ZMod (q : ℕ) → ℂ := primeHalfTests P S favorable
      let W := fun y : Fin (n + 1) → P => (w (Fin.tail y) : ℂ)
      (E.card : ℝ) * (c * (Real.exp (-(2 * (Real.log 2 + 2)) * m) *
        (1 / 2 : ℝ) ^ n * δ) ^ 2) ≤
        ‖∑ x : Fin ((n + 1) + (n + 1)) → P,
          (productPrior (Fin.append ν ν) x : ℂ) * doubledHalfWeight W x *
            physicalTupleSum P x (Fin.append F F) ψ X‖ := by
  let good := fun q : P => (1 / 3 : ℝ) ≤ residueDensity (S q) ∧ residueDensity (S q) ≤ 2 / 3
  have hif (ν : P → ℝ) : (∑ q, @ite ℝ (good q) (Classical.propDecidable (good q)) (ν q) 0) =
      ∑ q, if (1 / 3 : ℝ) ≤ residueDensity (S q) ∧ residueDensity (S q) ≤ 2 / 3 then ν q else 0 := by
    apply Finset.sum_congr rfl
    intro q _
    by_cases hh : good q
    · have hh' : (1 / 3 : ℝ) ≤ residueDensity (S q) ∧ residueDensity (S q) ≤ 2 / 3 := hh
      simp only [hh, hh', true_and, ite_true]
    · have hh' : ¬ ((1 / 3 : ℝ) ≤ residueDensity (S q) ∧ residueDensity (S q) ≤ 2 / 3) := hh
      simp only [hh, hh', ite_false]
  have hmb' (i : Fin b) : (1 / 2 : ℝ) ≤ ∑ q, @ite ℝ (good q) (Classical.propDecidable (good q)) (μb i q) 0 :=
    (hmb i).trans_eq (hif (μb i)).symm
  have hmd' (i : Fin d) : (1 / 2 : ℝ) ≤ ∑ q, @ite ℝ (good q) (Classical.propDecidable (good q)) (μd i q) 0 :=
    (hmd i).trans_eq (hif (μd i)).symm
  obtain ⟨cb, hcb, cd, hcd, hmass⟩ := exists_initial_balanced_cell_weights P hP b d r m Tb Td
    μb μd μc (fun _ => good) (fun _ => good) (fun _ => good)
    hm hb hd hTb hTd hlogb hlogd
    hmb' hmd' hmc hgc
  refine ⟨cb, hcb, cd, hcd, ?_⟩
  dsimp only
  let μ := Fin.append μb (Fin.append μd μc)
  let w := fun x : Fin (b + (d + r)) → P =>
    initialLogSumWeight (fun q : P => (q : ℕ)) cb (fun i => x (i.castAdd (d + r))) *
    initialLogSumWeight (fun q : P => (q : ℕ)) cd (fun i => x ((i.castAdd r).natAdd b))
  have hμ (i : Fin (b + (d + r))) (q : P) : 0 ≤ μ i q := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [μ, Fin.append_left] using hμb j q
    · refine Fin.addCases (fun k => ?_) (fun k => ?_) j
      · simpa only [μ, Fin.append_right, Fin.append_left] using hμd k q
      · simpa only [μ, Fin.append_right] using hμc k q
  have hgood : Fin.append (fun _ : Fin b => good)
      (Fin.append (fun _ : Fin d => good) (fun _ : Fin r => good)) =
      (fun _ : Fin (b + (d + r)) => good) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.append_left]
    · refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;> simp
  rw [hgood] at hmass
  apply primeHalfTests_statistic_lower P hP S favorable μ₀ μ w hμ
    (fun x => mul_nonneg (initialLogSumWeight_nonneg _ _ _) (initialLogSumWeight_nonneg _ _ _))
    E (balancedTupleSet (b + (d + r)) (fun _ => good))
    (Real.exp (-(2 * (Real.log 2 + 2)) * m)) δ c (Real.exp_nonneg _) hδ hc
    ?_ ?_ hendpoint hmean ψ X hX hψ hcE
  · simpa only [μ, w, mul_assoc] using hmass
  · intro x hx i
    have hh : ∀ i, good (x i) := by
      simpa only [balancedTupleSet, Finset.mem_filter, Finset.mem_univ, true_and] using hx
    exact hh i

end Ostmann

end OAI
