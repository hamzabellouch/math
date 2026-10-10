import OAI.NumberTheory.Ostmann.Construction.InitialLogSumScale
import OAI.NumberTheory.Ostmann.Construction.HalfPrimeInitialAmplitude
import OAI.NumberTheory.Ostmann.Construction.WordProductWindow

namespace OAI

/-! # The original two cutoff weights control the full sampled product -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def initialHalfCutoffWeight {P : Type*} (value : P → ℕ)
    (b d r : ℕ) (cb cd : ℝ) (x : Fin (b + (d + r)) → P) : ℝ :=
  initialLogSumWeight value cb (fun i => x (i.castAdd (d + r))) *
    initialLogSumWeight value cd (fun i => x ((i.castAdd r).natAdd b))

theorem initialHalfCutoffWeight_nonneg {P : Type*} (value : P → ℕ)
    (b d r : ℕ) (cb cd : ℝ) (x : Fin (b + (d + r)) → P) :
    0 ≤ initialHalfCutoffWeight value b d r cb cd x :=
  mul_nonneg (initialLogSumWeight_nonneg _ _ _) (initialLogSumWeight_nonneg _ _ _)

theorem initialHalfCutoffWeight_le_one {P : Type*} (value : P → ℕ)
    (b d r : ℕ) (cb cd : ℝ) (x : Fin (b + (d + r)) → P) :
    initialHalfCutoffWeight value b d r cb cd x ≤ 1 := by
  exact (mul_le_mul (initialLogSumWeight_le_one _ _ _) (initialLogSumWeight_le_one _ _ _)
    (initialLogSumWeight_nonneg _ _ _) zero_le_one).trans_eq (one_mul 1)

theorem initial_half_cutoff_log_product (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (b d r : ℕ) (μ₀ : P → ℝ) (μb : Fin b → P → ℝ)
    (μd : Fin d → P → ℝ) (μc : Fin r → P → ℝ) (G cb cd : ℝ) (center : Fin r → ℝ)
    (hG : ∀ q : P, μ₀ q ≠ 0 → |Real.log (q : ℝ) - G| ≤ 1)
    (hc : ∀ i (q : P), μc i q ≠ 0 → |Real.log (q : ℝ) - center i| ≤ 1)
    (x : Fin ((b + (d + r)) + 1) → P)
    (hprior : productPrior (Fin.cons μ₀ (Fin.append μb (Fin.append μd μc))) x ≠ 0)
    (hw : initialHalfCutoffWeight (fun q : P => (q : ℕ)) b d r cb cd (Fin.tail x) ≠ 0) :
    |Real.log (∏ i, (x i : ℝ)) - (G + cb + cd + ∑ i, center i)| ≤ r + 3 := by
  have hpriorAt (i : Fin ((b + (d + r)) + 1)) :
      (Fin.cons μ₀ (Fin.append μb (Fin.append μd μc)) : Fin ((b + (d + r)) + 1) → P → ℝ) i (x i) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hprior) i (Finset.mem_univ i)
  have hgiant : |Real.log (x 0 : ℝ) - G| ≤ 1 :=
    hG _ (by simpa only [Fin.cons_zero] using hpriorAt 0)
  have hcell (i : Fin r) :
      |Real.log (Fin.tail x ((i.natAdd d).natAdd b) : ℝ) - center i| ≤ 1 := by
    apply hc
    simpa only [Fin.cons_succ, Fin.append_right, Fin.tail] using
      hpriorAt (((i.natAdd d).natAdd b).succ)
  have hcells : |(∑ i : Fin r, Real.log (Fin.tail x ((i.natAdd d).natAdd b) : ℝ)) -
      ∑ i, center i| ≤ r := by
    rw [← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      using Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin r))) => hcell i)
  obtain ⟨hwb, hwd⟩ := mul_ne_zero_iff.mp hw
  have hb := (initialLogSumWeight_support (fun q : P => (q : ℕ)) cb _ hwb).le
  have hd := (initialLogSumWeight_support (fun q : P => (q : ℕ)) cd _ hwd).le
  rw [Real.log_prod (fun i _ => by exact_mod_cast (hP _ (x i).property).ne_zero)]
  rw [Fin.sum_univ_succ, Fin.sum_univ_add, Fin.sum_univ_add]
  obtain ⟨hglo, hghi⟩ := abs_le.mp hgiant
  obtain ⟨hblo, hbhi⟩ := abs_le.mp hb
  obtain ⟨hdlo, hdhi⟩ := abs_le.mp hd
  obtain ⟨hclo, hchi⟩ := abs_le.mp hcells
  dsimp only [Fin.tail] at hblo hbhi hdlo hdhi hclo hchi
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Ostmann

end OAI
