import OAI.Analysis.MarkovType.DyadicSynthesisPairing
import OAI.Analysis.MarkovType.FiniteDualNorming
import OAI.Analysis.MarkovType.FiniteWeightedHolder
import OAI.Analysis.MarkovType.DyadicTreeMartingale
import OAI.Analysis.MarkovType.DyadicConvexPotential

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem dyadicInputMoment_le_of_dual_synthesis {p q T : ℝ}
    (hpq : p.HolderConjugate q) (hT : 1 ≤ T)
    (hStrong : ∀ (N : ℕ) (ψ : DyadicAtom N → E →L[ℝ] ℝ),
      finiteMoment (dyadicLaw N).mass p (dyadicSynthesis N ψ) ≤
        T ^ p * finiteMoment dyadicInputWeight p ψ)
    (N : ℕ) (φ : DyadicAtom N → E) :
    finiteMoment dyadicInputWeight q φ ≤
      T ^ q * finiteMoment (dyadicLaw N).mass q (dyadicSynthesis N φ) := by
  classical
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  let I : ℝ := finiteMoment dyadicInputWeight q φ
  let O : ℝ := finiteMoment (dyadicLaw N).mass q (dyadicSynthesis N φ)
  have hI : 0 ≤ I := Finset.sum_nonneg fun a _ =>
    mul_nonneg (dyadicInputWeight_nonneg a) (Real.rpow_nonneg (norm_nonneg _) q)
  have hO : 0 ≤ O := Finset.sum_nonneg fun ω _ =>
    mul_nonneg ((dyadicLaw N).mass_nonneg ω) (Real.rpow_nonneg (norm_nonneg _) q)
  change I ≤ T ^ q * O
  by_cases hIz : I = 0
  · rw [hIz]
    exact mul_nonneg (Real.rpow_nonneg hT0 q) hO
  have hIpos : 0 < I := lt_of_le_of_ne hI (Ne.symm hIz)
  let D : ℝ := I ^ (1 / q)
  have hD : 0 < D := Real.rpow_pos_of_pos hIpos _
  have hDq : D ^ q = I :=
    weighted_norm_rpow_root dyadicInputWeight dyadicInputWeight_nonneg φ hpq.symm.pos
  obtain ⟨ψ, hψ, hpair⟩ := exists_weighted_dual_norming dyadicInputWeight
    dyadicInputWeight_nonneg φ hpq D hD hDq
  change finiteMoment dyadicInputWeight p ψ ≤ 1 at hψ
  have hM0 : 0 ≤ finiteMoment (dyadicLaw N).mass p (dyadicSynthesis N ψ) :=
    Finset.sum_nonneg fun ω _ => mul_nonneg ((dyadicLaw N).mass_nonneg ω)
      (Real.rpow_nonneg (norm_nonneg _) p)
  have hMoment : finiteMoment (dyadicLaw N).mass p (dyadicSynthesis N ψ) ≤ T ^ p := by
    calc
      _ ≤ T ^ p * finiteMoment dyadicInputWeight p ψ := hStrong N ψ
      _ ≤ T ^ p * 1 := mul_le_mul_of_nonneg_left hψ (Real.rpow_nonneg hT0 p)
      _ = T ^ p := mul_one _
  have hRoot : (finiteMoment (dyadicLaw N).mass p (dyadicSynthesis N ψ)) ^ (1 / p) ≤ T := by
    calc
      _ ≤ (T ^ p) ^ (1 / p) :=
        Real.rpow_le_rpow hM0 hMoment (one_div_pos.mpr hpq.pos).le
      _ = T := by rw [one_div, Real.rpow_rpow_inv hT0 hpq.ne_zero]
  have hPairing : (dyadicLaw N).expect (fun ω =>
      dyadicSynthesis N ψ ω (dyadicSynthesis N φ ω)) = D :=
    (dyadicSynthesis_pairing ψ φ).trans hpair
  have hHolder : |(dyadicLaw N).expect (fun ω =>
      dyadicSynthesis N ψ ω (dyadicSynthesis N φ ω))| ≤
      (finiteMoment (dyadicLaw N).mass p (dyadicSynthesis N ψ)) ^ (1 / p) * O ^ (1 / q) := by
    have hh := abs_sum_weighted_le_holder Finset.univ
      (w := (dyadicLaw N).mass) (a := fun ω => ‖dyadicSynthesis N ψ ω‖)
      (b := fun ω => ‖dyadicSynthesis N φ ω‖)
      (c := fun ω => dyadicSynthesis N ψ ω (dyadicSynthesis N φ ω)) hpq
      (fun ω _ => (dyadicLaw N).mass_nonneg ω) (fun ω _ => norm_nonneg _)
      (fun ω _ => norm_nonneg _) (by
        intro ω _
        simpa only [Real.norm_eq_abs] using
          (dyadicSynthesis N ψ ω).le_opNorm (dyadicSynthesis N φ ω))
    simpa only [FiniteLaw.expect, finiteMoment, O] using hh
  have hDle : D ≤ T * O ^ (1 / q) := by
    rw [hPairing, abs_of_pos hD] at hHolder
    exact hHolder.trans (mul_le_mul_of_nonneg_right hRoot (Real.rpow_nonneg hO _))
  have hOq : (O ^ (1 / q)) ^ q = O :=
    weighted_norm_rpow_root (dyadicLaw N).mass (dyadicLaw N).mass_nonneg
      (dyadicSynthesis N φ) hpq.symm.pos
  have hPower := Real.rpow_le_rpow hD.le hDle hpq.symm.pos.le
  rwa [hDq, Real.mul_rpow hT0 (Real.rpow_nonneg hO _), hOq] at hPower

theorem finiteDyadicCotype_of_dual_synthesis {p q T : ℝ}
    (hpq : p.HolderConjugate q) (hT : 1 ≤ T)
    (hStrong : ∀ (N : ℕ) (ψ : DyadicAtom N → E →L[ℝ] ℝ),
      finiteMoment (dyadicLaw N).mass p (dyadicSynthesis N ψ) ≤
        T ^ p * finiteMoment dyadicInputWeight p ψ) :
    FiniteDyadicCotype E q (T ^ q) := by
  intro t ht
  let N := DyadicTree.height t
  let u := DyadicTree.pad N t
  have hu : DyadicTree.Full N u := DyadicTree.pad_full N t le_rfl
  have h := dyadicInputMoment_le_of_dual_synthesis hpq hT hStrong N
    (DyadicTree.coefficients N u)
  rw [DyadicTree.coefficients_inputMoment hu hpq.symm.pos,
    DyadicTree.synthesis_moment hu q] at h
  simpa only [u, DyadicTree.root_pad, ht, norm_zero, Real.zero_rpow hpq.symm.ne_zero,
    zero_add, DyadicTree.energy_pad hpq.symm.pos, DyadicTree.moment_pad] using h

end MarkovSuperreflexivity

end

end OAI
