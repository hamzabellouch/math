import OAI.NumberTheory.CubicMoment.Estimates.SinglePrimeBilinear
import OAI.NumberTheory.CubicMoment.Estimates.SemiprimeSmoothWeights

namespace OAI

/-! The centered bilinear estimate for the concrete smooth prime pieces
of the semiprime branch. Their coefficient energy is derived from the
actual support and the proved norm bound for the roughness transition. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma bounded_prime_dyad_energy (P : Finset Eisenstein) (α : Eisenstein → ℂ)
    {A : ℝ} (hA : 0 ≤ A) (hP : ∀ p ∈ P, primary p ∧ norm p ≤ 2*A)
    (hα : ∀ p ∈ P, ‖α p‖ ≤ 1) : (∑ p ∈ P, ‖α p‖^2) ≤ 36*A := by
  have hsub : P ⊆ primaryElementBall (2*A) := fun p hp => mem_primaryElementBall.mpr (hP p hp)
  calc
    _ ≤ ∑ _p ∈ P, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact (pow_le_pow_left₀ (_root_.norm_nonneg _) (hα p hp) 2).trans_eq (one_pow 2)
    _ = (P.card:ℝ) := by simp
    _ ≤ ((primaryElementBall (2*A)).card:ℝ) := Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ 18*(2*A) := primaryElementBall_card_le (by positivity)
    _ = _ := by ring

theorem semiprime_prime_bilinear
    (hSW : KummerPrimeSiegelWalfisz) (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput a)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (k U : ℕ) :
    ∃ (η : ℝ) (G : ℕ) (K B₀ : ℝ), 0 < η ∧ η ≤ 1 ∧ 0 < K ∧
      ∀ r s A B u : ℝ, 0 ≤ r → 0 ≤ s → 1 ≤ B → B₀ ≤ B →
      (2*B)^(1/2:ℝ) < B → B^(1-η/16) ≤ A →
      A ≤ B^2/(1+Real.log B)^G → |u| ≤ (1+Real.log B)^U →
      ‖∑ p ∈ fullPrimeSupport 2 (fun _ : Unit => semiprimeSmoothWeight r) (fun _ => A) (),
          ∑ q ∈ fullPrimeSupport 2 (fun _ : Unit => semiprimeSmoothWeight s) (fun _ => B) (),
            semiprimeSmoothWeight r (norm p/A)*semiprimeSmoothWeight s (norm q/B)*
              centeredGauss (p*q)*normTwist u (p*q)‖ ≤
        K*A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^k := by
  let L : Ici (0:ℝ) × Ici (1:ℝ) → ℝ := fun z => z.2
  let W : Ici (0:ℝ) × Ici (1:ℝ) → ℝ → ℂ := fun z => semiprimeSmoothWeight z.1
  have hW : UniformLogWeights W := semiprimeSmoothWeights.reindex Prod.fst
  obtain ⟨η,G,K,B₀,hη,hη1,hK,hbound⟩ := single_prime_centered_bilinear
    (M := 36) hSW hpub hHuxley hperiod hMV hC (by norm_num) hGI hGQ hVor hGamma
    L W (fun z => z.2.property) hW
    (fun z _ hx => semiprimeSmoothWeight_low z.1 hx)
    (fun z _ hx => semiprimeSmoothWeight_high z.1 hx) k 0 U
  refine ⟨η,G,K,B₀,hη,hη1,hK,?_⟩
  intro r s A B u hr hs hB hB₀ hrough hAlo hAhi hu
  have hAp : 0 < A := (Real.rpow_pos_of_pos (zero_lt_one.trans_le hB) _).trans_le hAlo
  let P := fullPrimeSupport 2 (fun _ : Unit => semiprimeSmoothWeight r) (fun _ => A) ()
  have hP (p : Eisenstein) (hp : p ∈ P) : primary p ∧ norm p/A ∈ Icc 1 2 := by
    have hmem := (fullPrimeSupport_mem_iff (fun _ : Unit => semiprimeSmoothWeight r)
      (fun _ => A) (fun _ => hAp) (fun _ _ hx => semiprimeSmoothWeight_high r hx) () p).mp hp
    refine ⟨hmem.1.1,?_,?_⟩
    · exact le_of_not_gt (fun hx => hmem.2 (semiprimeSmoothWeight_low r hx))
    · exact le_of_not_gt (fun hx => hmem.2 (semiprimeSmoothWeight_high r hx))
  have henergy := bounded_prime_dyad_energy P
    (fun p => semiprimeSmoothWeight r (norm p/A)) hAp.le
    (fun p hp => ⟨(hP p hp).1,(div_le_iff₀ hAp).mp (hP p hp).2.2⟩)
    (fun p _ => semiprimeSmoothWeight_norm r (norm p/A))
  have hb := hbound (⟨s,hs⟩,⟨B,hB⟩) A u P
    (fun p => semiprimeSmoothWeight r (norm p/A)) hB₀ hrough hAlo hAhi hu hP
    (by simpa only [pow_zero,mul_one] using henergy)
  exact hb

end CubicFirstMoment

end

end OAI
