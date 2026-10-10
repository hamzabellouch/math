import OAI.NumberTheory.JointDickman.Counting.CoarseShiftedShort
import OAI.NumberTheory.JointDickman.Arithmetic.ResidueSmoothingIdentity

namespace OAI

/-! # Vanishing energy of the actual coarse feature after progression smoothing -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem coarse_residue_smoothing_energy
    (hMR : RealShortIntervalInput) (hMRT : ComplexShortIntervalInput)
    (hKMT : CharacterDistanceDivergence) (hM : PrimeReciprocalMertensInput)
    (hSD : SquarefreeSelbergDelangeInput) (hSW : SquarefreeCharacterEstimateInput)
    (hMP : PrimeProductMertensInput)
    {J : ℕ} (hJ : 0 < J) (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖ = 1)
    (μ : ℂ) (hμ : ‖μ‖ ≤ 1)
    (hmean : ∀ D : ℝ, 0 < D → Tendsto (centeredBinPrefix J ζ μ D) atTop (𝓝 0))
    {m : ℕ} (hm : 0 < m) (b : Fin m)
    {q : ℕ} [NeZero q] (A scale : ℕ → ℝ) (R M : ℕ → ℕ) (hA : ∀ B, 0 < A B)
    (hscale : Tendsto scale atTop atTop) (hR : Tendsto R atTop atTop) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop, ∀ (j : ℕ), j ≤ M B →
      (1/(A B*scale n))*(∑ u ∈ Ico ⌈A B*scale n⌉₊ ⌊2*(A B*scale n)⌋₊,
        ‖residueSmoothed (fun k =>
          (binLabel (fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)) ζ k-μ)*
            (primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature m B b) k : ℂ))
            q (R B) (u+j)‖^2) < ε := by
  have hq : 0 < q := NeZero.pos q
  have hqR : Tendsto (fun B => q*R B) atTop atTop := tendsto_atTop_mono (fun B => by nlinarith : ∀ B, R B ≤ q*R B) hR
  have hs := all_residues_coarse_shifted_short hMR hMRT hKMT hM hSD hSW hMP
    hJ ζ hζ μ hμ hmean hm b (q := q) A scale (fun B => q*R B) M hA hscale hqR
  intro ε hε
  let δ := ε/((q : ℝ)^3+1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  filter_upwards [hs δ hδ,hR.eventually_gt_atTop 0] with B hB hRB
  filter_upwards [hB,(hscale.const_mul_atTop (hA B)).eventually_gt_atTop 0] with n hn hX
  intro j hj
  let E := fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)
  let w := primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature m B b)
  let g := fun k => (binLabel E ζ k-μ)*(w k : ℂ)
  let I := Ico ⌈A B*scale n⌉₊ ⌊2*(A B*scale n)⌋₊
  have hpoint (u : ℕ) : ‖residueSmoothed g q (R B) (u+j)‖^2 ≤
      (q : ℝ)^2*∑ r : ZMod q, ‖residueBinAverage E ζ μ w r (q*R B : ℕ) (u+j)‖^2 := by
    rw [residueSmoothed_eq_residueBinAverage E ζ μ w hq hRB,norm_mul,Complex.norm_natCast,mul_pow]
    simp only [Nat.cast_add]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    exact single_le_sum
      (f := fun r : ZMod q => ‖residueBinAverage E ζ μ w r (q*R B : ℕ) ((u : ℝ)+j)‖^2)
      (fun r _ => sq_nonneg _) (mem_univ ((u : ZMod q)+(j : ZMod q)))
  have hsum := sum_le_sum (fun r (_ : r ∈ (univ : Finset (ZMod q))) => (hn j hj r).le)
  change (∑ r : ZMod q, (1/(A B*scale n))*(∑ u ∈ I,
    ‖residueBinAverage E ζ μ w r (q*R B : ℕ) (u+j)‖^2)) ≤ _ at hsum
  simp only [sum_const,card_univ,ZMod.card,nsmul_eq_mul] at hsum
  calc
    _ ≤ (1/(A B*scale n))*(∑ u ∈ I, (q : ℝ)^2*
        ∑ r : ZMod q, ‖residueBinAverage E ζ μ w r (q*R B : ℕ) (u+j)‖^2) :=
      mul_le_mul_of_nonneg_left (sum_le_sum (fun u _ => hpoint u)) (by positivity)
    _ = (q : ℝ)^2*∑ r : ZMod q, (1/(A B*scale n))*(∑ u ∈ I,
        ‖residueBinAverage E ζ μ w r (q*R B : ℕ) (u+j)‖^2) := by
      simp only [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro r _
      apply sum_congr rfl
      intro u _
      ring
    _ ≤ (q : ℝ)^2*((q : ℝ)*δ) := mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ < ε := by
      dsimp [δ]
      have hden : 0 < (q : ℝ)^3+1 := by positivity
      have he : (q : ℝ)^2*((q : ℝ)*(ε/((q : ℝ)^3+1))) =
          (q : ℝ)^3*ε/((q : ℝ)^3+1) := by ring
      rw [he]
      apply (div_lt_iff₀ hden).mpr
      nlinarith

end JointDickman

end OAI
