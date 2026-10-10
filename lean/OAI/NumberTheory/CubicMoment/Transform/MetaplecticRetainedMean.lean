import OAI.NumberTheory.CubicMoment.Transform.MetaplecticActualBlockMean
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticNormDyads

namespace OAI

/-! The whole actual retained polynomial, with its fixed cutoff, is
controlled by its canonical finite norm-dyad partition. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

private lemma mean_norm_finset_sum_normalized {ι : Type*} (S : Finset ι)
    (f : ι → ℝ → ℂ) (hf : ∀ i ∈ S, Continuous (f i))
    {T c B : ℝ} (hT : 0 < T) (hc : 0 < c)
    (hB : ∀ i ∈ S, ((∫ t in T..2*T, ‖f i t‖)/T)/c ≤ B) :
    ((∫ t in T..2*T, ‖∑ i ∈ S, f i t‖)/T)/c ≤ (S.card:ℝ)*B := by
  have hh := mean_norm_finset_sum_le S f hf hT (fun _ => B*c)
    (fun i hi => (div_le_iff₀ hc).mp (hB i hi))
  simp only [Finset.sum_const,nsmul_eq_mul] at hh
  apply (div_le_iff₀ hc).mpr
  nlinarith only [hh]

theorem metaplectic_actual_retained_mean
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (ha : MetaplecticCoefficientBounds a)
    {ε M : ℝ} (hε : 0 < ε) (hMV : MontgomeryVaughanBound M) (hM : 0 ≤ M) :
    ∃ D : ℝ, 0 < D ∧ ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ (S : Finset (MetaplecticDualArgument × PrimaryArgument)) (J T : ℝ),
      0 < J → 0 < T → (∀ nd ∈ S, metaplecticDualNorm nd ≤ J) →
      ∀ (ℓ : ℤ) (τ : ℝ),
      ((∫ t in T..2*T, ‖∑ nd ∈ S, metaplecticNormalizedDualCoefficient a r ℓ nd*
        mellinPhase (τ-t) (metaplecticDualNorm nd)‖)/T)/Real.sqrt (norm r) ≤
          ((Nat.log 2 ⌊3*J⌋₊+1:ℕ):ℝ)*D*(6*J)^(3*ε/2)*norm r^(2*ε)*
            (1+Real.sqrt (4*J/(norm r*T))) := by
  obtain ⟨D,hD,hb⟩ := metaplectic_actual_norm_block_mean ha hε hMV hM
  refine ⟨D,hD,?_⟩
  intro r hr hsr S J T hJ hT hS ℓ τ
  have hR := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hRroot := Real.sqrt_pos.mpr hR
  let P := S.image metaplecticNormDyadIndex
  let f := fun j : ℕ => fun t : ℝ => ∑ nd ∈ metaplecticNormDyad S j,
    metaplecticNormalizedDualCoefficient a r ℓ nd*mellinPhase (τ-t) (metaplecticDualNorm nd)
  let B := D*(6*J)^(3*ε/2)*norm r^(2*ε)*(1+Real.sqrt (4*J/(norm r*T)))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hf (j : ℕ) : Continuous (f j) := by
    apply continuous_finsetSum
    intro nd hnd
    apply continuous_const.mul
    unfold mellinPhase
    fun_prop
  have hblock (j : ℕ) (hj : j ∈ P) : ((∫ t in T..2*T, ‖f j t‖)/T)/Real.sqrt (norm r) ≤ B := by
    have hI := metaplecticNormDyadLength_pos j
    have hIJ := metaplectic_norm_dyad_length_le S hS hj
    have hx := hb r hr hsr (metaplecticNormDyad S j) (metaplecticNormDyadLength j) T hI hT
      (fun nd hnd => metaplectic_norm_dyad_bounds hnd) ℓ τ
    apply hx.trans
    have hp : (3*metaplecticNormDyadLength j)^(3*ε/2) ≤ (6*J)^(3*ε/2) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
    have hs : Real.sqrt (2*metaplecticNormDyadLength j/(norm r*T)) ≤
        Real.sqrt (4*J/(norm r*T)) :=
      Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (by linarith) (mul_pos hR hT).le)
    dsimp [B]
    gcongr
  have he (t : ℝ) : (∑ nd ∈ S, metaplecticNormalizedDualCoefficient a r ℓ nd*
      mellinPhase (τ-t) (metaplecticDualNorm nd)) = ∑ j ∈ P, f j t :=
    metaplectic_norm_dyad_partition S (fun nd =>
      metaplecticNormalizedDualCoefficient a r ℓ nd*mellinPhase (τ-t) (metaplecticDualNorm nd))
  have hh := mean_norm_finset_sum_normalized P f (fun j _ => hf j) hT hRroot hblock
  simp_rw [he]
  apply hh.trans
  calc
    _ ≤ ((Nat.log 2 ⌊3*J⌋₊+1:ℕ):ℝ)*B := mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr (metaplectic_norm_dyad_count S hS)) hB
    _ = _ := by dsimp [B]; ring

end CubicFirstMoment

end

end OAI
