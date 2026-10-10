import OAI.NumberTheory.CubicMoment.Transform.MetaplecticCodePartition
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticFreeReflection

namespace OAI

/-! Ordinary mean values for the exact finite prefix partition. The
coefficient hypotheses here are precisely the support data supplied by
`metaplectic_retained_support_partition`. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma mean_norm_finset_sum_le {ι : Type*} (S : Finset ι) (f : ι → ℝ → ℂ)
    (hf : ∀ i ∈ S, Continuous (f i)) {T : ℝ} (hT : 0 < T)
    (B : ι → ℝ) (hB : ∀ i ∈ S, (∫ t in T..2*T, ‖f i t‖)/T ≤ B i) :
    (∫ t in T..2*T, ‖∑ i ∈ S, f i t‖)/T ≤ ∑ i ∈ S, B i := by
  have hc := continuous_finsetSum S hf
  have hn := continuous_finsetSum S (fun i hi => (hf i hi).norm)
  calc
    _ ≤ (∫ t in T..2*T, ∑ i ∈ S, ‖f i t‖)/T := by
      apply div_le_div_of_nonneg_right _ hT.le
      exact intervalIntegral.integral_mono (by linarith)
        (hc.norm.intervalIntegrable _ _) (hn.intervalIntegrable _ _)
        (fun t => norm_sum_le _ _)
    _ = ∑ i ∈ S, (∫ t in T..2*T, ‖f i t‖)/T := by
      rw [intervalIntegral.integral_finsetSum (fun i hi => (hf i hi).norm.intervalIntegrable _ _),
        Finset.sum_div]
    _ ≤ _ := Finset.sum_le_sum hB

def metaplecticPrefixAmplitude (r : Eisenstein) (C : ℝ)
    (p : MetaplecticDyadPrefix r) : ℝ :=
  C*3^((max ((p.2.1:ℤ)-1) 0:ℤ)/3:ℝ)*Real.sqrt (norm p.2.2.2.2)*
    min (norm r) (norm p.2.2.2.1.val*norm p.2.2.2.2) /
    (Real.sqrt ((3:ℝ)^((p.2.1:ℝ)-1)*norm p.2.2.2.1.val*norm p.2.2.2.2^3)*norm p.1)

theorem metaplectic_code_block_mean {ε M : ℝ} (hε : 0 < ε)
    (hMV : MontgomeryVaughanBound M) (hM : 0 ≤ M) :
    ∃ D : ℝ, 0 < D ∧ ∀ (a : Eisenstein → MetaplecticDualArgument → ℂ)
      (C : ℝ), 0 ≤ C → ∀ r : Eisenstein, primary r →
      ∀ (S : Finset (MetaplecticRetainedCode r)) (p : MetaplecticDyadPrefix r),
      (∀ z ∈ S, IsCoprime z.2.2.val r) →
      (∀ z ∈ S, ‖a r (metaplecticRetainedDecode r z).1‖ ≤
        C*3^((max ((z.2.1.1:ℤ)-1) 0:ℤ)/3:ℝ)*Real.sqrt (norm z.2.1.2.2.2)) →
      ∀ I T : ℝ, p ∈ S.image metaplecticCodePrefix → 0 < T →
      (∀ z ∈ S, I/2 ≤ metaplecticDualNorm (metaplecticRetainedDecode r z) ∧
        metaplecticDualNorm (metaplecticRetainedDecode r z) ≤ I) →
      ∀ ℓ : ℤ, ∀ τ : ℝ,
      (∫ t in T..2*T, ‖∑ w ∈ metaplecticCodeFreeSet S p,
        metaplecticNormalizedDualCoefficient a r ℓ (metaplecticPrefixArgument r p.2 w,p.1)*
          mellinPhase (τ-t) (metaplecticDualNorm (metaplecticPrefixArgument r p.2 w,p.1))‖)/T ≤
        Real.sqrt (M*D)*(I/metaplecticFreeScale p)^(ε/2)*metaplecticPrefixAmplitude r C p*
          (1+Real.sqrt (2*(I/metaplecticFreeScale p)/T)) := by
  obtain ⟨D,hD,hbound⟩ := metaplectic_reflected_free_mean hε hMV hM
  refine ⟨D,hD,?_⟩
  intro a C hC r hr S p hcop hcoef I T hp hT hdyad ℓ τ
  let F := metaplecticCodeFreeSet S p
  let v := fun w => metaplecticNormalizedDualCoefficient a r ℓ
    (metaplecticPrefixArgument r p.2 w,p.1)
  have hj : -1 ≤ (p.2.1:ℤ)-1 := by omega
  have hnat : (((p.2.1:ℤ)-1+1).toNat) = p.2.1 := by omega
  have hcp (w : Eisenstein) (hw : w ∈ F) : IsCoprime w r := by
    obtain ⟨z,hz,_,rfl⟩ := metaplectic_mem_codeFreeSet.mp hw
    exact hcop z hz
  have hcf (w : Eisenstein) (hw : w ∈ F) :
      ‖a r (metaplecticPrefixArgument r p.2 w)‖ ≤
        C*3^((max ((p.2.1:ℤ)-1) 0:ℤ)/3:ℝ)*Real.sqrt (norm p.2.2.2.2) := by
    obtain ⟨z,hz,hzp,rfl⟩ := metaplectic_mem_codeFreeSet.mp hw
    have he := hcoef z hz
    rw [metaplectic_decode_of_prefix hzp] at he
    have hs : z.2.1 = p.2 := congrArg (fun q : MetaplecticDyadPrefix r => q.2) hzp
    simpa only [hs] using he
  have hv (w : Eisenstein) (hw : w ∈ F) :
      ‖v w‖^2 ≤ (metaplecticPrefixAmplitude r C p)^2/norm w := by
    have h := metaplectic_actual_free_coefficient_sq hC hr p.1 ℓ
      (metaplecticPrefixArgument r p.2 w) hj p.2.2.1
      (metaplecticDivisorPrimary r p.2.2.2.1).property p.2.2.2.2.property
      (metaplectic_codeFreeSet_primary S p hw) (hcp w hw)
      (metaplecticFreeArgument_frequency p.2.1 p.2.2.1
        (metaplecticDivisorPrimary r p.2.2.2.1) p.2.2.2.2
        (primary_ne_zero (metaplectic_codeFreeSet_primary S p hw))) (hcf w hw)
    simpa only [v,metaplecticPrefixAmplitude,hnat,metaplecticDivisorPrimary] using h
  have hK : 0 ≤ metaplecticPrefixAmplitude r C p := by
    have hd := norm_pos_of_ne_zero (primary_ne_zero p.1.property)
    have hh := norm_pos_of_ne_zero (primary_ne_zero (metaplecticDivisorPrimary r p.2.2.2.1).property)
    have hhp := norm_pos_of_ne_zero (primary_ne_zero p.2.2.2.2.property)
    have hR := norm_pos_of_ne_zero (primary_ne_zero hr)
    unfold metaplecticPrefixAmplitude
    change 0 ≤ C*3^((max ((p.2.1:ℤ)-1) 0:ℤ)/3:ℝ)*Real.sqrt (norm p.2.2.2.2)*
      min (norm r) (norm (metaplecticDivisorPrimary r p.2.2.2.1)*norm p.2.2.2.2)/_
    positivity
  have hb := hbound F (fun w hw => metaplectic_codeFreeSet_primary S p hw)
    v (I/metaplecticFreeScale p) (metaplecticPrefixAmplitude r C p) T τ
    (metaplecticFreeScale p) (metaplectic_codeFreeSet_length_one S hp
      (fun z hz => (hdyad z hz).2)) hK hT (metaplecticFreeScale_pos p)
    (metaplectic_codeFreeSet_dyad S p hdyad) hv
  convert hb using 1
  congr 2
  funext t
  congr 1
  apply Finset.sum_congr rfl
  intro w hw
  rw [metaplectic_prefix_frequency p
    (primary_ne_zero (metaplectic_codeFreeSet_primary S p hw))]

/-- Reassembling the chosen support codes costs only the sum of the explicit
free-block majorants. The original finite frequency polynomial is retained. -/
theorem metaplectic_code_mean {ε M : ℝ} (hε : 0 < ε)
    (hMV : MontgomeryVaughanBound M) (hM : 0 ≤ M) :
    ∃ D : ℝ, 0 < D ∧ ∀ (a : Eisenstein → MetaplecticDualArgument → ℂ)
      (C : ℝ), 0 ≤ C → ∀ r : Eisenstein, primary r →
      ∀ S : Finset (MetaplecticRetainedCode r),
      (∀ z ∈ S, IsCoprime z.2.2.val r) →
      (∀ z ∈ S, ‖a r (metaplecticRetainedDecode r z).1‖ ≤
        C*3^((max ((z.2.1.1:ℤ)-1) 0:ℤ)/3:ℝ)*Real.sqrt (norm z.2.1.2.2.2)) →
      ∀ I T : ℝ, 0 < T →
      (∀ z ∈ S, I/2 ≤ metaplecticDualNorm (metaplecticRetainedDecode r z) ∧
        metaplecticDualNorm (metaplecticRetainedDecode r z) ≤ I) →
      ∀ ℓ : ℤ, ∀ τ : ℝ,
      (∫ t in T..2*T, ‖∑ z ∈ S,
        metaplecticNormalizedDualCoefficient a r ℓ (metaplecticRetainedDecode r z)*
          mellinPhase (τ-t) (metaplecticDualNorm (metaplecticRetainedDecode r z))‖)/T ≤
        ∑ p ∈ S.image metaplecticCodePrefix,
          Real.sqrt (M*D)*(I/metaplecticFreeScale p)^(ε/2)*metaplecticPrefixAmplitude r C p*
            (1+Real.sqrt (2*(I/metaplecticFreeScale p)/T)) := by
  obtain ⟨D,hD,hb⟩ := metaplectic_code_block_mean hε hMV hM
  refine ⟨D,hD,?_⟩
  intro a C hC r hr S hcop hcoef I T hT hdyad ℓ τ
  let f := fun p : MetaplecticDyadPrefix r => fun t : ℝ =>
    ∑ w ∈ metaplecticCodeFreeSet S p,
      metaplecticNormalizedDualCoefficient a r ℓ (metaplecticPrefixArgument r p.2 w,p.1)*
        mellinPhase (τ-t) (metaplecticDualNorm (metaplecticPrefixArgument r p.2 w,p.1))
  have hf (p : MetaplecticDyadPrefix r) : Continuous (f p) := by
    apply continuous_finsetSum
    intro w hw
    apply continuous_const.mul
    unfold mellinPhase
    fun_prop
  have he (t : ℝ) : (∑ z ∈ S,
      metaplecticNormalizedDualCoefficient a r ℓ (metaplecticRetainedDecode r z)*
        mellinPhase (τ-t) (metaplecticDualNorm (metaplecticRetainedDecode r z))) =
      ∑ p ∈ S.image metaplecticCodePrefix, f p t :=
    metaplectic_code_partition S (fun nd =>
      metaplecticNormalizedDualCoefficient a r ℓ nd*mellinPhase (τ-t) (metaplecticDualNorm nd))
  simp_rw [he]
  exact mean_norm_finset_sum_le _ f (fun p _ => hf p) hT _
    (fun p hp => hb a C hC r hr S p hcop hcoef I T hp hT hdyad ℓ τ)

end CubicFirstMoment

end

end OAI
