import OAI.NumberTheory.CubicMoment.Transform.MetaplecticRetainedSubpower
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticNegativeSubpower
import OAI.NumberTheory.CubicMoment.Estimates.MellinWeightFamily

namespace OAI

/-! The actual retained means for both height signs with one constant
for a uniformly controlled logarithmic weight family. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem UniformLogWeights.metaplectic_retained_voronoi_subpower
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (ha : MetaplecticCoefficientBounds a)
    {M : ℝ} (hMV : MontgomeryVaughanBound M) (hM : 0 ≤ M)
    {ι : Type*} {W : ι → ℝ → ℂ} (h : UniformLogWeights W) (ℓ : ℤ)
    {η B : ℝ} (hη : 0 < η) (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i, ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ Y A X J T : ℝ, 1 ≤ Y → 0 ≤ A → 0 < X → 1 ≤ J → 0 < T →
      norm r ≤ Y^B → J ≤ Y^B →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-A) →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-A) →
      (∫ t in T..2*T, ‖metaplecticPrefactor r ℓ*
        ∑ nd ∈ metaplecticDualBall J,
          metaplecticDualTerm a r ℓ (fun x => W i x*mellinPhase t x) A X nd‖)/T ≤
        K*Real.sqrt X*Y^η*(1+Real.sqrt (4*J/(norm r*T))) := by
  obtain ⟨ε,C,hε,hC,hpower⟩ := metaplectic_retained_loss_small_power hη hB
  obtain ⟨D,hD,hbound⟩ := metaplectic_retained_voronoi_mean ha hε hMV hM
  obtain ⟨L,hL,hLm⟩ := h.mellin_norm_moment (1/2) 0
  have hmass (i : ι) : (∫ τ : ℝ, ‖mellin (W i) ((1/2:ℂ)+(τ:ℂ)*Complex.I)‖) ≤ L := by
    simpa only [pow_zero,one_mul,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using hLm i (1/2) (by norm_num)
  let P := 3^(7/2:ℝ)*(2*Real.pi)
  have hP : 0 < P := by dsimp [P]; positivity
  refine ⟨D*L/P*C,by positivity,?_⟩
  intro i r hr hsr Y A X J T hY hA hX hJ hT hRY hJY hm hp
  have hR := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hb := hbound r hr hsr ℓ (W i) (h.compact i) (h.positive i) (h.smooth i) A X J T hA hX
    (zero_lt_one.trans_le hJ) hT hm hp
  have hs := hpower Y (norm r) J hY hR hJ hRY hJY
  calc
    _ ≤ Real.sqrt X/P*
        (((Nat.log 2 ⌊3*J⌋₊+1:ℕ):ℝ)*D*(6*J)^(3*ε/2)*norm r^(2*ε)*
          (1+Real.sqrt (4*J/(norm r*T)))*
            (∫ τ : ℝ, ‖mellin (W i) ((1/2:ℂ)+(τ:ℂ)*Complex.I)‖)) := hb
    _ ≤ Real.sqrt X/P*
        (((Nat.log 2 ⌊3*J⌋₊+1:ℕ):ℝ)*D*(6*J)^(3*ε/2)*norm r^(2*ε)*
          (1+Real.sqrt (4*J/(norm r*T)))*L) := by
      gcongr
      exact hmass i
    _ = (D*L/P*Real.sqrt X)*
        (((Nat.log 2 ⌊3*J⌋₊+1:ℕ):ℝ)*(6*J)^(3*ε/2)*norm r^(2*ε))*
          (1+Real.sqrt (4*J/(norm r*T))) := by ring
    _ ≤ (D*L/P*Real.sqrt X)*(C*Y^η)*
          (1+Real.sqrt (4*J/(norm r*T))) := by gcongr
    _ = _ := by ring


theorem UniformLogWeights.metaplectic_retained_negative_voronoi_subpower
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (ha : MetaplecticCoefficientBounds a)
    {M : ℝ} (hMV : MontgomeryVaughanBound M) (hM : 0 ≤ M)
    {ι : Type*} {W : ι → ℝ → ℂ} (h : UniformLogWeights W) (ℓ : ℤ)
    {η B : ℝ} (hη : 0 < η) (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i, ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ Y A X J T : ℝ, 1 ≤ Y → 0 ≤ A → 0 < X → 1 ≤ J → 0 < T →
      norm r ≤ Y^B → J ≤ Y^B →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-A) →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-A) →
      (∫ t in T..2*T, ‖metaplecticPrefactor r ℓ*
        ∑ nd ∈ metaplecticDualBall J,
          metaplecticDualTerm a r ℓ (fun x => W i x*mellinPhase (-t) x) A X nd‖)/T ≤
        K*Real.sqrt X*Y^η*(1+Real.sqrt (4*J/(norm r*T))) := by
  obtain ⟨ε,C,hε,hC,hpower⟩ := metaplectic_retained_loss_small_power hη hB
  obtain ⟨D,hD,hbound⟩ := metaplectic_retained_negative_voronoi_mean ha hε hMV hM
  obtain ⟨L,hL,hLm⟩ := h.mellin_norm_moment (1/2) 0
  have hmass (i : ι) : (∫ τ : ℝ, ‖mellin (W i) ((1/2:ℂ)+(τ:ℂ)*Complex.I)‖) ≤ L := by
    simpa only [pow_zero,one_mul,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using hLm i (1/2) (by norm_num)
  let P := 3^(7/2:ℝ)*(2*Real.pi)
  have hP : 0 < P := by dsimp [P]; positivity
  refine ⟨D*L/P*C,by positivity,?_⟩
  intro i r hr hsr Y A X J T hY hA hX hJ hT hRY hJY hm hp
  have hR := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hb := hbound r hr hsr ℓ (W i) (h.compact i) (h.positive i) (h.smooth i) A X J T hA hX
    (zero_lt_one.trans_le hJ) hT hm hp
  have hs := hpower Y (norm r) J hY hR hJ hRY hJY
  calc
    _ ≤ Real.sqrt X/P*
        (((Nat.log 2 ⌊3*J⌋₊+1:ℕ):ℝ)*D*(6*J)^(3*ε/2)*norm r^(2*ε)*
          (1+Real.sqrt (4*J/(norm r*T)))*
            (∫ τ : ℝ, ‖mellin (W i) ((1/2:ℂ)+(τ:ℂ)*Complex.I)‖)) := hb
    _ ≤ Real.sqrt X/P*
        (((Nat.log 2 ⌊3*J⌋₊+1:ℕ):ℝ)*D*(6*J)^(3*ε/2)*norm r^(2*ε)*
          (1+Real.sqrt (4*J/(norm r*T)))*L) := by
      gcongr
      exact hmass i
    _ = (D*L/P*Real.sqrt X)*
        (((Nat.log 2 ⌊3*J⌋₊+1:ℕ):ℝ)*(6*J)^(3*ε/2)*norm r^(2*ε))*
          (1+Real.sqrt (4*J/(norm r*T))) := by ring
    _ ≤ (D*L/P*Real.sqrt X)*(C*Y^η)*
          (1+Real.sqrt (4*J/(norm r*T))) := by gcongr
    _ = _ := by ring


end CubicFirstMoment

end

end OAI
