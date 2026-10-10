import OAI.NumberTheory.CubicMoment.Transform.MetaplecticRetainedPowers

namespace OAI

/-! The retained contribution with its arbitrary small arithmetic loss
absorbed uniformly over conductor and dual length. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem metaplectic_retained_voronoi_subpower
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (ha : MetaplecticCoefficientBounds a)
    {M : ℝ} (hMV : MontgomeryVaughanBound M) (hM : 0 ≤ M)
    (ℓ : ℤ) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {η B : ℝ} (hη : 0 < η) (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ Y A X J T : ℝ, 1 ≤ Y → 0 ≤ A → 0 < X → 1 ≤ J → 0 < T →
      norm r ≤ Y^B → J ≤ Y^B →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-A) →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-A) →
      (∫ t in T..2*T, ‖metaplecticPrefactor r ℓ*
        ∑ nd ∈ metaplecticDualBall J,
          metaplecticDualTerm a r ℓ (fun x => W x*mellinPhase t x) A X nd‖)/T ≤
        K*Real.sqrt X*Y^η*(1+Real.sqrt (4*J/(norm r*T))) := by
  obtain ⟨ε,C,hε,hC,hpower⟩ := metaplectic_retained_loss_small_power hη hB
  obtain ⟨D,hD,hbound⟩ := metaplectic_retained_voronoi_mean ha hε hMV hM
  let L := ∫ τ : ℝ, ‖mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)‖
  have hL : 0 ≤ L := integral_nonneg (fun _ => _root_.norm_nonneg _)
  let P := 3^(7/2:ℝ)*(2*Real.pi)
  have hP : 0 < P := by dsimp [P]; positivity
  refine ⟨D*L/P*C,by positivity,?_⟩
  intro r hr hsr Y A X J T hY hA hX hJ hT hRY hJY hm hp
  have hR := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hb := hbound r hr hsr ℓ W hW hpos hsm A X J T hA hX
    (zero_lt_one.trans_le hJ) hT hm hp
  have hs := hpower Y (norm r) J hY hR hJ hRY hJY
  calc
    _ ≤ Real.sqrt X/P*
        (((Nat.log 2 ⌊3*J⌋₊+1:ℕ):ℝ)*D*(6*J)^(3*ε/2)*norm r^(2*ε)*
          (1+Real.sqrt (4*J/(norm r*T)))*L) := hb
    _ = (D*L/P*Real.sqrt X)*
        (((Nat.log 2 ⌊3*J⌋₊+1:ℕ):ℝ)*(6*J)^(3*ε/2)*norm r^(2*ε))*
          (1+Real.sqrt (4*J/(norm r*T))) := by ring
    _ ≤ (D*L/P*Real.sqrt X)*(C*Y^η)*
          (1+Real.sqrt (4*J/(norm r*T))) := by gcongr
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
