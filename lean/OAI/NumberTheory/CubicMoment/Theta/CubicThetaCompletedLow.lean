import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRawVoronoi
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticLowPowers
import OAI.NumberTheory.CubicMoment.Estimates.GammaQuotientGrowth

namespace OAI

/-! The actual nonzero-angular low-height bound. The fixed dilation and
numerical factor of the proved formula are absorbed in its constant. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicTheta_dilated_power {X : ℝ} (hX : 0<X) (σ : ℝ) :
    (X/729)^(-σ)=X^(-σ)*(729:ℝ)^σ := by
  rw [Real.div_rpow hX.le (by norm_num),Real.rpow_neg (by norm_num : (0:ℝ)≤729),
    div_eq_mul_inv,inv_inv]

theorem uniform_cubicTheta_completed_low
    {ι : Type*} {W : ι→ℝ→ℂ} (hW : UniformLogWeights W)
    {ℓ : ℤ} (hℓ : ℓ≠0) {ε σ : ℝ} (hε : 0<ε) (hσ : 0<σ) :
    ∃ K : ℝ, 0≤K ∧ ∀ i r, primary r → Squarefree r → ∀ X : ℝ, 0<X →
      ‖metaplecticCompleted r ℓ (W i) X‖≤
        K*Real.sqrt (norm r)*norm r^(ε+2*σ)*X^(-σ) := by
  have hGamma := angularGammaQuotientStripBound_proved (metaplecticAngularShift ℓ)
    (-σ-1/6) (lt_of_lt_of_le (by norm_num : -(1/2:ℝ)<0) (metaplecticAngularShift_nonneg ℓ))
  obtain ⟨C,hC,hTr⟩ := hW.metaplecticTransform_bound ℓ hσ hGamma
  obtain ⟨M,hM,hMass⟩ := metaplectic_coefficient_mass_small_power
    cubicThetaCoreCoefficient_bounds hε hσ
  let S : ℝ := ∑' d : PrimaryArgument,norm d^(-5/2-3*σ)
  have hS : 0≤S := tsum_nonneg (fun d => Real.rpow_nonneg (norm_nonneg d) _)
  let P : ℝ := 3^(7/2:ℝ)*(2*Real.pi)^2
  have hP : 0<P := by dsimp [P]; positivity
  refine ⟨81*C*M*S*(2*Real.pi)^(-4*σ)*(729:ℝ)^σ/P,by positivity,?_⟩
  intro i r hr hsr X hX
  have hR := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hRs : norm r^(2*σ)*norm r^ε=norm r^(ε+2*σ) := by
    rw [←Real.rpow_add hR]
    congr 1
    ring
  have hbound := metaplecticDualTerm_tsum_norm_bound hr ℓ (W i) hσ
    (div_pos hX (by norm_num : (0:ℝ)<729)) hC (hTr i)
    (hMass r hr hsr).1 (hMass r hr hsr).2
  rw [cubicTheta_completed_voronoi hr hsr hℓ (W i) (hW.compact i)
    (hW.positive i) (hW.smooth i) hσ hX,norm_mul,norm_mul,
    norm_metaplecticPrefactor (primary_ne_zero hr),Complex.norm_ofNat]
  calc
    _ ≤ (81*(Real.sqrt (norm r)/P))*
        ((C*((2*Real.pi)^(-4*σ)*(X/729)^(-σ)*norm r^(2*σ)))*(M*norm r^ε)*S) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = (81*C*M*S*(2*Real.pi)^(-4*σ)*(729:ℝ)^σ/P)*Real.sqrt (norm r)*
        (norm r^(2*σ)*norm r^ε)*X^(-σ) := by rw [cubicTheta_dilated_power hX]; ring
    _ = _ := by rw [hRs]

theorem uniform_cubicTheta_completed_subpower
    {ι : Type*} {W : ι→ℝ→ℂ} (hW : UniformLogWeights W)
    {ℓ : ℤ} (hℓ : ℓ≠0) {ε B : ℝ} (hε : 0<ε) (hB : 0≤B) :
    ∃ K : ℝ, 0≤K ∧ ∀ i r, primary r → Squarefree r →
      ∀ Y X : ℝ, 1≤Y → 0<X → norm r≤Y^B → Y^(-B)≤X →
        ‖metaplecticCompleted r ℓ (W i) X‖≤K*Y^ε*Real.sqrt (norm r) := by
  let δ := ε/(4*(B+1))
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hδε : 4*B*δ≤ε := by
    have hh : δ*(4*(B+1))=ε := by dsimp [δ]; field_simp
    nlinarith
  obtain ⟨K,hK,hbound⟩ := uniform_cubicTheta_completed_low hW hℓ hδ hδ
  refine ⟨K,hK,?_⟩
  intro i r hr hsr Y X hY hX hRY hYX
  have hs := metaplectic_low_scale_power hY (norm_pos_of_ne_zero (primary_ne_zero hr)) hX hB hδ hRY hYX
  have he : δ+2*δ=3*δ := by ring
  have hpow := Real.rpow_le_rpow_of_exponent_le hY hδε
  calc
    _ ≤ K*Real.sqrt (norm r)*norm r^(3*δ)*X^(-δ) := by simpa only [he] using hbound i r hr hsr X hX
    _ = (K*Real.sqrt (norm r))*(norm r^(3*δ)*X^(-δ)) := by ring
    _ ≤ (K*Real.sqrt (norm r))*Y^(4*B*δ) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ ≤ (K*Real.sqrt (norm r))*Y^ε := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
