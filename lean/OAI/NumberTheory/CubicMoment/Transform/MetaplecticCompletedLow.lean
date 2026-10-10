import OAI.NumberTheory.CubicMoment.Transform.MetaplecticDualScaling

namespace OAI

/-! The low-height completed angular estimate, derived from the actual
published Voronoi identity, coefficient support, and Gamma strip bound. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CubicFirstMoment

private lemma norm_tsum_le_separated {α β : Type*}
    (f : α × β → ℂ) (u : α → ℝ) (v : β → ℝ) {K M : ℝ}
    (hu : Summable u) (hv : Summable v)
    (hu0 : ∀ a, 0 ≤ u a) (hv0 : ∀ b, 0 ≤ v b) (hK : 0 ≤ K)
    (hM : (∑' a, u a) ≤ M)
    (hpoint : ∀ z, ‖f z‖ ≤ K*(u z.1*v z.2)) :
    ‖∑' z, f z‖ ≤ K*M*(∑' b, v b) := by
  have hp : Summable (fun z : α × β => u z.1*v z.2) :=
    hu.mul_of_nonneg hv hu0 hv0
  have hs : HasSum (fun z : α × β => K*(u z.1*v z.2))
      (K*((∑' a, u a)*(∑' b, v b))) :=
    (hu.hasSum.mul hv.hasSum hp).mul_left K
  have hb : ‖∑' z, f z‖ ≤ K*((∑' a, u a)*(∑' b, v b)) :=
    tsum_of_norm_bounded hs hpoint
  calc
    _ ≤ K*((∑' a, u a)*(∑' b, v b)) := hb
    _ ≤ K*(M*(∑' b, v b)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hM (tsum_nonneg hv0)) hK
    _ = _ := by ring

private lemma metaplectic_d_weight_summable {σ : ℝ} (hσ : 0 < σ) :
    Summable (fun d : PrimaryArgument => norm d^(-5/2-3*σ)) := by
  convert primary_norm_rpow_summable (show 1 < 5/2+3*σ by linarith) using 1
  ext d
  congr 1
  ring

lemma metaplecticDualTerm_tsum_norm_bound
    {a : Eisenstein → MetaplecticDualArgument → ℂ} {r : Eisenstein}
    (hr : primary r) (ℓ : ℤ) (W : ℝ → ℂ) {σ X C M : ℝ}
    (hσ : 0 < σ) (hX : 0 < X) (hC : 0 ≤ C)
    (hW : ∀ v : ℝ, 0 < v → ‖metaplecticTransform ℓ W σ v‖ ≤ C*v^(-σ))
    (hm : Summable (metaplecticCoefficientMassTerm a r σ))
    (hM : (∑' n, metaplecticCoefficientMassTerm a r σ n) ≤ M) :
    ‖∑' nd : MetaplecticDualArgument × PrimaryArgument, metaplecticDualTerm a r ℓ W σ X nd‖ ≤
      (C*((2*Real.pi)^(-4*σ)*X^(-σ)*norm r^(2*σ)))*M*
        (∑' d : PrimaryArgument, norm d^(-5/2-3*σ)) := by
  apply norm_tsum_le_separated _ (metaplecticCoefficientMassTerm a r σ)
    (fun d : PrimaryArgument => norm d^(-5/2-3*σ)) hm
    (metaplectic_d_weight_summable hσ) (metaplecticCoefficientMassTerm_nonneg a r σ)
    (fun d => Real.rpow_nonneg (norm_nonneg d) _)
    (mul_nonneg hC (mul_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_nonneg hX.le _)) (Real.rpow_nonneg (norm_nonneg r) _))) hM
  intro nd
  simpa only [mul_assoc] using metaplecticDualTerm_norm_le a hr ℓ W hX hC hW nd

/-- All constants are chosen before the weight index, level and scale.
This is the explicit form before absorbing the arbitrarily small powers. -/
theorem uniform_metaplectic_completed_low
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {ι : Type*} {W : ι → ℝ → ℂ} (hW : UniformLogWeights W)
    (ℓ : ℤ) {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) (hσs : σ < 1/10000)
    (hGamma : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ) (-σ-1/6)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i r, primary r → Squarefree r → ∀ X : ℝ, 0 < X →
      ‖metaplecticCompleted r ℓ (W i) X-metaplecticMain r ℓ (W i) X‖ ≤
        K*Real.sqrt (norm r)*norm r^(ε+2*σ)*X^(-σ) := by
  obtain ⟨C,hC,hTr⟩ := hW.metaplecticTransform_bound ℓ hσ hGamma
  obtain ⟨M,hM,hMass⟩ := metaplectic_coefficient_mass_small_power hV.1 hε hσ
  let S : ℝ := ∑' d : PrimaryArgument, norm d^(-5/2-3*σ)
  have hS : 0 ≤ S := tsum_nonneg (fun d => Real.rpow_nonneg (norm_nonneg d) _)
  let P : ℝ := 3^(7/2:ℝ)*(2*Real.pi)^2
  have hP : 0 < P := by dsimp [P]; positivity
  refine ⟨C*M*S*(2*Real.pi)^(-4*σ)/P,by positivity,?_⟩
  intro i r hr hsr X hX
  have hR := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hRs : norm r^(2*σ)*norm r^ε = norm r^(ε+2*σ) := by
    rw [←Real.rpow_add hR]
    congr 1
    ring
  have hbound := metaplecticDualTerm_tsum_norm_bound hr ℓ (W i) hσ hX hC (hTr i)
    (hMass r hr hsr).1 (hMass r hr hsr).2
  rw [metaplectic_angular_voronoi hV hr hsr ℓ (W i) (hW.compact i)
    (hW.positive i) (hW.smooth i) (X := X) (σ := σ) hX hσ hσs,
    add_sub_cancel_left,norm_mul,norm_metaplecticPrefactor (primary_ne_zero hr)]
  calc
    _ ≤ (Real.sqrt (norm r)/P)*
        ((C*((2*Real.pi)^(-4*σ)*X^(-σ)*norm r^(2*σ)))*(M*norm r^ε)*S) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = (C*M*S*(2*Real.pi)^(-4*σ)/P)*Real.sqrt (norm r)*
        (norm r^(2*σ)*norm r^ε)*X^(-σ) := by ring
    _ = _ := by rw [hRs]

end CubicFirstMoment

end

end OAI
