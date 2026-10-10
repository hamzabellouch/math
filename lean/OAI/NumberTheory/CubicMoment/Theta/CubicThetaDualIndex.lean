import OAI.NumberTheory.CubicMoment.Theta.CubicThetaDualFrequency

namespace OAI

/-! The full dual sum of the concrete core coefficient, with summability
transferred from the proved arithmetic free-cube parametrization. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaDualTerm_support (r : Eisenstein) (ℓ : ℤ)
    (W : ℝ→ℂ) (σ X : ℝ) :
    Function.support (metaplecticDualTerm cubicThetaCoreCoefficient r ℓ W σ X) ⊆
      Set.range (cubicThetaCoreFreeArgument r) := by
  intro nd hnd
  have hd : IsCoprime (nd.2:Eisenstein) r := by
    by_contra h
    exact hnd (by simp only [metaplecticDualTerm,ite_eq_right h])
  have hn : CubicThetaCoreSupport r nd.1 := by
    by_contra h
    exact hnd (by simp only [metaplecticDualTerm,ite_eq_left hd,
      cubicThetaCoreCoefficient,ite_eq_right h,zero_mul,zero_div])
  obtain ⟨x,hx⟩ := (cubicThetaCoreArgument_range r nd.1).mpr hn
  exact ⟨(x,⟨nd.2,hd⟩),Prod.ext hx rfl⟩

lemma cubicThetaDualTerm_tsum (r : Eisenstein) (ℓ : ℤ)
    (W : ℝ→ℂ) (σ X : ℝ) :
    (∑' x : CubicThetaCoreIndex r × CubicThetaFreeArgument r,
      metaplecticDualTerm cubicThetaCoreCoefficient r ℓ W σ X (cubicThetaCoreFreeArgument r x))=
    ∑' nd,metaplecticDualTerm cubicThetaCoreCoefficient r ℓ W σ X nd :=
  (cubicThetaCoreFreeArgument_injective r).tsum_eq (cubicThetaDualTerm_support r ℓ W σ X)

lemma cubicThetaDualTerm_summable_iff (r : Eisenstein) (ℓ : ℤ)
    (W : ℝ→ℂ) (σ X : ℝ) :
    Summable (fun x : CubicThetaCoreIndex r × CubicThetaFreeArgument r =>
      metaplecticDualTerm cubicThetaCoreCoefficient r ℓ W σ X (cubicThetaCoreFreeArgument r x)) ↔
    Summable (metaplecticDualTerm cubicThetaCoreCoefficient r ℓ W σ X) :=
  (cubicThetaCoreFreeArgument_injective r).summable_iff
    (f:=metaplecticDualTerm cubicThetaCoreCoefficient r ℓ W σ X) (by
    intro nd hn
    by_contra hne
    exact hn (cubicThetaDualTerm_support r ℓ W σ X hne))

theorem cubicThetaFullDual_voronoi {r : Eisenstein} (hr : primary r) (hs : Squarefree r)
    [Fintype (Residues r)] (rev : Bool) {k : ℕ} (hk : 0<k)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {σ X : ℝ} (hσ : 0<σ) (hX : 0<X) :
    Summable (metaplecticDualTerm cubicThetaCoreCoefficient r (cubicThetaCircleOrder (!rev) k)
      W σ (X/729)) ∧
    ((((3^(5/2:ℝ):ℝ):ℂ)*theta (cubicThetaCircleOrder (!rev) k) lambdaE)*
      ((Real.sqrt (norm r):ℂ)*gauss r))*
        metaplecticRawCompleted r (cubicThetaCircleOrder (!rev) k) W X=
    ((cubicThetaLevelAngularRoot r rev k)⁻¹*cubicThetaDualPrefactor r*
      (27*theta (cubicThetaCircleOrder rev k) lambdaE))*
        ∑' nd,metaplecticDualTerm cubicThetaCoreCoefficient r (cubicThetaCircleOrder (!rev) k)
          W σ (X/729) nd := by
  obtain ⟨hS,hE⟩ := cubicThetaFree_voronoi hr hs rev hk W hW hpos hsm hσ hX
  have hfactor : (27:ℂ)*theta (cubicThetaCircleOrder rev k) lambdaE≠0 :=
    mul_ne_zero (by norm_num) (norm_ne_zero_iff.mp (by
      rw [norm_theta (show lambdaE≠0 by
        intro h
        exact traceLambda_ne_zero (by simpa only [lambdaE_coe,ZeroMemClass.coe_zero] using congrArg (fun z : Eisenstein => (z:ℂ)) h))]
      norm_num))
  have he := cubicThetaFreeLocalDualTerm_frequency hr rev k W σ X
  have hSc := hS.congr he
  have hSr := (summable_mul_left_iff hfactor).mp hSc
  refine ⟨(cubicThetaDualTerm_summable_iff r _ W σ (X/729)).mp hSr,?_⟩
  rw [show (∑' x,cubicThetaFreeLocalDualTerm r rev k W σ X x)=
    (27*theta (cubicThetaCircleOrder rev k) lambdaE)*
      ∑' x : CubicThetaCoreIndex r × CubicThetaFreeArgument r,
        metaplecticDualTerm cubicThetaCoreCoefficient r (cubicThetaCircleOrder (!rev) k)
          W σ (X/729) (cubicThetaCoreFreeArgument r x) by
    simp only [he,tsum_mul_left],cubicThetaDualTerm_tsum] at hE
  simpa only [mul_assoc] using hE

end CubicFirstMoment

end

end OAI
