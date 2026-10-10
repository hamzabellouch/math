import OAI.NumberTheory.CubicMoment.Theta.CubicThetaDualIndex
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaDualScalar

namespace OAI

/-! The proved nonzero-angular raw formula, with the full dual index set
and the actual fixed scale. This is not an assertion of the differently
normalized published input. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma cubicTheta_nonzero_order {ℓ : ℤ} (hℓ : ℓ≠0) :
    ∃ (rev : Bool) (k : ℕ), 0<k ∧ cubicThetaCircleOrder (!rev) k=ℓ := by
  cases ℓ with
  | ofNat n =>
    refine ⟨true,n,Nat.pos_of_ne_zero (fun hn => hℓ (by simp [hn])),?_⟩
    simp [cubicThetaCircleOrder]
  | negSucc n =>
    refine ⟨false,n+1,by omega,?_⟩
    simp only [Bool.not_false,cubicThetaCircleOrder,ite_true,Nat.cast_add,Nat.cast_one]
    omega

theorem cubicTheta_raw_voronoi {r : Eisenstein} (hr : primary r) (hs : Squarefree r)
    [Fintype (Residues r)] {ℓ : ℤ} (hℓ : ℓ≠0)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {σ X : ℝ} (hσ : 0<σ) (hX : 0<X) :
    Summable (metaplecticDualTerm cubicThetaCoreCoefficient r ℓ W σ (X/729)) ∧
    metaplecticRawCompleted r ℓ W X=
      81*metaplecticRawPrefactor r ℓ*
        ∑' nd,metaplecticDualTerm cubicThetaCoreCoefficient r ℓ W σ (X/729) nd := by
  obtain ⟨rev,k,hk,rfl⟩ := cubicTheta_nonzero_order hℓ
  obtain ⟨hS,hE⟩ := cubicThetaFullDual_voronoi hr hs rev hk W hW hpos hsm hσ hX
  refine ⟨hS,?_⟩
  let A := (((3^(5/2:ℝ):ℝ):ℂ)*theta (cubicThetaCircleOrder (!rev) k) lambdaE)*
      ((Real.sqrt (norm r):ℂ)*gauss r)
  have hA : A≠0 := by
    dsimp only [A]
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (by norm_num) _).ne'
      · rw [cubicTheta_theta_lambda]
        exact zpow_ne_zero _ Complex.I_ne_zero
    · apply mul_ne_zero
      · exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr
          (norm_pos_of_ne_zero (primary_ne_zero hr))).ne'
      · apply norm_ne_zero_iff.mp
        rw [norm_gauss_of_squarefree hr hs]
        norm_num
  apply mul_left_cancel₀ hA
  calc
    _ = _ := hE
    _ = _ := by rw [←cubicThetaDual_scalar hr hs rev k]; ring

theorem cubicTheta_completed_voronoi {r : Eisenstein} (hr : primary r) (hs : Squarefree r)
    {ℓ : ℤ} (hℓ : ℓ≠0)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {σ X : ℝ} (hσ : 0<σ) (hX : 0<X) :
    metaplecticCompleted r ℓ W X=
      81*metaplecticPrefactor r ℓ*
        ∑' nd,metaplecticDualTerm cubicThetaCoreCoefficient r ℓ W σ (X/729) nd := by
  let : Finite (Residues r) := finite_residues (primary_ne_zero hr)
  let : Fintype (Residues r) := Fintype.ofFinite _
  rw [metaplecticCompleted_eq_raw hr,(cubicTheta_raw_voronoi hr hs hℓ W hW hpos hsm hσ hX).2]
  calc
    _ = 81*(gauss r*theta ℓ r*metaplecticRawPrefactor r ℓ)*
        ∑' nd,metaplecticDualTerm cubicThetaCoreCoefficient r ℓ W σ (X/729) nd := by ring
    _ = _ := by rw [metaplecticPrefactor_normalization hr hs]

end CubicFirstMoment

end

end OAI
