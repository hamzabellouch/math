import OAI.NumberTheory.CubicMoment.Transform.MetaplecticCoefficientMass
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticTransformBounds

namespace OAI

/-! Exact scaling of the actual angular Voronoi terms. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma norm_complexAngular {z : ℂ} (hz : z ≠ 0) (ℓ : ℤ) : ‖complexAngular ℓ z‖ = 1 := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  simp [complexAngular,norm_zpow,hn]

lemma metaplectic_argument_power {B D P R X : ℝ}
    (hB : 0 < B) (hD : 0 < D) (hP : 0 < P) (hR : 0 < R) (hX : 0 < X) (σ : ℝ) :
    ((B^4*D^3*P*X)/R^2)^(-σ) =
      B^(-4*σ)*D^(-3*σ)*P^(-σ)*X^(-σ)*R^(2*σ) := by
  have hb : (B^4)^(-σ) = B^(-4*σ) := by
    rw [←Real.rpow_natCast_mul hB.le]
    congr 1
    norm_num
  have hd : (D^3)^(-σ) = D^(-3*σ) := by
    rw [←Real.rpow_natCast_mul hD.le]
    congr 1
    norm_num
  have hr : (R^2)^(-σ) = (R^(2*σ))⁻¹ := by
    rw [←Real.rpow_natCast_mul hR.le,←Real.rpow_neg hR.le]
    congr 1
    norm_num
  rw [Real.div_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) hX.le,
    Real.mul_rpow (by positivity) hP.le,
    Real.mul_rpow (by positivity) (pow_nonneg hD.le _),hb,hd,hr,
    div_eq_mul_inv,inv_inv]

lemma metaplectic_dual_scalar {A B D P R X : ℝ}
    (hB : 0 < B) (hD : 0 < D) (hP : 0 < P) (hR : 0 < R) (hX : 0 < X) (σ : ℝ) :
    A/(P*D^(5/2:ℝ))*((B^4*D^3*P*X)/R^2)^(-σ) =
      (B^(-4*σ)*X^(-σ)*R^(2*σ))*(A/P^(1+σ))*D^(-5/2-3*σ) := by
  have hp : P^(-σ)/P = (P^(1+σ))⁻¹ := by
    calc
      _ = P^(-σ)/P^(1:ℝ) := by rw [Real.rpow_one]
      _ = P^(-σ-1) := (Real.rpow_sub hP _ _).symm
      _ = P^(-(1+σ)) := by congr 1; ring
      _ = _ := Real.rpow_neg hP.le _
  have hd : D^(-3*σ)/D^(5/2:ℝ) = D^(-5/2-3*σ) := by
    rw [←Real.rpow_sub hD]
    congr 1
    ring
  rw [metaplectic_argument_power hB hD hP hR hX]
  calc
    _ = (B^(-4*σ)*X^(-σ)*R^(2*σ))*A*(P^(-σ)/P)*(D^(-3*σ)/D^(5/2:ℝ)) := by ring
    _ = _ := by rw [hp,hd]; ring

/-- The actual dual term has the separated coefficient/d-variable
majorant supplied by the published formula and the derived transform bound. -/
lemma metaplecticDualTerm_norm_le
    (a : Eisenstein → MetaplecticDualArgument → ℂ) {r : Eisenstein} (hr : primary r)
    (ℓ : ℤ) (W : ℝ → ℂ) {σ X C : ℝ} (hX : 0 < X) (hC : 0 ≤ C)
    (hW : ∀ v : ℝ, 0 < v → ‖metaplecticTransform ℓ W σ v‖ ≤ C*v^(-σ))
    (nd : MetaplecticDualArgument × PrimaryArgument) :
    ‖metaplecticDualTerm a r ℓ W σ X nd‖ ≤
      (C*((2*Real.pi)^(-4*σ)*X^(-σ)*norm r^(2*σ)))*
        metaplecticCoefficientMassTerm a r σ nd.1*norm nd.2^(-5/2-3*σ) := by
  have hR : 0 < norm r := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hD : 0 < norm nd.2 := norm_pos_of_ne_zero (primary_ne_zero nd.2.property)
  have hP : 0 < Complex.normSq (metaplecticFrequency nd.1) :=
    Complex.normSq_pos.mpr (metaplecticFrequency_ne_zero nd.1)
  have hB : 0 < 2*Real.pi := by positivity
  have hz : ((nd.2:Eisenstein)^3:ℂ)*metaplecticFrequency nd.1 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (fun h => primary_ne_zero nd.2.property (Subtype.ext h)))
      (metaplecticFrequency_ne_zero nd.1)
  have hnorm : Complex.normSq (((nd.2:Eisenstein)^3:ℂ)*metaplecticFrequency nd.1) =
      norm nd.2^3*Complex.normSq (metaplecticFrequency nd.1) := by
    rw [Complex.normSq_mul,map_pow]
    rfl
  unfold metaplecticDualTerm
  split_ifs
  · rw [norm_mul,norm_mul,norm_div,Complex.norm_real,
      Real.norm_of_nonneg (by positivity),norm_complexAngular hz,mul_one,hnorm]
    have hv : 0 < (2*Real.pi)^4*(norm nd.2^3*Complex.normSq (metaplecticFrequency nd.1))*X/norm r^2 := by
      positivity
    apply (mul_le_mul_of_nonneg_left (hW _ hv) (by positivity)).trans_eq
    rw [mul_left_comm _ C,mul_assoc]
    have hs := metaplectic_dual_scalar (A := ‖a r nd.1*metaplecticLocalCoefficient r nd.1‖)
      hB hD hP hR hX σ
    change C*(_/(_*_) * _^(-σ)) = _
    rw [show (2*Real.pi)^4*(norm nd.2^3*Complex.normSq (metaplecticFrequency nd.1)*X)/norm r^2 =
      ((2*Real.pi)^4*norm nd.2^3*Complex.normSq (metaplecticFrequency nd.1)*X)/norm r^2 by ring,hs]
    unfold metaplecticCoefficientMassTerm
    ring
  · rw [norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC (by positivity))
      (metaplecticCoefficientMassTerm_nonneg a r σ nd.1)) (Real.rpow_nonneg hD.le _)

end CubicFirstMoment

end

end OAI
