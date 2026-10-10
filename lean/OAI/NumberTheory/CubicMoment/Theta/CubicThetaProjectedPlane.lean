import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimaryBruhat
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCirclePlane

namespace OAI

/-! The actual projected cusp expansion supports the same angular
extraction as the original theta series, with its own literal coefficients. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology MatrixGroups
namespace CubicFirstMoment

local instance : Fact (0<(1:ℝ)) := ⟨by norm_num⟩

lemma cubicThetaProjectedCoefficient_arithmetic_bound (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (n : Eisenstein) (hn : n≠0) :
    ‖cubicThetaProjectedCoefficient g hc n‖≤243*norm n :=
  (cubicThetaProjectedCoefficient_bound g hc n).trans
    (le_mul_of_one_le_right (by norm_num) (one_le_norm hn))

def cubicThetaProjectedPlane (g : SL(2,Eisenstein)) (hc : primary (g 1 0))
    (p : ℂ×ℝ) : ℂ :=
  cubicThetaProjectedConstant g hc*((p.2^(2/3:ℝ):ℝ):ℂ)+
    cubicThetaNonconstant (cubicThetaProjectedCoefficient g hc) p

def cubicThetaPrimaryCuspCenter (g : SL(2,Eisenstein)) : ℂ := (g 0 0:ℂ)/(g 1 0:ℂ)

def cubicThetaPrimaryDualCenter (g : SL(2,Eisenstein)) : ℂ :=
  (g 1 1:ℂ)-(g 1 1:ℂ)/(g 1 0:ℂ)

lemma cubicThetaSelected_projected_plane (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (z : ℂ) {v : ℝ} (hv : 0<v) :
    cubicThetaNonconstant cubicThetaSelectedCoefficient
      ((cubicThetaInversion (g 1 0:ℂ) (z,v)).1+cubicThetaPrimaryCuspCenter g,
        (cubicThetaInversion (g 1 0:ℂ) (z,v)).2)=
      cubicThetaProjectedPlane g hc (z+cubicThetaPrimaryDualCenter g,v) := by
  have he := cubicThetaSelected_primary_cusp g hc z hv
  have hz : z-(g 1 1:ℂ)/(g 1 0:ℂ)+(g 1 1:ℂ)=z+cubicThetaPrimaryDualCenter g := by
    unfold cubicThetaPrimaryDualCenter
    ring
  rw [hz] at he
  exact he

lemma cubicThetaProjectedPlane_circle_coefficient (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (z d : ℂ) {v : ℝ} (hv : 0<v)
    (r : ℝ) (rev : Bool) {k : ℕ} (hk : 0<k) :
    fourierCoeff (fun t => cubicThetaProjectedPlane g hc
      (z+cubicThetaSignedCircle rev d r t,v)) (k:ℤ)=
      fourierCoeff (fun t => cubicThetaNonconstant (cubicThetaProjectedCoefficient g hc)
        (z+cubicThetaSignedCircle rev d r t,v)) (k:ℤ) := by
  have hs := cubicThetaSeries_summable (by norm_num : (0:ℝ)≤243)
    (cubicThetaProjectedCoefficient_arithmetic_bound g hc) hv z
  have hf : Continuous (fun t => cubicThetaNonconstant (cubicThetaProjectedCoefficient g hc)
      (z+cubicThetaSignedCircle rev d r t,v)) := by
    rw [cubicThetaCircleActual_series]
    exact cubicThetaCircleSeries_continuous hs.norm r
  change fourierCoeff (fun t => cubicThetaProjectedConstant g hc*((v^(2/3:ℝ):ℝ):ℂ)+
    cubicThetaNonconstant (cubicThetaProjectedCoefficient g hc)
      (z+cubicThetaSignedCircle rev d r t,v)) (k:ℤ)=_
  exact cubicThetaCircle_coefficient_const_add _
    (hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (by exact_mod_cast hk.ne')

theorem cubicThetaProjectedPlane_circle_limit (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (z : ℂ) (rev : Bool) {k : ℕ} (hk : 0<k)
    {d : ℝ→ℂ} {v : ℝ→ℝ} {d₀ : ℂ} {v₀ : ℝ}
    (hd : Tendsto d (𝓝[Set.Ioi 0] 0) (𝓝 d₀))
    (hv : Tendsto v (𝓝[Set.Ioi 0] 0) (𝓝 v₀)) (hv₀ : 0<v₀) :
    Tendsto (fun r : ℝ => fourierCoeff
      (fun t => cubicThetaProjectedPlane g hc (z+cubicThetaSignedCircle rev (d r) r t,v r))
        (k:ℤ)/(r:ℂ)^k) (𝓝[Set.Ioi 0] 0)
      (𝓝 (((2*Real.pi*Complex.I)^k/(k.factorial:ℂ))*(cubicThetaCircleMultiplier rev d₀)^k*
        cubicThetaNonconstant
          (cubicThetaAngularCoefficient (cubicThetaProjectedCoefficient g hc)
            (cubicThetaCircleOrder rev k)) (z,v₀))) := by
  have H := cubicThetaCircleActual_limit (by norm_num : (0:ℝ)≤243)
    (cubicThetaProjectedCoefficient_arithmetic_bound g hc) z rev k hd hv hv₀
  apply H.congr'
  filter_upwards [hv.eventually (lt_mem_nhds hv₀)] with r hr
  rw [cubicThetaProjectedPlane_circle_coefficient g hc z (d r) hr r rev hk]

end CubicFirstMoment

end

end OAI
