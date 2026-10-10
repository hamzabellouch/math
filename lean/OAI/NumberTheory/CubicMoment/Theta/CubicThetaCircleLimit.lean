import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCircleUniform

namespace OAI

/-! Angular extraction survives continuous changes of height and direction. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

local instance : Fact (0<(1:ℝ)) := ⟨by norm_num⟩

theorem cubicThetaCircleActual_limit {a : Eisenstein→ℂ} {C : ℝ} (hC : 0≤C)
    (ha : ∀ n : Eisenstein,n≠0 → ‖a n‖≤C*norm n) (z : ℂ) (rev : Bool) (k : ℕ)
    {d : ℝ→ℂ} {v : ℝ→ℝ} {d₀ : ℂ} {v₀ : ℝ}
    (hd : Tendsto d (𝓝[Set.Ioi 0] 0) (𝓝 d₀))
    (hv : Tendsto v (𝓝[Set.Ioi 0] 0) (𝓝 v₀)) (hv₀ : 0<v₀) :
    Tendsto (fun r : ℝ => fourierCoeff
      (fun t => cubicThetaNonconstant a (z+cubicThetaSignedCircle rev (d r) r t,v r))
        (k:ℤ)/(r:ℂ)^k) (𝓝[Set.Ioi 0] 0)
      (𝓝 (((2*Real.pi*Complex.I)^k/(k.factorial:ℂ))*(cubicThetaCircleMultiplier rev d₀)^k*
        cubicThetaNonconstant (cubicThetaAngularCoefficient a (cubicThetaCircleOrder rev k)) (z,v₀))) := by
  let g := fun r : ℝ => ((2*Real.pi*Complex.I)^k/(k.factorial:ℂ))*
    (cubicThetaCircleMultiplier rev (d r))^k*
      cubicThetaNonconstant (cubicThetaAngularCoefficient a (cubicThetaCircleOrder rev k)) (z,v r)
  have hdM : Tendsto (fun r => cubicThetaCircleMultiplier rev (d r))
      (𝓝[Set.Ioi 0] 0) (𝓝 (cubicThetaCircleMultiplier rev d₀)) := by
    cases rev
    · exact hd
    · exact hd.star
  have hF := (cubicThetaAngular_continuousAt hC ha (cubicThetaCircleOrder rev k)
    (p := (z,v₀)) hv₀).tendsto.comp (tendsto_const_nhds.prodMk_nhds hv)
  have hg : Tendsto g (𝓝[Set.Ioi 0] 0)
      (𝓝 (((2*Real.pi*Complex.I)^k/(k.factorial:ℂ))*(cubicThetaCircleMultiplier rev d₀)^k*
        cubicThetaNonconstant (cubicThetaAngularCoefficient a (cubicThetaCircleOrder rev k)) (z,v₀))) :=
    (tendsto_const_nhds.mul (hdM.pow k)).mul hF
  obtain ⟨K,hK,hbound⟩ := cubicThetaCircleActual_uniform hC ha
    (show 0<v₀/2 by positivity) (show 0≤‖d₀‖+1 by positivity) rev k
  have hb : ∀ᶠ r : ℝ in 𝓝[Set.Ioi 0] 0,
      ‖fourierCoeff
        (fun t => cubicThetaNonconstant a (z+cubicThetaSignedCircle rev (d r) r t,v r))
          (k:ℤ)/(r:ℂ)^k-g r‖≤K*r := by
    filter_upwards [hv.eventually (lt_mem_nhds (by linarith : v₀/2<v₀)),
      hd.norm.eventually (gt_mem_nhds (lt_add_one ‖d₀‖)),self_mem_nhdsWithin] with r hvr hdr hr
    exact hbound z (d r) (v r) r hvr hdr.le hr
  have he : Tendsto (fun r : ℝ => fourierCoeff
      (fun t => cubicThetaNonconstant a (z+cubicThetaSignedCircle rev (d r) r t,v r))
        (k:ℤ)/(r:ℂ)^k-g r) (𝓝[Set.Ioi 0] 0) (𝓝 0) := by
    apply squeeze_zero_norm' hb
    simpa using (tendsto_const_nhds.mul (tendsto_id.mono_left nhdsWithin_le_nhds) :
      Tendsto (fun r : ℝ => K*r) (𝓝[Set.Ioi 0] 0) (𝓝 (K*0)))
  simpa only [zero_add,sub_add_cancel] using he.add hg

end CubicFirstMoment

end

end OAI
