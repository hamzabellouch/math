import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRobinPlane

namespace OAI

/-! Convergence of normalized column values and derivatives passes through
the physical scaling and the exact outgoing Robin matrix. -/

open Filter Topology
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem spectralPhysicalJet_tendsto (ν : ℕ → ℂ) (ν₀ : ℂ)
    (Y : ℕ → ℝ → ℂ × ℂ) (Y₀ : ℝ → ℂ × ℂ) (r : ℝ)
    (hν : Tendsto ν atTop (𝓝 ν₀))
    (hY : Tendsto (fun n => Y n (Real.log r)) atTop (𝓝 (Y₀ (Real.log r)))) :
    Tendsto (fun n => spectralPhysicalJet (ν n) (Y n) r) atTop
      (𝓝 (spectralPhysicalJet ν₀ Y₀ r)) := by
  have he := Complex.continuous_exp.continuousAt.tendsto.comp
    (hν.mul_const (Real.log r : ℂ))
  exact (he.mul hY.fst_nhds).prodMk_nhds
    ((he.div_const (r : ℂ)).mul ((hν.mul hY.fst_nhds).add hY.snd_nhds))

theorem spectralPhysicalPair_tendsto (νp νm : ℕ → ℂ) (νp₀ νm₀ : ℂ)
    (Y : ℕ → ℝ → E₄) (Y₀ : ℝ → E₄) (r : ℝ)
    (hp : Tendsto νp atTop (𝓝 νp₀)) (hm : Tendsto νm atTop (𝓝 νm₀))
    (hY : Tendsto (fun n => Y n (Real.log r)) atTop (𝓝 (Y₀ (Real.log r)))) :
    Tendsto (fun n => spectralPhysicalPair (νp n) (νm n) (Y n) r) atTop
      (𝓝 (spectralPhysicalPair νp₀ νm₀ Y₀ r)) := by
  exact (spectralPhysicalJet_tendsto νp νp₀ _ _ r hp hY.fst_nhds).prodMk_nhds
    (spectralPhysicalJet_tendsto νm νm₀ _ _ r hm hY.snd_nhds)

theorem spectralJetRobin_tendsto (U V : ℕ → E₄) (U₀ V₀ : E₄)
    (hU : Tendsto U atTop (𝓝 U₀)) (hV : Tendsto V atTop (𝓝 V₀))
    (hd : spectralValueDet (spectralPhysicalValueMap U₀) (spectralPhysicalValueMap V₀) ≠ 0) :
    Tendsto (fun n => spectralJetRobin (U n) (V n)) atTop (𝓝 (spectralJetRobin U₀ V₀)) := by
  exact spectralRobinOperator_tendsto _ _ _ _ _ _ _ _
    (spectralPhysicalValueMap.continuous.continuousAt.tendsto.comp hU)
    (spectralPhysicalValueMap.continuous.continuousAt.tendsto.comp hV)
    (spectralPhysicalDerivativeMap.continuous.continuousAt.tendsto.comp hU)
    (spectralPhysicalDerivativeMap.continuous.continuousAt.tendsto.comp hV) hd

theorem spectralPhysicalRobin_tendsto (νp νm : ℕ → ℂ) (νp₀ νm₀ : ℂ)
    (Y Z : ℕ → ℝ → E₄) (Y₀ Z₀ : ℝ → E₄) (r : ℝ)
    (hp : Tendsto νp atTop (𝓝 νp₀)) (hm : Tendsto νm atTop (𝓝 νm₀))
    (hY : Tendsto (fun n => Y n (Real.log r)) atTop (𝓝 (Y₀ (Real.log r))))
    (hZ : Tendsto (fun n => Z n (Real.log r)) atTop (𝓝 (Z₀ (Real.log r))))
    (hd : spectralValueDet
      (spectralPhysicalValueMap (spectralPhysicalPair νp₀ νm₀ Y₀ r))
      (spectralPhysicalValueMap (spectralPhysicalPair νp₀ νm₀ Z₀ r)) ≠ 0) :
    Tendsto (fun n => spectralJetRobin
      (spectralPhysicalPair (νp n) (νm n) (Y n) r)
      (spectralPhysicalPair (νp n) (νm n) (Z n) r)) atTop
      (𝓝 (spectralJetRobin (spectralPhysicalPair νp₀ νm₀ Y₀ r)
        (spectralPhysicalPair νp₀ νm₀ Z₀ r))) :=
  spectralJetRobin_tendsto _ _ _ _ (spectralPhysicalPair_tendsto νp νm νp₀ νm₀ Y Y₀ r hp hm hY)
    (spectralPhysicalPair_tendsto νp νm νp₀ νm₀ Z Z₀ r hp hm hZ) hd

end DefocusingNLS

end OAI
