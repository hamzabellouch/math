import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralOutgoingBoundary
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRobinPlane

namespace OAI

/-! A single sufficiently large radius gives the exact holomorphic outgoing
Robin condition throughout a neighborhood of a fixed spectral parameter. -/

open Filter Topology Set
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem spectralValueDet_analyticAt (U V : ℂ → E₄) (z : ℂ)
    (hU : AnalyticAt ℂ U z) (hV : AnalyticAt ℂ V z) :
    AnalyticAt ℂ (fun w => spectralValueDet (spectralPhysicalValueMap (U w))
      (spectralPhysicalValueMap (V w))) z := by
  have hu := (spectralPhysicalValueMap.analyticAt (U z)).comp hU
  have hv := (spectralPhysicalValueMap.analyticAt (V z)).comp hV
  have huf := ((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt _).comp hu
  have hus := ((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt _).comp hu
  have hvf := ((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt _).comp hv
  have hvs := ((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt _).comp hv
  exact (huf.mul hvs).sub (hus.mul hvf)

theorem spectralOutgoing_boundary_neighborhood
    (U V : ℂ → ℝ → E₄) (z : ℂ)
    (ha : ∀ w r, 1 ≤ r → AnalyticAt ℂ (fun lam => U lam r) w ∧
      AnalyticAt ℂ (fun lam => V lam r) w)
    (hd : ∀ᶠ r in atTop, spectralValueDet (spectralPhysicalValueMap (U z r))
      (spectralPhysicalValueMap (V z r)) ≠ 0) (R₀ : ℝ) :
    ∃ R : ℝ, R₀ ≤ R ∧ 1 ≤ R ∧ ∃ S : Set ℂ, IsOpen S ∧ z ∈ S ∧
      ∀ w ∈ S, AnalyticAt ℂ (fun lam => spectralJetRobin (U lam R) (V lam R)) w ∧
        ∀ W : E₄,
          spectralPhysicalDerivativeMap W=spectralJetRobin (U w R) (V w R)
            (spectralPhysicalValueMap W) ↔
          ∃ c : ℂ × ℂ, W=c.1 • U w R+c.2 • V w R := by
  obtain ⟨R,hR,h1,hdet⟩ := (eventually_ge_atTop R₀ |>.and
    ((eventually_ge_atTop 1).and hd)).exists
  have hc := (spectralValueDet_analyticAt (fun w => U w R) (fun w => V w R) z
    (ha z R h1).1 (ha z R h1).2).continuousAt
  have he : ∀ᶠ w in 𝓝 z, spectralValueDet (spectralPhysicalValueMap (U w R))
      (spectralPhysicalValueMap (V w R)) ≠ 0 :=
    hc.eventually (eventually_ne_nhds hdet)
  obtain ⟨S,hS,hopen,hz⟩ := mem_nhds_iff.mp he
  refine ⟨R,hR,h1,S,hopen,hz,?_⟩
  intro w hw
  have hwdet := hS hw
  exact ⟨spectralJetRobin_analyticAt _ _ w (ha w R h1).1 (ha w R h1).2 hwdet,
    fun W => spectralJetRobin_plane _ _ W hwdet⟩

theorem canonical_physical_robin_neighborhood (m : ℕ) (hm : 1 ≤ m)
    (b : ℝ) (c : ℂ) (hc : c ≠ 0) (η : ℂ) (L : ℝ)
    (hX : HasRadialExterior (-1/(m : ℂ)+2*Complex.I*(b : ℂ)) m c L)
    (z : ℂ) (R₀ : ℝ) :
    let μ := -1/(m : ℂ)+2*Complex.I*(b : ℂ)
    let Q := fun r => Complex.exp (μ*(Real.log r : ℂ))*
      (radialExteriorCanonical μ m c L (Real.log r)).1
    ∃ Vp Vm : ℂ → ℝ → E₄, ∃ R : ℝ, R₀ ≤ R ∧ 1 ≤ R ∧
      (∀ lam r, 1 ≤ r → HasDerivAt (Vp lam)
        (spectralPhysicalCircularField (μ-2*lam) (star μ-2*lam) η m (Q r) r (Vp lam r)) r) ∧
      (∀ lam r, 1 ≤ r → HasDerivAt (Vm lam)
        (spectralPhysicalCircularField (μ-2*lam) (star μ-2*lam) η m (Q r) r (Vm lam r)) r) ∧
      ∃ S : Set ℂ, IsOpen S ∧ z ∈ S ∧ ∀ w ∈ S,
        AnalyticAt ℂ (fun lam => spectralJetRobin (Vp lam R) (Vm lam R)) w ∧
        ∀ W : E₄,
          spectralPhysicalDerivativeMap W=spectralJetRobin (Vp w R) (Vm w R)
            (spectralPhysicalValueMap W) ↔
          ∃ c : ℂ × ℂ, W=c.1 • Vp w R+c.2 • Vm w R := by
  intro μ Q
  obtain ⟨Vp,Vm,hp,hn,ha,hd⟩ := canonical_physical_boundary_basis m hm b c hc η L hX
  obtain ⟨R,hR,h1,S,ho,hz,hS⟩ := spectralOutgoing_boundary_neighborhood Vp Vm z ha (hd z) R₀
  exact ⟨Vp,Vm,R,hR,h1,hp,hn,S,ho,hz,hS⟩

end DefocusingNLS

end OAI
