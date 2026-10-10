import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHolomorphicSingularLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalRobinLimit

namespace OAI

/-! A common physical radius supports convergent Robin matrices from the
actual holomorphic outgoing columns along any convergent spectral sequence. -/

open Filter Topology Set
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem exists_canonical_holomorphic_robin_limit
    (ν m lam : ℕ → ℂ) (ν₀ m₀ lam₀ η : ℂ)
    (hν : Tendsto ν atTop (𝓝 ν₀)) (hm : Tendsto m atTop (𝓝 m₀))
    (hlam : Tendsto lam atTop (𝓝 lam₀)) (hm₀ : m₀ ≠ 0)
    (δ L R₀ : ℝ) (hδ : 0 < δ) (hsmall : ‖m₀‖+2*δ < 1)
    (hX : ∀ᶠ n in atTop, HasRadialExterior (ν n) n (m n) L) :
    ∃ R : ℝ, R₀ ≤ R ∧ 1 ≤ R ∧
      ∃ Y Z : ℕ → ℂ → ℝ → E₄, ∃ Y₀ Z₀ : ℝ → E₄,
        (∀ᶠ n in atTop,
          IsCanonicalHolomorphicColumn (ν n) η (m n) n L (1,0) (Y n) ∧
          IsCanonicalHolomorphicColumn (ν n) η (m n) n L (0,1) (Z n)) ∧
        let U := fun n z => spectralPhysicalPair (ν n-2*z) (star (ν n)-2*z) (Y n z) R
        let V := fun n z => spectralPhysicalPair (ν n-2*z) (star (ν n)-2*z) (Z n z) R
        let U₀ := spectralPhysicalPair (ν₀-2*lam₀) (star ν₀-2*lam₀) Y₀ R
        let V₀ := spectralPhysicalPair (ν₀-2*lam₀) (star ν₀-2*lam₀) Z₀ R
        Tendsto (fun n => spectralJetRobin (U n (lam n)) (V n (lam n))) atTop
          (𝓝 (spectralJetRobin U₀ V₀)) ∧
        spectralValueDet (spectralPhysicalValueMap U₀) (spectralPhysicalValueMap V₀) ≠ 0 ∧
        ∀ᶠ n in atTop,
          AnalyticAt ℂ (fun z => spectralJetRobin (U n z) (V n z)) (lam n) ∧
          ∀ W : E₄,
            spectralPhysicalDerivativeMap W=
              spectralJetRobin (U n (lam n)) (V n (lam n)) (spectralPhysicalValueMap W) ↔
            ∃ c : ℂ × ℂ, W=c.1 • U n (lam n)+c.2 • V n (lam n) := by
  obtain ⟨Y,hY,TY,hTY,_hLY,Y₀,hy,hylim,_hyeq⟩ :=
    exists_canonical_holomorphic_singular_limit ν m lam ν₀ m₀ lam₀ η hν hm hlam hm₀
      δ L hδ hsmall hX (1,0)
  obtain ⟨Z,hZ,TZ,hTZ,_hLZ,Z₀,hz,hzlim,_hzeq⟩ :=
    exists_canonical_holomorphic_singular_limit ν m lam ν₀ m₀ lam₀ η hν hm hlam hm₀
      δ L hδ hsmall hX (0,1)
  have hd := spectralPhysicalValueDet_eventually_ne_zero (ν₀-2*lam₀) (star ν₀-2*lam₀)
    Y₀ Z₀ hylim hzlim
  have hlog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max TY TZ))
  obtain ⟨R,hR₀,hR,hlogR,hdR⟩ :=
    ((eventually_ge_atTop R₀).and ((eventually_ge_atTop (1 : ℝ)).and (hlog.and hd))).exists
  have hRY : TY ≤ Real.log R := (le_max_left TY TZ).trans hlogR
  have hRZ : TZ ≤ Real.log R := (le_max_right TY TZ).trans hlogR
  have hyR := hy.tendsto_at hRY
  have hzR := hz.tendsto_at hRZ
  have hp := hν.sub (hlam.const_mul 2)
  have hm' := (continuous_star.continuousAt.tendsto.comp hν).sub (hlam.const_mul 2)
  let U := fun n z => spectralPhysicalPair (ν n-2*z) (star (ν n)-2*z) (Y n z) R
  let V := fun n z => spectralPhysicalPair (ν n-2*z) (star (ν n)-2*z) (Z n z) R
  let U₀ := spectralPhysicalPair (ν₀-2*lam₀) (star ν₀-2*lam₀) Y₀ R
  let V₀ := spectralPhysicalPair (ν₀-2*lam₀) (star ν₀-2*lam₀) Z₀ R
  have hUR : Tendsto (fun n => U n (lam n)) atTop (𝓝 U₀) :=
    spectralPhysicalPair_tendsto _ _ _ _ _ _ R hp hm' hyR
  have hVR : Tendsto (fun n => V n (lam n)) atTop (𝓝 V₀) :=
    spectralPhysicalPair_tendsto _ _ _ _ _ _ R hp hm' hzR
  have hdet := spectralValueDet_tendsto _ _ _ _
    (spectralPhysicalValueMap.continuous.continuousAt.tendsto.comp hUR)
    (spectralPhysicalValueMap.continuous.continuousAt.tendsto.comp hVR)
  have hdetn := hdet.eventually (eventually_ne_nhds hdR)
  refine ⟨R,hR₀,hR,Y,Z,Y₀,Z₀,hY.and hZ,
    spectralJetRobin_tendsto _ _ _ _ hUR hVR hdR,hdR,?_⟩
  filter_upwards [hY,hZ,hdetn] with n hyn hzn hdn
  have hlog0 : 0 ≤ Real.log R := hTY.trans hRY
  have hνp : AnalyticAt ℂ (fun z : ℂ => ν n-2*z) (lam n) :=
    analyticAt_const.sub (analyticAt_const.mul analyticAt_id)
  have hνm : AnalyticAt ℂ (fun z : ℂ => star (ν n)-2*z) (lam n) :=
    analyticAt_const.sub (analyticAt_const.mul analyticAt_id)
  have hau : AnalyticAt ℂ (U n) (lam n) := spectralPhysicalPair_analyticAt _ _ _ _ R hνp hνm
    (hyn.2.2.1 (lam n) (Real.log R) hlog0)
  have hav : AnalyticAt ℂ (V n) (lam n) := spectralPhysicalPair_analyticAt _ _ _ _ R hνp hνm
    (hzn.2.2.1 (lam n) (Real.log R) hlog0)
  exact ⟨spectralJetRobin_analyticAt (U n) (V n) (lam n) hau hav hdn,
    fun W => spectralJetRobin_plane (U n (lam n)) (V n (lam n)) W hdn⟩

end DefocusingNLS

end OAI
