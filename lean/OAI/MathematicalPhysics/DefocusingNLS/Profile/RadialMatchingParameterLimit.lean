import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchingLimit

namespace OAI

/-! Every accumulation point of the nonlinear matching parameters is a certified free root. -/

open Filter
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchingMap_zero_limit (s : ℕ → ℕ) (hs : Tendsto s atTop atTop)
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
    (hz : Tendsto z atTop (nhds z₀)) (hzero : ∀ i, radialMatchingMap (s i) (z i)=0) :
    z₀.val.1=0 ∧ diskProfile (profileMatchingParameter z₀)=0 := by
  have hsub : TendstoUniformly (fun i => radialMatchingMap (s i))
      (fun z => (z.val.1,diskProfile (profileMatchingParameter z))) atTop :=
    fun u hu => hs.eventually (radialMatchingMap_limit u hu)
  have hc : Continuous (fun z : ProfileMatchingBall =>
      (z.val.1,diskProfile (profileMatchingParameter z))) :=
    continuous_subtype_val.fst.prodMk (continuous_diskProfile.comp continuous_profileMatchingParameter)
  have ht := hsub.tendsto_comp hc.continuousAt hz
  have h0 : Tendsto (fun i => radialMatchingMap (s i) (z i)) atTop (nhds 0) := by
    simp only [hzero]
    exact tendsto_const_nhds
  have he := tendsto_nhds_unique ht h0
  exact ⟨congrArg Prod.fst he,congrArg Prod.snd he⟩

end DefocusingNLS

end OAI
