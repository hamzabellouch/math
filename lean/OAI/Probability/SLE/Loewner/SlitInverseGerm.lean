import OAI.Probability.SLE.Geometry.StrictRealLocalChart

namespace OAI

/-! The analytic inverse germ at infinity respects reflection and the
upper side. This is the local branch for the actual slit inverse. -/
noncomputable section
open Set Filter Complex Function Metric
open scoped Topology ComplexConjugate

namespace SLEExactGauge

lemma local_inverse_reflection {q r : ℂ → ℂ}
    (hr : ContinuousAt r 0) (hr0 : r 0=0)
    (hs : ∀ᶠ z in 𝓝 (0:ℂ), q (conj z)=conj (q z))
    (hl : ∀ᶠ z in 𝓝 (0:ℂ), r (q z)=z)
    (hh : ∀ᶠ z in 𝓝 (0:ℂ), q (r z)=z) :
    ∀ᶠ z in 𝓝 (0:ℂ), r (conj z)=conj (r z) := by
  have ht : Tendsto r (𝓝 (0:ℂ)) (𝓝 0) := by simpa only [hr0] using hr.tendsto
  have hc : Tendsto (fun z => conj (r z)) (𝓝 (0:ℂ)) (𝓝 0) := by
    convert! (Complex.continuous_conj.tendsto 0).comp ht using 1
    simp
  filter_upwards [ht.eventually hs,hc.eventually hl,hh] with z hsz hlz hhz
  rwa [hsz,hhz] at hlz

theorem slitReciprocalMap_exists_upper_inverse
    {D : Set ℂ} (hD : D ∈ 𝓝 (0:ℂ)) {f : ℂ → ℂ} {a : ℝ}
    (hf : AnalyticAt ℂ f 0) (ha : a ≠ 0) (hd : deriv f 0=(a:ℂ))
    (hs : ∀ z ∈ D, f (conj z)=conj (f z)) :
    ∃ (r : ℂ → ℂ) (ε : ℝ), 0<ε ∧ AnalyticAt ℂ r 0 ∧ r 0=0 ∧ deriv r 0=1 ∧
      MapsTo r (ball 0 ε ∩ upperHalfPlane) upperHalfPlane ∧
      (∀ᶠ z in 𝓝 (0:ℂ), r (slitReciprocalMap f a z)=z) ∧
      (∀ᶠ z in 𝓝 (0:ℂ), slitReciprocalMap f a (r z)=z) := by
  obtain ⟨r,hr,hr0,hrd,hl,hh⟩ := slitReciprocalMap_exists_local_inverse hf ha hd
  have hsym : ∀ᶠ z in 𝓝 (0:ℂ), slitReciprocalMap f a (conj z)=
      conj (slitReciprocalMap f a z) := by
    filter_upwards [hD] with z hz
    exact slitReciprocalMap_reflection hD hs a z hz
  have hrs := local_inverse_reflection hr.continuousAt hr0 hsym hl hh
  obtain ⟨S,hS,hsS⟩ := hrs.exists_mem
  have hstrict : HasStrictDerivAt r 1 0 := by simpa only [hrd] using hr.hasStrictDerivAt
  obtain ⟨ε,hε,hupper⟩ := strict_real_germ_maps_upper hS hstrict hsS
  exact ⟨r,ε,hε,hr,hr0,hrd,hupper,hl,hh⟩

end SLEExactGauge

end

end OAI
