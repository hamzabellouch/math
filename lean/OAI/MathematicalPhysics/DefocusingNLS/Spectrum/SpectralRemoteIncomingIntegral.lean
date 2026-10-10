import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteIntegratingFactor

namespace OAI

/-! Integration from infinity gives the small incoming component. The
exponent of the solution bound is fixed before the decay order is chosen. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralRemote_incoming_terminal (L T C m A M : ℝ)
    (hLT : L < T) (hgap : 5*C < m)
    (b y f : ℝ → ℂ) (hb : ContinuousOn b (Ioi L)) (hf : ContinuousOn f (Ici T))
    (hbnd : ∀ t ∈ Ioi L, |(b t).re| ≤ C)
    (hy : ∀ t ∈ Ici T, HasDerivAt y (b t*y t+f t) t)
    (hlim : Tendsto (fun t => spectralRemoteIntegratingFactor T b t*y t) atTop (𝓝 0))
    (hforcing : ∀ t ∈ Ici T,
      ‖f t‖ ≤ A*M*Real.exp (4*C*(t-T))*Real.exp (-m*t)) :
    ‖y T‖ ≤ A*M/(m-5*C)*Real.exp (-m*T) := by
  let mu := spectralRemoteIntegratingFactor T b
  have hmu : ContinuousOn mu (Ici T) := by
    intro t ht
    exact (spectralRemoteIntegratingFactor_deriv L T t hLT ht b hb).continuousAt.continuousWithinAt
  have hderiv (t : ℝ) (ht : t ∈ Ici T) :
      HasDerivAt (fun u => mu u*y u) (mu t*f t) t :=
    spectralRemoteIntegratingFactor_equation L T t hLT ht b y f hb (hy t ht)
  have hbound (t : ℝ) (ht : t ∈ Ici T) :
      ‖mu t*f t‖ ≤ A*M*Real.exp (-5*C*T)*Real.exp (-(m-5*C)*t) := by
    rw [norm_mul]
    calc
      _ ≤ Real.exp (C*(t-T))*‖f t‖ := mul_le_mul_of_nonneg_right
        (spectralRemoteIntegratingFactor_bound L T t C hLT ht b hb hbnd) (norm_nonneg _)
      _ ≤ Real.exp (C*(t-T))*(A*M*Real.exp (4*C*(t-T))*Real.exp (-m*t)) :=
        mul_le_mul_of_nonneg_left (hforcing t ht) (Real.exp_pos _).le
      _ = A*M*Real.exp (-5*C*T)*Real.exp (-(m-5*C)*t) := by
        calc
          _ = A*M*(Real.exp (C*(t-T))*Real.exp (4*C*(t-T))*Real.exp (-m*t)) := by ring
          _ = A*M*(Real.exp (-5*C*T)*Real.exp (-(m-5*C)*t)) := by
            rw [← Real.exp_add,← Real.exp_add,← Real.exp_add]
            congr 2
            ring
          _ = _ := by ring
  have hh := spectralRemote_terminal_bound T (m-5*C) (A*M*Real.exp (-5*C*T))
    (sub_pos.mpr hgap) (fun t => mu t*y t) (fun t => mu t*f t)
    (hmu.mul hf) hderiv hlim hbound
  have hbase : mu T = 1 := spectralRemoteIntegratingFactor_base T b
  rw [hbase,one_mul] at hh
  apply hh.trans_eq
  calc
    _ = A*M/(m-5*C)*(Real.exp (-5*C*T)*Real.exp (-(m-5*C)*T)) := by ring
    _ = _ := by
      rw [← Real.exp_add]
      congr 2
      ring

theorem spectralRemote_integrating_factor_limit (L T C sigma : ℝ) (hLT : L < T)
    (b y : ℝ → ℂ) (hb : ContinuousOn b (Ioi L))
    (hbnd : ∀ t ∈ Ioi L, |(b t).re| ≤ C)
    (hy : HasLogJetBound sigma y) (hdecay : C+sigma < 0) :
    Tendsto (fun t => spectralRemoteIntegratingFactor T b t*y t) atTop (𝓝 0) := by
  obtain ⟨K,hK,hbound⟩ := hy.bound 0
  have hexp : Tendsto (fun t : ℝ => Real.exp ((C+sigma)*t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_neg hdecay).2 tendsto_id)
  apply squeeze_zero_norm' _ (by simpa only [mul_zero] using hexp.const_mul (K*Real.exp (-C*T)))
  filter_upwards [hbound,eventually_ge_atTop T] with t ht htT
  rw [norm_mul]
  simp only [iteratedDeriv_zero] at ht
  calc
    _ ≤ Real.exp (C*(t-T))*(K*Real.exp (sigma*t)) :=
      mul_le_mul (spectralRemoteIntegratingFactor_bound L T t C hLT htT b hb hbnd) ht
        (norm_nonneg _) (Real.exp_pos _).le
    _ = K*Real.exp (-C*T)*Real.exp ((C+sigma)*t) := by
      calc
        _ = K*(Real.exp (C*(t-T))*Real.exp (sigma*t)) := by ring
        _ = K*(Real.exp (-C*T)*Real.exp ((C+sigma)*t)) := by
          rw [← Real.exp_add,← Real.exp_add]
          congr 2
          ring
        _ = _ := by ring

end DefocusingNLS

end OAI
