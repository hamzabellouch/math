import OAI.Geometry.RCD.Heat.LiYauParameterAlgebra
import OAI.Geometry.RCD.Heat.RiccatiInitialBound

namespace OAI

/-! # Arbitrary-parameter Li--Yau control from the proved Fisher evolution -/

open Set
namespace RegularPointCoordinates

theorem liYau_fisher_parameter_bound {I : ℝ → ℝ} {T n M k D α : ℝ}
    (hT : 0 < T) (hn : 0 < n) (hM : 0 < M) (hk : 0 ≤ k) (hα : 1 < α)
    (h0 : ContinuousAt I 0) (hc : ContinuousOn I (Ico 0 T))
    (hI : ∀ t ∈ Ioo 0 T, 0 ≤ I t)
    (hd : ∀ t ∈ Ioo 0 T, ∃ rate : ℝ, HasDerivAt I rate t ∧
      (2/n)*(D-I t)^2-2*k*M*I t ≤ M*rate) :
    I 0-α*D ≤ (n*M*α^2/2)*(k/(α-1)+1/T) := by
  let Y := fun t => I t-α*D
  have hα0 : 0 < α := lt_trans zero_lt_one hα
  have hY0 : ContinuousAt Y 0 := h0.sub continuousAt_const
  have hYc : ContinuousOn Y (Ico 0 T) := hc.sub continuousOn_const
  have hYd (t : ℝ) (ht : t ∈ Ioo 0 T) :
      ∃ rate : ℝ, HasDerivAt Y rate t ∧
        (n*M*α^2*k/(2*(α-1)) ≤ Y t →
          (2/(n*M*α^2))*(Y t-n*M*α^2*k/(2*(α-1)))^2 ≤ rate) := by
    obtain ⟨rate,hrate,hbound⟩ := hd t ht
    exact ⟨rate,hrate.sub_const (α*D),
      liYau_parameter_algebra hn hM hk (hI t ht) hα hbound⟩
  have hb := riccati_initial_bound hT (by positivity : 0 < 2/(n*M*α^2)) hY0 hYc hYd
  have he : n*M*α^2*k/(2*(α-1))+1/((2/(n*M*α^2))*T) =
      (n*M*α^2/2)*(k/(α-1)+1/T) := by
    field_simp
  rwa [he] at hb

end RegularPointCoordinates

end OAI
