import OAI.Geometry.RCD.Heat.LiYauRiccatiAlgebra
import OAI.Geometry.RCD.Heat.RiccatiInitialBound

namespace OAI

/-! # The parameter-two scalar Li--Yau bound from Fisher evolution -/

open Set
namespace RegularPointCoordinates

theorem liYau_fisher_bound {I : ℝ → ℝ} {T n M k D : ℝ}
    (hT : 0<T) (hn : 0<n) (hM : 0<M) (hk : 0≤k)
    (h0 : ContinuousAt I 0) (hc : ContinuousOn I (Ico 0 T))
    (hI : ∀ t∈Ioo 0 T, 0≤I t)
    (hd : ∀ t∈Ioo 0 T, ∃ rate : ℝ, HasDerivAt I rate t ∧
      (2/n)*(D-I t)^2-2*k*M*I t≤M*rate) :
    I 0-2*D≤2*n*M*(k+1/T) := by
  let Y := fun t => I t-2*D
  have hY0 : ContinuousAt Y 0 := h0.sub continuousAt_const
  have hYc : ContinuousOn Y (Ico 0 T) := hc.sub continuousOn_const
  have hYd (t : ℝ) (ht : t∈Ioo 0 T) :
      ∃ rate : ℝ, HasDerivAt Y rate t ∧
        (2*n*M*k≤Y t → (1/(2*n*M))*(Y t-2*n*M*k)^2≤rate) := by
    obtain ⟨rate,hrate,hbound⟩ := hd t ht
    exact ⟨rate,hrate.sub_const (2*D),
      liYau_riccati_algebra hn hM hk (hI t ht) hbound⟩
  have hb := riccati_initial_bound hT (by positivity : 0<1/(2*n*M)) hY0 hYc hYd
  have he : 2*n*M*k+1/((1/(2*n*M))*T)=2*n*M*(k+1/T) := by
    field_simp
  rwa [he] at hb

end RegularPointCoordinates

end OAI
