import Mathlib
import OAI.Combinatorics.KMedian.Compression.BoundedDependence

namespace OAI

namespace MetricKMedian.Compression
open Finset Matrix

theorem full_integer_kernel {R Ω : Type} [Fintype R] [Fintype Ω]
    (V : Matrix R Ω ℤ) (L : ℕ) (hV : ∀ r i, |V r i| ≤ (2:ℤ)^L)
    (hsize : Fintype.card R < Fintype.card Ω) :
    ∃ z : Ω → ℤ, (∃ i, z i ≠ 0) ∧
      (∀ i, |z i| ≤ (2:ℤ)^(2*Fintype.card R*(Fintype.card R+L))) ∧
      ∀ r, ∑ i, z i*V r i=0 := by
  classical
  obtain ⟨K,inst,a,z,ha,_,hne,hbound,hker⟩ := small_integer_dependence V L hV hsize
  let zz : Ω → ℤ := fun i => ∑ k, if a k=i then z k else 0
  have hzval : ∀ k, zz (a k)=z k := by
    intro k
    simp only [zz,ha.eq_iff]
    simpa only [mem_univ,ite_true] using sum_ite_eq' univ k z
  have hzout : ∀ i, (¬∃ k, a k=i) → zz i=0 := by
    intro i hi
    apply sum_eq_zero
    intro k _
    exact ite_eq_right (fun hk => hi ⟨k,hk⟩)
  refine ⟨zz,?_,?_,?_⟩
  · obtain ⟨k,hk⟩ := hne
    exact ⟨a k,by rwa [hzval]⟩
  · intro i
    by_cases hi : ∃ k, a k=i
    · obtain ⟨k,rfl⟩ := hi
      rw [hzval]
      exact hbound k
    · rw [hzout i hi,abs_zero]
      positivity
  · intro r
    change (∑ i, (∑ k, if a k=i then z k else 0)*V r i)=0
    simp only [sum_mul,ite_mul,zero_mul]
    rw [sum_comm]
    simpa using hker r

end MetricKMedian.Compression

end OAI
