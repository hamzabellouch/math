import Mathlib
import OAI.Combinatorics.UniformKServer.AlphaEmpty

namespace OAI

                                    
section

/-! Common-core prepared states can be evaluated in either parameter domain.
 The zero-weight case is proved separately; there is no hidden division by a
 small core mass. -/
noncomputable section
namespace UniformKServer.AlphaPrepared
open Finset UniformKServer.AlphaEmpty
open scoped Classical
variable {ι : Type*} [Fintype ι]

theorem zero_of_sum {B : ι → ℝ} (hB : ∀ i, 0 ≤ B i) (hz : ∑ i, B i=0) :
    B=fun _ => 0 := by
  funext i
  have hi := single_le_sum (s:=univ) (f:=B) (fun j _ => hB j) (mem_univ i)
  exact le_antisymm (by linarith) (hB i)

theorem prepared_state {p q : Config ι} {B b : ι → ℝ}
    (hS : 0 < ∑ i, B i) (hs : DomainTransport.Supported (active p) B)
    (hqB : DomainTransport.Supported (active q) B) (hb : state q b)
    (hf : ∀ i, (∑ j, B j)*b i ≤ (1+eta p i)*B i) : state p b := by
  cases p with
  | none =>
    have he := zero_supported hs
    simp only [he,sum_const_zero,lt_self_iff_false] at hS
  | some p =>
    cases q with
    | none =>
      have he := zero_supported hqB
      simp only [he,sum_const_zero,lt_self_iff_false] at hS
    | some q =>
      change DomainTransport.simplex q.active b at hb
      refine ⟨hb.1,?_,hb.2.2⟩
      intro i hi
      have h := hf i
      rw [hs i hi,mul_zero] at h
      exact le_antisymm ((nonpos_of_mul_nonpos_right h hS)) (hb.1 i)

theorem bound {p q : Config ι} (hp : valid p) (B b : ι → ℝ)
    (hB : ∀ i, 0 ≤ B i) (hs : DomainTransport.Supported (active p) B)
    (hqB : DomainTransport.Supported (active q) B) (hb : state q b)
    (hf : ∀ i, (∑ j, B j)*b i ≤ (1+eta p i)*B i) :
    |potential p B b| ≤ 15*scale p*(∑ i, B i) := by
  have hS : 0 ≤ ∑ i, B i := sum_nonneg fun i _ => hB i
  rcases hS.eq_or_lt with hz | hpos
  · have he := zero_of_sum hB hz.symm
    rw [he,potential_zero,abs_zero,sum_const_zero,mul_zero]
  · have ho := prepared_state hpos hs hqB hb hf
    have h := input_bound hp B (fun _ => 0) b ho
    simpa only [potential_zero,sub_zero,abs_of_nonneg (hB _)] using h

theorem jump {p q : Config ι} (hp : valid p) (hq : valid q) (B b : ι → ℝ)
    (hB : ∀ i, 0 ≤ B i) (hs : DomainTransport.Supported (active p) B)
    (hqB : DomainTransport.Supported (active q) B) (hb : state q b)
    (hf : ∀ i, (∑ j, B j)*b i ≤ (1+eta p i)*B i) :
    |potential q B b-potential p B b| ≤ 15*(scale p+scale q)*(∑ i, B i) := by
  have h := bound hp B b hB hs hqB hb hf
  have h' := input_bound hq B (fun _ => 0) b hb
  simp only [potential_zero,sub_zero,abs_of_nonneg (hB _)] at h'
  exact (abs_sub _ _).trans (by nlinarith)

end UniformKServer.AlphaPrepared

end


end

end OAI
