import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.Failure
import OAI.Combinatorics.RamseyFive.Entropy.Swap

namespace OAI

namespace SharpRamseyFive.LowConflict
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.CoreGeometry
open scoped BigOperators Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

noncomputable def reverseMiss (p : Law β) (q : Law γ)
    (v : β → Module.Dual K V) (w : γ → V) : ℝ :=
  ∑ b,∑ c,if v b (w c)≠0 then p b*q c else 0

omit [FiniteDimensional K V] in
lemma reverseMiss_nonneg (p : Law β) (q : Law γ)
    (v : β → Module.Dual K V) (w : γ → V) : 0≤reverseMiss p q v w := by
  apply Finset.sum_nonneg
  intro b _
  apply Finset.sum_nonneg
  intro c _
  split_ifs
  · exact mul_nonneg (p.nonneg b) (q.nonneg c)
  · exact le_rfl

omit [FiniteDimensional K V] in
lemma reverseMiss_eq (p : Law β) (q : Law γ)
    (v : β → Module.Dual K V) (w : γ → V) :
    reverseMiss p q v w = ∑ c,q c*failure p v (Module.Dual.eval K V (w c)) := by
  rw [reverseMiss,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [CoreGeometry.failure,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  change (if v b (w c)≠0 then _ else _) = q c*(if v b (w c)≠0 then _ else _)
  split_ifs <;> simp [mul_comm]

noncomputable def capturedEvent (p : Law (α × β)) (q : Law (γ × δ))
    (v : β → Module.Dual K V) (w : γ → V) (good : α → δ → Prop)
    (a : α) (b : β) (c : γ) (y : δ) : Prop :=
  good a y ∧ reverseMiss (fiber p a) (fiber (swap q) y) v w≤(1/40000:ℝ) ∧
    v b∈core (K := K) (fiber p a) v (1/200) ∧
    w c∈core (K := K) (fiber (swap q) y) w (1/200)

omit [FiniteDimensional K V] in
lemma captured_orthogonal (p : Law (α × β)) (q : Law (γ × δ))
    (v : β → Module.Dual K V) (w : γ → V) (good : α → δ → Prop)
    (a : α) (b : β) (c : γ) (y : δ) (h : capturedEvent p q v w good a b c y) :
    core (K := K) (fiber p a) v (1/200) ≤
      (core (K := K) (fiber (swap q) y) w (1/200)).dualAnnihilator := by
  intro f hf
  apply (Submodule.mem_dualAnnihilator f).mpr
  intro z hz
  apply core_orthogonal (fiber p a) v (fiber (swap q) y) w (1/200) (by norm_num) _ f hf z hz
  rw [←reverseMiss_eq]
  convert h.2.1 using 1; norm_num

lemma conditional_charge (hdim : finrank K V=5) (p : Law (α × β)) (q : Law (γ × δ))
    (v : β → Module.Dual K V) (w : γ → V) (good : α → δ → Prop) (a : α) (y : δ) :
    (19/20:ℝ)*(if good a y then 1 else 0) ≤
      38000*(if good a y then reverseMiss (fiber p a) (fiber (swap q) y) v w else 0)+
      ∑ b,∑ c,if capturedEvent p q v w good a b c y then
        fiber p a b*fiber (swap q) y c else 0 := by
  by_cases hg : good a y
  · simp only [hg,ite_true]
    by_cases hm : reverseMiss (fiber p a) (fiber (swap q) y) v w≤(1/40000:ℝ)
    · have hc := source_core_capture hdim (fiber p a) (fiber (swap q) y) v w
      have hz := reverseMiss_nonneg (fiber p a) (fiber (swap q) y) v w
      simp only [capturedEvent,hg,hm,true_and]
      nlinarith
    · have hh : (19/20:ℝ)≤38000*reverseMiss (fiber p a) (fiber (swap q) y) v w := by
        linarith
      simpa only [capturedEvent,hg,hm,true_and,false_and,ite_false,Finset.sum_const_zero,add_zero,mul_one] using hh
  · simp only [hg,ite_false,mul_zero,zero_add,capturedEvent,false_and,Finset.sum_const_zero,le_refl]
end SharpRamseyFive.LowConflict

end OAI
