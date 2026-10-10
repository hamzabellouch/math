import Mathlib
import OAI.Combinatorics.TriangleRemoval.Probability.FiniteMean

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open scoped BigOperators
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave
section FixedRoots
variable {α : Type*} [Fintype α] [DecidableEq α]

lemma uniform_root_atom (G : Finset α) (hne : G.Nonempty) (e : α) :
    pmfMean (PMF.uniformOfFinset G hne) (fun x => if x = e then 1 else 0) =
      if e ∈ G then 1/(G.card : ℝ) else 0 := by
  rw [pmfMean_uniformOfFinset]
  by_cases he : e ∈ G
  · simp only [he,ite_true]
    rw [Finset.sum_ite_eq']
    simp [he]
  · simp [he]

lemma uniform_ordered_root_atoms (G : Finset α) (hne : G.Nonempty) (e f : α) :
    pmfMean (PMF.uniformOfFinset G hne) (fun x =>
      pmfMean (PMF.uniformOfFinset G hne) (fun y => if x = e ∧ y = f then 1 else 0)) =
      if e ∈ G ∧ f ∈ G then 1/(G.card : ℝ)^2 else 0 := by
  have h (x : α) :
      pmfMean (PMF.uniformOfFinset G hne) (fun y => if x = e ∧ y = f then 1 else 0) =
        (if x = e then 1 else 0)*(if f ∈ G then 1/(G.card : ℝ) else 0) := by
    by_cases hx : x = e
    · simp only [hx,true_and,ite_true,one_mul]
      exact uniform_root_atom G hne f
    · simp [hx]
  simp_rw [h]
  rw [pmfMean_mul_const,uniform_root_atom]
  by_cases he : e ∈ G <;> by_cases hf : f ∈ G <;> simp only [he,hf,ite_true,ite_false,true_and,false_and,zero_mul,mul_zero]
  ring

theorem uniform_root_set_probability_le (G : Finset α) (hne : G.Nonempty)
    (E : Finset α) (hE : E.card = 2) :
    pmfMean (PMF.uniformOfFinset G hne) (fun x =>
      pmfMean (PMF.uniformOfFinset G hne) (fun y => if ({x,y} : Finset α) = E then 1 else 0)) ≤
        2/(G.card : ℝ)^2 := by
  obtain ⟨e,f,hef,rfl⟩ := Finset.card_eq_two.mp hE
  have hpt (x y : α) : (if ({x,y} : Finset α) = {e,f} then (1 : ℝ) else 0) ≤
      (if x=e ∧ y=f then 1 else 0) + (if x=f ∧ y=e then 1 else 0) := by
    by_cases h : ({x,y} : Finset α) = {e,f}
    · have hm : x ∈ ({e,f} : Finset α) := h ▸ Finset.mem_insert_self _ _
      have hn : y ∈ ({e,f} : Finset α) := h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      have hxy : x ≠ y := by
        intro heq
        subst y
        have hh := congrArg Finset.card h
        simp only [Finset.insert_eq_of_mem (Finset.mem_singleton_self _),Finset.card_singleton,
          Finset.card_pair hef] at hh
        omega
      have hx : x = e ∨ x = f := by simpa only [Finset.mem_insert,Finset.mem_singleton] using hm
      have hy : y = e ∨ y = f := by simpa only [Finset.mem_insert,Finset.mem_singleton] using hn
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact False.elim (hxy (hx.trans hy.symm))
      · simp [hx,hy,hef]
      · simp [hx,hy,hef,Finset.pair_comm]
      · exact False.elim (hxy (hx.trans hy.symm))
    · simp only [h,ite_false]
      split_ifs <;> norm_num
  have hh : pmfMean (PMF.uniformOfFinset G hne) (fun x =>
      pmfMean (PMF.uniformOfFinset G hne) (fun y => if ({x,y} : Finset α) = {e,f} then 1 else 0)) ≤
      pmfMean (PMF.uniformOfFinset G hne) (fun x =>
      pmfMean (PMF.uniformOfFinset G hne) (fun y =>
        (if x=e ∧ y=f then 1 else 0)+(if x=f ∧ y=e then 1 else 0))) := by
    apply pmfMean_mono
    intro x _
    apply pmfMean_mono
    intro y _
    exact hpt x y
  simp_rw [pmfMean_add] at hh
  rw [uniform_ordered_root_atoms,uniform_ordered_root_atoms] at hh
  have hnon : 0 ≤ 1/(G.card : ℝ)^2 := by positivity
  have htwo : 2/(G.card : ℝ)^2 = 2*(1/(G.card : ℝ)^2) := by ring
  exact hh.trans (by rw [htwo]; split_ifs <;> linarith)

end FixedRoots
end SharpTerminalLeave

end

end OAI
