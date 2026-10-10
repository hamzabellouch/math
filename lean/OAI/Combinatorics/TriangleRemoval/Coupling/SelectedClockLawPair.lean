import Mathlib
import OAI.Combinatorics.TriangleRemoval.Queries.OrderedMarkedRowUnweighted

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

theorem selectedClockLaw_pair {K : Type*} [DecidableEq K]
    (N : ℕ) [NeZero N] (a b : K) (hab : a ≠ b) (u v : Fin N) :
    selectedClockLaw N {a,b} (Function.update (fun _ => v) a u) =
      Function.update (Function.update (fun _ : K => PMF.uniformOfFintype (Fin N))
        a (PMF.pure u)) b (PMF.pure v) := by
  funext k
  by_cases hka : k = a
  · subst k
    simp [selectedClockLaw,hab]
  · by_cases hkb : k = b
    · subst k
      simp [selectedClockLaw,hka]
    · simp [selectedClockLaw,hka,hkb]

theorem productPMF_split_two_uniform {K : Type*} [Fintype K] [DecidableEq K]
    (N : ℕ) [NeZero N] (a b : K) (hab : a ≠ b) :
    productPMF (fun _ : K => PMF.uniformOfFintype (Fin N)) =
      (PMF.uniformOfFintype (Fin N)).bind (fun u =>
        (PMF.uniformOfFintype (Fin N)).bind (fun v =>
          productPMF (selectedClockLaw N {a,b} (Function.update (fun _ => v) a u)))) := by
  rw [productPMF_split (fun _ : K => PMF.uniformOfFintype (Fin N)) a]
  congr 1
  funext u
  rw [productPMF_split (Function.update (fun _ : K => PMF.uniformOfFintype (Fin N))
    a (PMF.pure u)) b,Function.update_of_ne hab.symm]
  congr 1
  funext v
  rw [selectedClockLaw_pair N a b hab u v]

theorem marked_row_two_paths {K : Type*} [Fintype K] [DecidableEq K]
    (N : ℕ) [NeZero N] (order : List K) (horder : order.Perm Finset.univ.toList)
    (a b : K) (hab : a ≠ b) (p : K → Fin N → PMF (Bool × Bool))
    (q : K → Fin N → ℝ) (deadline : ℕ) (w : ℕ → ℝ)
    (hmarg : ∀ k ∉ ({a,b} : Finset K), ∀ u, markedSuccess (p k u) = q k u)
    (hfactor : ∀ t < deadline, ∀ k, (7 / 8 : ℝ) ≤ prospectiveFailure N t (q k))
    (hfull : ∀ t < deadline, ∏ k, prospectiveFailure N t (q k) ≤ (9 / 8 : ℝ) * w t) :
    markedGood ((productPMF (fun _ : K => PMF.uniformOfFintype (Fin N))).bind
      (fun ω => markedCheck (orderedMarkedRow order {a,b} p deadline ω))) ≤
      (1 / (N : ℝ)) * ∑ u : Fin N, (1 / (N : ℝ)) * ∑ v : Fin N,
        if u.val < deadline ∧ v.val < deadline then
          (markedGood (p a u) * markedGood (p b v)) * (2 * w (max u.val v.val))
        else 0 := by
  rw [productPMF_split_two_uniform N a b hab,PMF.bind_bind,markedGood_bind]
  have hpoint : ∀ u v : Fin N,
      markedGood ((productPMF (selectedClockLaw N {a,b}
        (Function.update (fun _ => v) a u))).bind
        (fun ω => markedCheck (orderedMarkedRow order {a,b} p deadline ω))) ≤
      if u.val < deadline ∧ v.val < deadline then
        (markedGood (p a u) * markedGood (p b v)) * (2 * w (max u.val v.val)) else 0 := by
    intro u v
    let σ : K → Fin N := Function.update (fun _ => v) a u
    have hσa : σ a = u := Function.update_self ..
    have hσb : σ b = v := Function.update_of_ne hab.symm ..
    by_cases huv : u.val < deadline ∧ v.val < deadline
    · rw [ite_eq_left huv]
      have htd : max u.val v.val < deadline := max_lt huv.1 huv.2
      have hsel : ∀ k ∈ ({a,b} : Finset K), (σ k).val < deadline := by
        intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · simpa only [hσa] using huv.1
        · have he : k = b := Finset.mem_singleton.mp hk
          simpa only [he,hσb] using huv.2
      have ht : ∃ k ∈ ({a,b} : Finset K), max u.val v.val ≤ (σ k).val := by
        by_cases h : u.val ≤ v.val
        · exact ⟨b,by simp,by simp only [hσb,max_eq_right h,le_refl]⟩
        · exact ⟨a,by simp,by simp only [hσa,max_eq_left (le_of_not_ge h),le_refl]⟩
      have hh := orderedMarkedRow_cavity_bound N order horder {a,b} σ p q deadline
        (max u.val v.val) (Nat.le_of_lt htd) hsel ht (by simp [hab]) hmarg
        (w (max u.val v.val)) (hfactor _ htd) (hfull _ htd)
      simpa only [Finset.prod_pair hab,hσa,hσb] using hh
    · rw [ite_eq_right huv]
      rw [markedGood_bind]
      apply le_trans (pmfMean_mono _ (g := fun _ => 0) ?_) (by simp)
      intro ω hω
      have hsa := selectedClockLaw_support N {a,b} σ ω hω a (by simp)
      have hsb := selectedClockLaw_support N {a,b} σ ω hω b (by simp)
      by_cases hu : u.val < deadline
      · have hv : deadline ≤ v.val := by omega
        rw [orderedMarkedRow_forbidden order horder {a,b} p deadline ω b (by simp)
          (by simpa only [hsb,hσb] using hv)]
      · rw [orderedMarkedRow_forbidden order horder {a,b} p deadline ω a (by simp)
          (by simpa only [hsa,hσa] using Nat.le_of_not_gt hu)]
  calc
    _ ≤ pmfMean (PMF.uniformOfFintype (Fin N)) (fun u =>
        pmfMean (PMF.uniformOfFintype (Fin N)) (fun v =>
          if u.val < deadline ∧ v.val < deadline then
            (markedGood (p a u) * markedGood (p b v)) * (2 * w (max u.val v.val)) else 0)) := by
      apply pmfMean_mono
      intro u _
      rw [PMF.bind_bind,markedGood_bind]
      exact pmfMean_mono _ (fun v _ => hpoint u v)
    _ = _ := by
      simp only [pmfMean,PMF.uniformOfFintype_apply,ENNReal.toReal_inv,
        ENNReal.toReal_natCast,Fintype.card_fin,one_div,Finset.mul_sum]

theorem max_weight_separate (w : ℕ → ℝ) (C : ℝ)
    (hw : ∀ t, 0 ≤ w t) (hC : ∀ t, 1 ≤ C * w t) (u v : ℕ) :
    w (max u v) ≤ C * (w u * w v) := by
  rcases le_total u v with h | h
  · rw [max_eq_right h]
    have hh := mul_le_mul_of_nonneg_right (hC u) (hw v)
    nlinarith
  · rw [max_eq_left h]
    have hh := mul_le_mul_of_nonneg_right (hC v) (hw u)
    nlinarith

end SharpTerminalLeave

end

end OAI
