import OAI.Combinatorics.Crossing.Bivariate
import OAI.Combinatorics.Crossing.TwoTriangleIndices

namespace OAI

noncomputable section
namespace Zarankiewicz
open PolynomialModule
open Finset

theorem eq_zero_of_roots_injOn {W : Type*} [AddCommGroup W] [Module ℝ W]
    (node : ℕ → ℝ) (S : Finset ℕ) (hn : Set.InjOn node (S : Set ℕ))
    (p : PolynomialModule ℝ W) (hp : Bounded S.card p)
    (he : ∀ i ∈ S, eval (node i) p = 0) : p = 0 := by
  let x : S → ℝ := fun i => node i.val
  have hx : Function.Injective x := by
    intro i j hij
    exact Subtype.ext (hn i.property j.property hij)
  apply eq_zero_of_node_roots x hx Finset.univ p
  · simpa using hp
  · intro i hi
    exact he i.val i.property

theorem twoTriangle_unisolvent (s : ℕ) (node : ℕ → ℝ)
    (hn : Set.InjOn node (Set.Icc 1 (2*s+1))) (p : BiPoly)
    (hp : BiBounded s s p)
    (hv : ∀ a b, (a,b) ∈ twoTriangle s → biEval (node a) (node b) p = 0) : p = 0 := by
  induction s generalizing node p with
  | zero => exact (bounded_zero_iff p).mp hp.1
  | succ k ih =>
    have node_ne : ∀ a b, a ∈ Icc 1 (2*(k+1)+1) → b ∈ Icc 1 (2*(k+1)+1) →
        a ≠ b → node a ≠ node b := by
      intro a b ha hb hab he
      exact hab (hn (by simpa only [mem_Icc, Set.mem_Icc] using ha)
        (by simpa only [mem_Icc, Set.mem_Icc] using hb) he)

    have hrow : eval (node (k+2)) p = 0 := by
      apply eq_zero_of_roots_injOn node (Icc 1 (k+1))
      · intro a ha b hb he
        apply hn _ _ he <;> simp only [mem_coe, mem_Icc, Set.mem_Icc] at * <;> omega
      · simpa using bounded_eval_outer hp (node (k+2))
      · intro q hq
        apply hv (k+2) q
        rw [mem_twoTriangle]
        simp only [mem_Icc] at hq
        left
        omega
    obtain ⟨p₁, hp₁, he₁⟩ := bi_factor_row k (k+1) p hp (node (k+2)) hrow

    have hcol : eval (node 1) (swapBi p₁) = 0 := by
      apply eq_zero_of_roots_injOn node (Icc 2 (k+1))
      · intro a ha b hb he
        apply hn _ _ he <;> simp only [mem_coe, mem_Icc, Set.mem_Icc] at * <;> omega
      · simpa using bounded_eval_outer (biBounded_swap hp₁) (node 1)
      · intro a ha
        change biEval (node 1) (node a) (swapBi p₁) = 0
        rw [biEval_swap]
        have hpa : biEval (node a) (node 1) p = 0 := by
          apply hv
          rw [mem_twoTriangle]
          simp only [mem_Icc] at ha
          left
          omega
        rw [← he₁, biEval_mulRoot] at hpa
        apply (mul_eq_zero.mp hpa).resolve_left
        apply sub_ne_zero.mpr
        apply node_ne a (k+2) <;> simp only [mem_Icc] at * <;> omega
    obtain ⟨r, hr, her⟩ := bi_factor_row k k (swapBi p₁) (biBounded_swap hp₁) (node 1) hcol

    let y : ℕ → ℝ := fun i => node (triangleRelabel (k+1) i)
    have hyrange : ∀ a, a ∈ Icc 1 (2*k+1) →
        triangleRelabel (k+1) a ∈ Icc 1 (2*(k+1)+1) ∧
          triangleRelabel (k+1) a ≠ k+2 ∧ triangleRelabel (k+1) a ≠ 1 := by
      intro a ha
      simpa only [show k+1+1 = k+2 from rfl] using
        triangleRelabel_range (k+1) a (by simp only [mem_Icc] at *; omega)
    have hyn : Set.InjOn y (Set.Icc 1 (2*k+1)) := by
      intro a ha b hb he
      have ha' : a ∈ Icc 1 (2*k+1) := by simpa only [mem_Icc, Set.mem_Icc] using ha
      have hb' : b ∈ Icc 1 (2*k+1) := by simpa only [mem_Icc, Set.mem_Icc] using hb
      apply triangleRelabel_injective_on (k+1)
      · simp only [Set.mem_Icc] at *
        omega
      · simp only [Set.mem_Icc] at *
        omega
      · exact hn (by simpa only [Set.mem_Icc, mem_Icc] using (hyrange a ha').1)
          (by simpa only [Set.mem_Icc, mem_Icc] using (hyrange b hb').1) he
    have hrv : ∀ a b, (a,b) ∈ twoTriangle k → biEval (y a) (y b) r = 0 := by
      intro a b hab
      have ha : a ∈ Icc 1 (2*k+1) := by
        rw [mem_twoTriangle] at hab
        simp only [mem_Icc]
        omega
      have hb : b ∈ Icc 1 (2*k+1) := by
        rw [mem_twoTriangle] at hab
        simp only [mem_Icc]
        omega
      have hpattern := relabel_twoTriangle (k+1) (by omega) a b (by simpa using hab)
      have hval := hv (triangleRelabel (k+1) b) (triangleRelabel (k+1) a) hpattern.1
      rw [← he₁, biEval_mulRoot] at hval
      have hfirst : node (triangleRelabel (k+1) b) - node (k+2) ≠ 0 :=
        sub_ne_zero.mpr (node_ne _ _ (hyrange b hb).1 (by simp) (hyrange b hb).2.1)
      have hp₁val := (mul_eq_zero.mp hval).resolve_left hfirst
      have hswap : p₁ = swapBi (mulRoot (node 1) r) := by rw [her, swapBi_swapBi]
      rw [hswap, biEval_swap, biEval_mulRoot] at hp₁val
      apply (mul_eq_zero.mp hp₁val).resolve_left
      exact sub_ne_zero.mpr (node_ne _ _ (hyrange a ha).1 (by simp) (hyrange a ha).2.2)
    have hr0 := ih y hyn r hr hrv
    have hp₁0 : p₁ = 0 := by
      apply swapBi.injective
      rw [← her, hr0]
      simp [mulRoot]
    rw [← he₁, hp₁0]
    simp [mulRoot]

theorem twoTriangle_evaluation_injective (s : ℕ) (node : ℕ → ℝ)
    (hn : Set.InjOn node (Set.Icc 1 (2*s+1))) (p q : BiPoly)
    (hp : BiBounded s s p) (hq : BiBounded s s q)
    (he : ∀ a b, (a,b) ∈ twoTriangle s → biEval (node a) (node b) p = biEval (node a) (node b) q) :
    p = q := by
  apply sub_eq_zero.mp
  apply twoTriangle_unisolvent s node hn (p-q)
  · refine ⟨bounded_sub hp.1 hq.1, ?_⟩
    intro a
    exact bounded_sub (hp.2 a) (hq.2 a)
  · intro a b hab
    rw [map_sub, he a b hab, sub_self]

end Zarankiewicz

end

end OAI
