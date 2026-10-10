import Mathlib
import OAI.Analysis.RieszRectifiability.Packing.ADCellHaarPairs

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem integral_mul_zero_of_constant_on_set {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (A : Set X) (f g : X → ℝ) (c : ℝ)
    (hf : ∀ x ∈ A, f x = c) (hg : ∀ x ∉ A, g x = 0) (hzero : (∫ x, g x ∂μ) = 0) :
    (∫ x, f x * g x ∂μ) = 0 := by
  have heq : (fun x => f x * g x) = fun x => c * g x := by
    funext x
    by_cases hx : x ∈ A
    · rw [hf x hx]
    · rw [hg x hx, mul_zero, mul_zero]
  rw [heq, integral_const_mul, hzero, mul_zero]

theorem integral_mul_zero_of_disjoint_support_sets {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (A B : Set X) (f g : X → ℝ) (hAB : Disjoint A B)
    (hf : ∀ x ∉ A, f x = 0) (hg : ∀ x ∉ B, g x = 0) :
    (∫ x, f x * g x ∂μ) = 0 := by
  apply integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall fun x => by
    change f x * g x = 0
    by_cases hx : x ∈ A
    · rw [hg x (fun hy => Set.disjoint_left.mp hAB hx hy), mul_zero]
    · rw [hf x hx, zero_mul]

theorem SupportCellDescendant.disjoint_of_same_depth {d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (i j : SupportCellDescendant μ R hR k z) (hdepth : i.depth = j.depth) (hne : i ≠ j) :
    Disjoint i.cell j.cell := by
  rcases i with ⟨ti, xi, hxi, hai⟩
  rcases j with ⟨tj, xj, hxj, haj⟩
  dsimp only at hdepth
  subst tj
  have hc : xi ≠ xj := by
    intro heq
    subst xj
    exact hne rfl
  exact cleanSupportCell_disjoint μ R hR (k + ti) ⟨xi, hxi⟩ ⟨xj, hxj⟩
    (fun h => hc (congrArg Subtype.val h))

theorem cellHaarPair_orthogonal_of_level_gap {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k l I : ℕ)
    (z : (supportLatticeNets μ R hR k).points) (w : (supportLatticeNets μ R hR l).points)
    (P : CellHaarPair μ R hR k z I) (Q : CellHaarPair μ R hR l w I)
    (hgap : k + I ≤ l) (hzero : (∫ x, Q.test x ∂μ) = 0) :
    (∫ x, P.test x * Q.test x ∂μ) = 0 := by
  obtain ⟨c, hc⟩ := P.test_constant_on_finer l hgap w
  exact integral_mul_zero_of_constant_on_set μ (cleanSupportCell μ R hR l w) P.test Q.test c
    hc Q.test_zero_outside_parent hzero

theorem bounded_depth_cell_haar_orthogonal {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k I : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (P : (i : SupportCellDescendant μ R hR k z) →
      CellHaarPair μ R hR (k + i.depth) ⟨i.center, i.mem_net⟩ I)
    (i j : SupportCellDescendant μ R hR k z) (hmod : i.depth % I = j.depth % I) (hne : i ≠ j) :
    (∫ x, (P i).test x * (P j).test x ∂μ) = 0 := by
  have hzero (a : SupportCellDescendant μ R hR k z) : (∫ x, (P a).test x ∂μ) = 0 :=
    ((P a).test_properties C G hC hG hg hlower
      (lattice_core_admissible_at_later_level μ R hR k (k + a.depth)
        (Nat.le_add_right k a.depth) hcore)).2.1
  rcases lt_trichotomy i.depth j.depth with hij | hij | hij
  · have hgap : i.depth + I ≤ j.depth := Nat.ModEq.add_le_of_lt hmod hij
    exact cellHaarPair_orthogonal_of_level_gap μ R hR (k + i.depth) (k + j.depth) I
      ⟨i.center, i.mem_net⟩ ⟨j.center, j.mem_net⟩ (P i) (P j) (by omega) (hzero j)
  · exact integral_mul_zero_of_disjoint_support_sets μ i.cell j.cell (P i).test (P j).test
      (i.disjoint_of_same_depth j hij hne) (P i).test_zero_outside_parent (P j).test_zero_outside_parent
  · have hgap : j.depth + I ≤ i.depth := Nat.ModEq.add_le_of_lt hmod.symm hij
    have h := cellHaarPair_orthogonal_of_level_gap μ R hR (k + j.depth) (k + i.depth) I
      ⟨j.center, j.mem_net⟩ ⟨i.center, i.mem_net⟩ (P j) (P i) (by omega) (hzero i)
    simpa only [mul_comm] using! h

end

end RieszRectifiability

end OAI
