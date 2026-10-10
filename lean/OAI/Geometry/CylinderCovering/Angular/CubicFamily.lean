import OAI.Geometry.CylinderCovering.Angular.CubicCoverDefinitions
import OAI.Geometry.CylinderCovering.Angular.Margins
import OAI.Geometry.CylinderCovering.Cubic.LowerGeometry

namespace OAI

noncomputable section
namespace CylinderCovering.Cubic
open Set TriangularCovering

lemma family_node_strict {N : ℕ} (hN : 0 < N) (j : ℕ) :
    node N j < node N (j + 1) := by
  have := node_succ N j
  have := step_pos hN
  linarith

lemma family_cap_pos {ε : ℝ} (hε : 0 ≤ ε) (a b : ℝ) : 0 < cap ε a b := by
  have ha : 0 ≤ profile a := by unfold profile; positivity
  have hm : 0 ≤ profileMax a b := ha.trans (le_max_left _ _)
  unfold cap
  positivity

def lowerFamily4 (ε : ℝ) (hε : 0 < ε) (j : Fin (n ε)) : TriCylinder :=
  CubicLowerGeometry.lowerCylinder
    (family_node_strict (ceil_count_pos hε) j)
    (family_cap_pos hε.le (node (n ε) j) (node (n ε) (j + 1))) ε
    (alpha (node (n ε) j) (node (n ε) (j + 1)))
    (beta (node (n ε) j) (node (n ε) (j + 1)))

def upperFamily4 (ε : ℝ) (hε : 0 < ε) (j : Fin (n ε)) : TriCylinder :=
  TriangularCovering.upperCylinder
    (family_node_strict (ceil_count_pos hε) j)
    (family_cap_pos hε.le (node (n ε) j) (node (n ε) (j + 1))) ε
    (alpha (node (n ε) j) (node (n ε) (j + 1)))
    (beta (node (n ε) j) (node (n ε) (j + 1)))

def finiteFamily4 (ε : ℝ) (hε : 0 < ε) : Fin (2 * n ε) → TriCylinder :=
  (Fin.append (lowerFamily4 ε hε) (upperFamily4 ε hε)) ∘ Fin.cast (two_mul (n ε))

lemma finiteFamily4_covers_of_coordinate_cover {ε : ℝ} (hε : 0 < ε)
    (hcover : ∀ x y z : ℝ, |x| ≤ 1 - z → |y| ≤ 1 + z →
      (∃ j : ℕ, j < n ε ∧ LowerHit (n ε) j ε x y z) ∨
      (∃ j : ℕ, j < n ε ∧ UpperHit (n ε) j ε x y z)) :
    CoversK4 (finiteFamily4 ε hε) := by
  rintro p ⟨x, y, z, _hz0, _hz1, hx, hy, rfl⟩
  rcases hcover x y z hx hy with ⟨j, hj, hl⟩ | ⟨j, hj, hu⟩
  · refine ⟨Fin.cast (two_mul (n ε)).symm
      (Fin.castAdd (n ε) (⟨j, hj⟩ : Fin (n ε))), ?_⟩
    simp only [finiteFamily4, Function.comp_apply, Fin.cast_cast,
      Fin.cast_eq_self, Fin.append_left]
    exact CubicLowerGeometry.lowerCylinder_hit _ _ _ _ _ _ _ _
      hl.1.1 hl.2 hl.1.2.1 hl.1.2.2
  · refine ⟨Fin.cast (two_mul (n ε)).symm
      (Fin.natAdd (n ε) (⟨j, hj⟩ : Fin (n ε))), ?_⟩
    simp only [finiteFamily4, Function.comp_apply, Fin.cast_cast,
      Fin.cast_eq_self, Fin.append_right]
    exact TriangularCovering.upperCylinder_hit _ _ _ _ _ _ _ _
      hu.1.1 hu.2 hu.1.2.1 hu.1.2.2

lemma finiteFamily4_total (ε : ℝ) (hε : 0 < ε) :
    totalArea (finiteFamily4 ε hε) = cubicCost ε := by
  have hs : totalArea (finiteFamily4 ε hε) =
      (∑ j : Fin (n ε), area (lowerFamily4 ε hε j).base) +
      (∑ j : Fin (n ε), area (upperFamily4 ε hε j).base) := by
    change (∑ i : Fin (2 * n ε),
      (fun k : Fin (n ε + n ε) =>
        area (Fin.append (lowerFamily4 ε hε) (upperFamily4 ε hε) k).base)
        ((finCongr (two_mul (n ε))) i)) = _
    rw [Equiv.sum_comp (finCongr (two_mul (n ε)))
      (fun k => area (Fin.append (lowerFamily4 ε hε) (upperFamily4 ε hε) k).base)]
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  rw [hs, ← Finset.sum_add_distrib, cubicCost, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [lowerFamily4, upperFamily4, CubicLowerGeometry.lowerCylinder_area,
    TriangularCovering.upperCylinder_area, node_succ]
  dsimp only [n]
  ring

lemma finiteFamily4_prescribed (ε : ℝ) (hε : 0 < ε) :
    PrescribedFamily ε (finiteFamily4 ε hε) := by
  intro j
  simp only [lowerIndex, upperIndex, finiteFamily4, Function.comp_apply,
    Fin.cast_cast, Fin.cast_eq_self, Fin.append_left, Fin.append_right]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem finiteCover_proof : FiniteCoverStatement := by
  intro ε hε hsmall
  refine ⟨finiteFamily4 ε hε, ?_, finiteFamily4_total ε hε,
    finiteFamily4_prescribed ε hε⟩
  apply finiteFamily4_covers_of_coordinate_cover hε
  intro x y z hx hy
  exact finite_coordinate_cover_ceil hε hsmall hx hy

end CylinderCovering.Cubic

end

end OAI
