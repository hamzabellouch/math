import OAI.Combinatorics.ProgressionColoring.LiteralLabelRectangles
import OAI.Combinatorics.ProgressionColoring.LabelFiber
import OAI.Combinatorics.ProgressionColoring.ClosestReturn
import OAI.Combinatorics.ProgressionColoring.CyclicRationalReturn

namespace OAI

/-!
# Closest returns to actual full labels

The occurrence set is the literal full-label fiber in an actual cyclic
progression. The box widths, arithmetic-progression congruences and dilation
congruence are discharged using the concrete mesh and representative APIs.
-/

noncomputable section

namespace QuantitativeVanDerWaerden

def fullLabelFiber (mesh : AdaptiveMesh) (q D lam Ucount : ℕ)
    (hU : 0 < Ucount) (k : ℕ) (a d : CyclicGroup q D)
    (beta : (Fin D → Fin Ucount) × (Fin D → mesh.Label)) : Finset ℕ :=
  labelFiber k (fun j => literalFullLabel mesh q D lam Ucount hU (a + j • d)) beta

@[simp] theorem mem_fullLabelFiber {mesh : AdaptiveMesh} {q D lam Ucount k j : ℕ}
    {hU : 0 < Ucount} {a d : CyclicGroup q D}
    {beta : (Fin D → Fin Ucount) × (Fin D → mesh.Label)} :
    j ∈ fullLabelFiber mesh q D lam Ucount hU k a d beta ↔
      j < k ∧ literalFullLabel mesh q D lam Ucount hU (a + j • d) = beta :=
  mem_labelFiber

structure IsHeavyLabelReturn (mesh : AdaptiveMesh) (q D lam Ucount k M : ℕ)
    (hU : 0 < Ucount) (a d : CyclicGroup q D)
    (beta : (Fin D → Fin Ucount) × (Fin D → mesh.Label)) (j h : ℕ) : Prop where
  start_lt : j < k
  end_lt : j + h < k
  gap_pos : 0 < h
  gap_le : h ≤ 2 * M
  start_label : literalFullLabel mesh q D lam Ucount hU (a + j • d) = beta
  end_label : literalFullLabel mesh q D lam Ucount hU (a + (j + h) • d) = beta
  minimum : ∀ s ∈ fullLabelFiber mesh q D lam Ucount hU k a d beta,
    ∀ t ∈ fullLabelFiber mesh q D lam Ucount hU k a d beta, s < t → h ≤ t - s
  no_earlier : ∀ t, 0 < t → t < h →
    literalFullLabel mesh q D lam Ucount hU (a + (j + t) • d) ≠ beta
  x_card : ∀ i, |xRep q D (a + (j + h) • d) i - xRep q D (a + j • d) i| ≤
    (1 / (Ucount : ℝ)) /
      ((fullLabelFiber mesh q D lam Ucount hU k a d beta).card - 1 : ℝ)
  x_rate : ∀ i, |xRep q D (a + (j + h) • d) i - xRep q D (a + j • d) i| ≤
    2 * (M : ℝ) * (1 / (Ucount : ℝ)) / (k : ℝ)
  y_card : ∀ i, |yRep q D lam (a + (j + h) • d) i - yRep q D lam (a + j • d) i| ≤
    (2 * mesh.H) /
      ((fullLabelFiber mesh q D lam Ucount hU k a d beta).card - 1 : ℝ)
  y_rate : ∀ i, |yRep q D lam (a + (j + h) • d) i - yRep q D lam (a + j • d) i| ≤
    4 * (M : ℝ) * mesh.H / (k : ℝ)
  dilation_eq : ∀ i,
    yRep q D lam (a + (j + h) • d) i - yRep q D lam (a + j • d) i =
      (lam : ℝ) * (xRep q D (a + (j + h) • d) i - xRep q D (a + j • d) i)

/-- A heavy actual full-label fiber has an attained closest return with the
claimed real displacement bounds. No representative or label geometry is
assumed: only the displayed scalar parameter inequalities remain as inputs. -/
theorem exists_heavy_label_return (mesh : AdaptiveMesh) {q D lam Ucount k M : ℕ}
    (hq : 0 < q) (hU : 0 < Ucount) (hM : 0 < M) (hscale : 2 * M ≤ k)
    (a d : CyclicGroup q D)
    (beta : (Fin D → Fin Ucount) × (Fin D → mesh.Label))
    (hheavy : k < M * (fullLabelFiber mesh q D lam Ucount hU k a d beta).card)
    (hwidth : 1 / (Ucount : ℝ) ≤ 2 * mesh.H)
    (hdilation : (lam : ℝ) * (1 / (Ucount : ℝ)) = mesh.H)
    (hsmall : 2 * (k : ℝ) * mesh.H < 1)
    (hdriftsmall : 6 * (M : ℝ) * mesh.H / (k : ℝ) < 1) :
    ∃ j h, IsHeavyLabelReturn mesh q D lam Ucount k M hU a d beta j h := by
  let J := fullLabelFiber mesh q D lam Ucount hU k a d beta
  have hJ : ∀ j ∈ J, j < k := fun _ hj => (mem_fullLabelFiber.mp hj).1
  have hlabels : ∀ j ∈ J, literalFullLabel mesh q D lam Ucount hU (a + j • d) = beta :=
    fun _ hj => (mem_fullLabelFiber.mp hj).2
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hscaleR : 2 * (M : ℝ) ≤ k := by exact_mod_cast hscale
  have hheavyR : (k : ℝ) / M < J.card := by
    apply (div_lt_iff₀ hMR).2
    have hh : (k : ℝ) < (M : ℝ) * (J.card : ℝ) := by exact_mod_cast hheavy
    simpa only [mul_comm] using hh
  have hxbox : ∀ i ∈ J, ∀ j ∈ J, ∀ e,
      |xRep q D (a + j • d) e - xRep q D (a + i • d) e| ≤ 1 / (Ucount : ℝ) := by
    intro i hi j hj e
    exact literalFullLabel_same_first_distance mesh q D lam Ucount hU
      ((hlabels j hj).trans (hlabels i hi).symm) e
  have hybox : ∀ i ∈ J, ∀ j ∈ J, ∀ e,
      |yRep q D lam (a + j • d) e - yRep q D lam (a + i • d) e| ≤ 2 * mesh.H := by
    intro i hi j hj e
    exact literalFullLabel_same_second_distance mesh q D lam Ucount hU
      ((hlabels j hj).trans (hlabels i hi).symm) e
  obtain ⟨j, h, hj, hjh, hh, hend, hmin, _, hgap, hcoord⟩ :=
    exists_closest_return_drift hJ hMR hscaleR hheavyR mesh.H_pos.le
      (by positivity : (0 : ℝ) ≤ 1 / (Ucount : ℝ)) hwidth hsmall hxbox hybox
      (fun n i => xRep_ap_congr hq a d n i)
      (fun n i => yRep_ap_congr hq lam a d n i)
      (Nat.cast_nonneg lam) hdilation
      (fun n i => yRep_dilation_congr hq lam (a + n • d) i) hdriftsmall
  refine ⟨j, h, ?_⟩
  refine {
    start_lt := hJ j hj
    end_lt := hend
    gap_pos := hh
    gap_le := by exact_mod_cast hgap
    start_label := hlabels j hj
    end_label := hlabels (j + h) hjh
    minimum := hmin
    no_earlier := no_earlier_label_return hj hend hmin
    x_card := fun i => (hcoord i).1
    x_rate := fun i => (hcoord i).2.1
    y_card := fun i => (hcoord i).2.2.1
    y_rate := fun i => (hcoord i).2.2.2.1
    dilation_eq := fun i => (hcoord i).2.2.2.2 }

namespace IsHeavyLabelReturn

variable {mesh : AdaptiveMesh} {q D lam Ucount k M j h : ℕ} {hU : 0 < Ucount}
  {a d : CyclicGroup q D} {beta : (Fin D → Fin Ucount) × (Fin D → mesh.Label)}
  (R : IsHeavyLabelReturn mesh q D lam Ucount k M hU a d beta j h)

include R

theorem start_rectangle :
    (∀ i, UniformMesh.Contains Ucount (beta.1 i) (xRep q D (a + j • d) i)) ∧
    (∀ i, mesh.Contains (beta.2 i) (yRep q D lam (a + j • d) i)) :=
  (literalFullLabel_eq_iff mesh q D lam Ucount hU _ beta).mp R.start_label

theorem end_rectangle :
    (∀ i, UniformMesh.Contains Ucount (beta.1 i) (xRep q D (a + (j + h) • d) i)) ∧
    (∀ i, mesh.Contains (beta.2 i) (yRep q D lam (a + (j + h) • d) i)) :=
  (literalFullLabel_eq_iff mesh q D lam Ucount hU _ beta).mp R.end_label

theorem no_earlier_rectangle (t : ℕ) (ht : 0 < t) (hth : t < h) :
    ¬ ((∀ i, UniformMesh.Contains Ucount (beta.1 i) (xRep q D (a + (j + t) • d) i)) ∧
      (∀ i, mesh.Contains (beta.2 i) (yRep q D lam (a + (j + t) • d) i))) := by
  intro hrect
  exact R.no_earlier t ht hth
    ((literalFullLabel_eq_iff mesh q D lam Ucount hU _ beta).mpr hrect)

/-- The primitive rational path now follows for this actual heavy label,
using the actual first-coordinate displacement as the drift vector. -/
theorem primitive_return_path (hq : 0 < q) :
    ∃ t : Fin D → ℤ, (∀ i, 0 ≤ t i ∧ t i < h) ∧ PrimitiveVector h t ∧
      (∀ (n : ℕ) (i : Fin D), ∃ z : ℤ,
        xRep q D (a + n • d) i - xRep q D a i - (n : ℝ) / h *
          ((t i : ℝ) + (xRep q D (a + (j + h) • d) i - xRep q D (a + j • d) i)) = z) ∧
      (∀ (n : ℕ) (i : Fin D), ∃ z : ℤ,
        yRep q D lam (a + n • d) i - yRep q D lam a i - (n : ℝ) / h *
          ((lam : ℝ) * ((t i : ℝ) +
            (xRep q D (a + (j + h) • d) i - xRep q D (a + j • d) i))) = z) := by
  exact cyclic_primitive_return_path hq a d
    (fun i => UniformMesh.left Ucount (beta.1 i))
    (fun i => UniformMesh.right Ucount (beta.1 i))
    (fun i => mesh.left (beta.2 i)) (fun i => mesh.right (beta.2 i))
    (fun i => xRep q D (a + (j + h) • d) i - xRep q D (a + j • d) i)
    R.gap_pos R.end_lt R.start_rectangle.1 R.start_rectangle.2
    R.end_rectangle.1 R.end_rectangle.2 R.no_earlier_rectangle (fun _ => rfl) R.dilation_eq

end IsHeavyLabelReturn

end QuantitativeVanDerWaerden

end

end OAI
