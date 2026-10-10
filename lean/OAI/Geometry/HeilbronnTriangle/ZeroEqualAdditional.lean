import OAI.Geometry.HeilbronnTriangle.LatticePacking
import OAI.Geometry.HeilbronnTriangle.LatticeBox
import OAI.Geometry.HeilbronnTriangle.IntegralPlaneLattice

namespace OAI


noncomputable section

open MeasureTheory

namespace Problem355.ZeroEqualAdditional

theorem fiber_bound {X I h q r g W : ℝ}
    (hI : 0 < I) (hq : 0 < q) (hr : 0 < r) (hg : 0 < g)
    (hW : 0 ≤ W) (hpairing : g ^ 3 ≤ I * h ^ 2) :
    W * (9 * Real.pi * X ^ 2 / (q * (I * r / g))) ^ 3 ≤
      W * (9 * Real.pi) ^ 3 * X ^ 6 * h ^ 2 / (q ^ 3 * I ^ 2 * r ^ 3) := by
  have hid : W * (9 * Real.pi * X ^ 2 / (q * (I * r / g))) ^ 3 =
      (W * (9 * Real.pi) ^ 3 * X ^ 6 / (q ^ 3 * I ^ 3 * r ^ 3)) * g ^ 3 := by
    field_simp
  rw [hid]
  calc
    (W * (9 * Real.pi) ^ 3 * X ^ 6 / (q ^ 3 * I ^ 3 * r ^ 3)) * g ^ 3 ≤
        (W * (9 * Real.pi) ^ 3 * X ^ 6 / (q ^ 3 * I ^ 3 * r ^ 3)) * (I * h ^ 2) :=
      mul_le_mul_of_nonneg_left hpairing (by positivity)
    _ = W * (9 * Real.pi) ^ 3 * X ^ 6 * h ^ 2 / (q ^ 3 * I ^ 2 * r ^ 3) := by
      field_simp

theorem sum_shell_bound (S : Finset (Fin 3 → ℤ)) (R X I h q W : ℝ)
    (hR : 1 ≤ R) (hI : 0 < I) (hq : 0 < q) (hW : 0 ≤ W)
    (g F : (Fin 3 → ℤ) → ℝ)
    (hshell : ∀ x ∈ S, R ≤ ‖LatticeBox.realVector x‖ ∧
      ‖LatticeBox.realVector x‖ ≤ 2 * R)
    (hg : ∀ x ∈ S, 0 < g x)
    (hpairing : ∀ x ∈ S, g x ^ 3 ≤ I * h ^ 2)
    (hF : ∀ x ∈ S, F x ≤
      W * (9 * Real.pi * X ^ 2 /
        (q * (I * ‖LatticeBox.realVector x‖ / g x))) ^ 3) :
    ∑ x ∈ S, F x ≤
      125 * W * (9 * Real.pi) ^ 3 * X ^ 6 * h ^ 2 / (q ^ 3 * I ^ 2) := by
  have hRp : 0 < R := by linarith
  let C := W * (9 * Real.pi) ^ 3 * X ^ 6 * h ^ 2 /
    (q ^ 3 * I ^ 2 * R ^ 3)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbound (x : Fin 3 → ℤ) (hx : x ∈ S) : F x ≤ C := by
    have hr : 0 < ‖LatticeBox.realVector x‖ := hRp.trans_le (hshell x hx).1
    refine (hF x hx).trans ((fiber_bound hI hq hr (hg x hx) hW (hpairing x hx)).trans ?_)
    dsimp [C]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    gcongr
    exact (hshell x hx).1
  have hc : (S.card : ℝ) ≤ 125 * R ^ 3 :=
    LatticeBox.card_le_onehundredtwentyfive_mul_cube hR S
      (fun x hx i => (LatticeBox.abs_coord_le_norm x i).trans (hshell x hx).2)
  calc
    ∑ x ∈ S, F x ≤ ∑ _x ∈ S, C := Finset.sum_le_sum hbound
    _ = (S.card : ℝ) * C := by simp
    _ ≤ (125 * R ^ 3) * C := mul_le_mul_of_nonneg_right hc hC
    _ = 125 * W * (9 * Real.pi) ^ 3 * X ^ 6 * h ^ 2 / (q ^ 3 * I ^ 2) := by
      dsimp [C]
      field_simp

theorem weighted_lattice_shell_bound
    (S : Finset (Fin 3 → ℤ)) (R X I h q W : ℝ)
    (hR : 1 ≤ R) (hX : 0 ≤ X) (hI : 0 < I) (hq : 0 < q) (hW : 0 ≤ W)
    (g : (Fin 3 → ℤ) → ℝ)
    (K : (x : Fin 3 → ℤ) → Submodule ℤ (IntegralPlaneLattice.plane x))
    [∀ x, DiscreteTopology (K x)] [∀ x, IsZLattice ℝ (K x)]
    (A : (x : Fin 3 → ℤ) → Finset (Fin 3 → K x))
    (weight : (x : Fin 3 → ℤ) → (Fin 3 → K x) → ℝ)
    (hdim : ∀ x ∈ S, Module.finrank ℝ (IntegralPlaneLattice.plane x) = 2)
    (hshell : ∀ x ∈ S, R ≤ ‖LatticeBox.realVector x‖ ∧
      ‖LatticeBox.realVector x‖ ≤ 2 * R)
    (hg : ∀ x ∈ S, 0 < g x)
    (hpairing : ∀ x ∈ S, g x ^ 3 ≤ I * h ^ 2)
    (hcovol : ∀ x ∈ S, ZLattice.covolume (K x) =
      q * (I * ‖LatticeBox.realVector x‖ / g x))
    (hweight : ∀ x ∈ S, ∀ a ∈ A x, weight x a ≤ W)
    (hnorm : ∀ x ∈ S, ∀ a ∈ A x, ∀ i,
      ‖(a i : IntegralPlaneLattice.plane x)‖ ≤ X)
    (hpair : ∀ x ∈ S, ∀ a ∈ A x, ∃ i j : Fin 3,
      LinearIndependent ℝ ![(a i : IntegralPlaneLattice.plane x),
        (a j : IntegralPlaneLattice.plane x)]) :
    ∑ x ∈ S, ∑ a ∈ A x, weight x a ≤
      125 * W * (9 * Real.pi) ^ 3 * X ^ 6 * h ^ 2 / (q ^ 3 * I ^ 2) := by
  apply sum_shell_bound S R X I h q W hR hI hq hW g
    (fun x => ∑ a ∈ A x, weight x a) hshell hg hpairing
  intro x hx
  have hc := LatticePacking.plane_spanning_triples_card_le
    (hdim x hx) (K x) (A x) X hX (hnorm x hx) (hpair x hx)
  rw [hcovol x hx] at hc
  calc
    ∑ a ∈ A x, weight x a ≤ ∑ _a ∈ A x, W :=
      Finset.sum_le_sum (hweight x hx)
    _ = W * ((A x).card : ℝ) := by simp [mul_comm]
    _ ≤ W * (9 * Real.pi * X ^ 2 /
        (q * (I * ‖LatticeBox.realVector x‖ / g x))) ^ 3 :=
      mul_le_mul_of_nonneg_left hc hW

end Problem355.ZeroEqualAdditional

end

end OAI
