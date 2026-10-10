import OAI.Probability.ContinuumTransition.KacKernel

namespace OAI

section
open scoped Topology BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

noncomputable def gridIndex (u : ℝ) (x : Space) : Lattice := fun i => ⌊x i/u⌋

noncomputable def gridCenter (u : ℝ) (k : Lattice) : Space :=
  WithLp.toLp 2 (fun i => u*((k i : ℝ)+1/2))

def gridBox (u : ℝ) (k : Lattice) : Set Space :=
  {x | ∀ i, u*(k i : ℝ) ≤ x i ∧ x i < u*((k i : ℝ)+1)}

theorem measurableSet_gridBox (u : ℝ) (k : Lattice) : MeasurableSet (gridBox u k) := by
  have heq : gridBox u k = (@WithLp.ofLp 2 (Fin 3 → ℝ)) ⁻¹'
      (Set.pi Set.univ (fun i => Ico (u*(k i : ℝ)) (u*((k i : ℝ)+1)))) := by
    ext x
    simp only [gridBox, mem_preimage, mem_ofPred_eq, Set.mem_pi, mem_univ, forall_const, mem_Ico]
  rw [heq]
  exact (MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ico)).preimage
    (PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)).continuous.measurable

theorem mem_gridBox_iff {u : ℝ} (hu : 0 < u) (k : Lattice) (x : Space) :
    x ∈ gridBox u k ↔ gridIndex u x = k := by
  simp only [gridBox, mem_ofPred_eq, gridIndex, funext_iff]
  apply forall_congr'
  intro i
  rw [Int.floor_eq_iff, le_div_iff₀ hu, div_lt_iff₀ hu]
  simp only [mul_comm u]

theorem mem_gridBox {u : ℝ} (hu : 0 < u) (x : Space) : x ∈ gridBox u (gridIndex u x) :=
  (mem_gridBox_iff hu _ _).2 rfl

theorem gridBox_disjoint {u : ℝ} (hu : 0 < u) {k l : Lattice} (hkl : k ≠ l) :
    Disjoint (gridBox u k) (gridBox u l) := by
  apply Set.disjoint_left.2
  intro x hx hy
  exact hkl (((mem_gridBox_iff hu _ _).1 hx).symm.trans ((mem_gridBox_iff hu _ _).1 hy))

theorem volume_gridBox {u : ℝ} (hu : 0 ≤ u) (k : Lattice) :
    volume (gridBox u k) = ENNReal.ofReal (u^3) := by
  have heq : gridBox u k = (@WithLp.ofLp 2 (Fin 3 → ℝ)) ⁻¹'
      (Set.pi Set.univ (fun i => Ico (u*(k i : ℝ)) (u*((k i : ℝ)+1)))) := by
    ext x
    simp only [gridBox, mem_preimage, mem_ofPred_eq, Set.mem_pi, mem_univ, forall_const, mem_Ico]
  rw [heq, (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage
    ((MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ico)).nullMeasurableSet)]
  change (Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ))) _ = _
  rw [Measure.pi_pi]
  simp only [Real.volume_Ico]
  simp only [show ∀ i, u*((k i : ℝ)+1)-u*(k i : ℝ)=u by intro i; ring]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.ofReal_pow hu]

theorem gridBox_center_distance {u : ℝ} (hu : 0 < u) {k : Lattice} {x : Space}
    (hx : x ∈ gridBox u k) : ‖x-gridCenter u k‖ ≤ 2*u := by
  have hc (i : Fin 3) : |x i-gridCenter u k i| ≤ u := by
    have hxi := hx i
    change |x i-u*((k i : ℝ)+1/2)| ≤ u
    rw [abs_le]
    constructor <;> linarith
  have hs (i : Fin 3) : (x i-gridCenter u k i)^2 ≤ u^2 :=
    by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hu.le).2 (hc i)
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) => hs i)
  have hn : ‖x-gridCenter u k‖^2 ≤ 3*u^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa only [PiLp.sub_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
      using hh
  nlinarith [norm_nonneg (x-gridCenter u k)]

theorem gridIndex_quarter_nat (q : ℕ) (x : Space) :
    gridIndex ((q : ℝ)/4) x = fun i => cellIndex x i/(q : ℤ) := by
  funext i
  dsimp only [gridIndex, cellIndex]
  rw [show x i/((q : ℝ)/4)=(4*x i)/(q : ℝ) by ring, Int.floor_div_natCast]

theorem gridIndex_eq_of_cellIndex_eq (q : ℕ) {x y : Space} (hxy : cellIndex x = cellIndex y) :
    gridIndex ((q : ℝ)/4) x = gridIndex ((q : ℝ)/4) y := by
  rw [gridIndex_quarter_nat, gridIndex_quarter_nat, hxy]

end ContinuumTemperature
end

end OAI
