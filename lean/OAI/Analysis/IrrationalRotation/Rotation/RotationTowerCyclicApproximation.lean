import OAI.Analysis.IrrationalRotation.Rotation.RotationTowerAlgebras
import OAI.Analysis.IrrationalRotation.Analysis.TowerCyclicShift
import OAI.Analysis.IrrationalRotation.Operators.TowerTraceBounds
import OAI.Analysis.IrrationalRotation.Rotation.RotationTowerApproximation

namespace OAI

noncomputable section
open Filter
open scoped BigOperators Topology

namespace Invariant233.Rotation

variable {β : Type*} [Fintype β]

omit [Fintype β] in

theorem towerMatrixEntries_diagonal_eq_setProjection
    (θ : ℝ) (s : β → Set Circle) (hs : ∀ b, MeasurableSet (s b))
    (height : β → ℕ) (b : β) (i : Fin (height b)) :
    towerMatrixEntries θ s hs height b i i =
      setProjection θ (towerLevel θ (s b) i)
        (measurableSet_towerLevel θ (s b) (hs b) i) := by
  obtain ⟨hm, heq⟩ := U_pow_setProjection_star_image θ i.val (s b) (hs b)
  exact heq

theorem sum_towerMatrixEntries_diagonal_eq_one
    (θ : ℝ) (s : β → Set Circle) (hs : ∀ b, MeasurableSet (s b))
    (height : β → ℕ)
    (hdisj : Pairwise (fun a b : Σ c, Fin (height c) =>
      Disjoint (towerLevel θ (s a.1) a.2) (towerLevel θ (s b.1) b.2)))
    (hcover : ∀ x : Circle, ∃ b, ∃ i : Fin (height b), x ∈ towerLevel θ (s b) i) :
    (∑ b, ∑ i : Fin (height b), towerMatrixEntries θ s hs height b i i) = 1 := by
  classical
  let level : (Σ b, Fin (height b)) → Set Circle := fun a => towerLevel θ (s a.1) a.2
  have hm : ∀ a, MeasurableSet (level a) := fun a =>
    measurableSet_towerLevel θ (s a.1) (hs a.1) a.2
  have hcov : (⋃ a ∈ (Finset.univ : Finset (Σ b, Fin (height b))), level a) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨b, i, hi⟩ := hcover x
    exact Set.mem_iUnion.mpr ⟨⟨b, i⟩, Set.mem_iUnion.mpr ⟨Finset.mem_univ _, hi⟩⟩
  have hsum := sum_setProjection_eq_one θ Finset.univ level hm
    (fun a _ b _ hab => hdisj hab) hcov
  simp only [Fintype.sum_sigma] at hsum
  simpa only [towerMatrixEntries_diagonal_eq_setProjection] using hsum

def towerCyclicOperator (θ : ℝ) (s : β → Set Circle)
    (hs : ∀ b, MeasurableSet (s b)) (height : β → ℕ) : Hilbert →L[ℂ] Hilbert :=
  TowerCyclicShift.cyclicSum height (towerMatrixEntries θ s hs (fun b => height b + 1))

def towerTopProjection (θ : ℝ) (s : β → Set Circle)
    (hs : ∀ b, MeasurableSet (s b)) (height : β → ℕ) : Hilbert →L[ℂ] Hilbert :=
  TowerCyclicShift.topSum height (towerMatrixEntries θ s hs (fun b => height b + 1))

theorem towerCyclicOperator_properties
    (θ : ℝ) (s : β → Set Circle) (hs : ∀ b, MeasurableSet (s b)) (height : β → ℕ)
    (hdisj : Pairwise (fun a b : Σ c, Fin (height c + 1) =>
      Disjoint (towerLevel θ (s a.1) a.2) (towerLevel θ (s b.1) b.2)))
    (hcover : ∀ x : Circle, ∃ b, ∃ i : Fin (height b + 1), x ∈ towerLevel θ (s b) i) :
    towerCyclicOperator θ s hs height ∈ finiteTowerAlgebra θ s hs (fun b => height b + 1) ∧
    towerCyclicOperator θ s hs height ∈ unitary (Hilbert →L[ℂ] Hilbert) ∧
    IsStarProjection (towerTopProjection θ s hs height) ∧
    U - towerCyclicOperator θ s hs height =
      (U - towerCyclicOperator θ s hs height) * towerTopProjection θ s hs height ∧
    ‖U - towerCyclicOperator θ s hs height‖ ≤ 2 := by
  classical
  let e := towerMatrixEntries θ s hs (fun b => height b + 1)
  have he := towerMatrixEntries_isBlockMatrixUnitFamily θ s hs (fun b => height b + 1) hdisj
  have hcomplete : (∑ b, TowerCyclicShift.diagonalSum (e b)) = 1 :=
    sum_towerMatrixEntries_diagonal_eq_one θ s hs (fun b => height b + 1) hdisj hcover
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact TowerCyclicShift.cyclicSum_mem _ height e (fun b i j =>
      towerEntry_mem_finiteTowerAlgebra θ s hs _ b i.isLt j.isLt)
  · exact TowerCyclicShift.cyclicSum_mem_unitary height e
      (fun b => (he.block b).star) (fun b => (he.block b).mul) he.cross hcomplete
  · exact TowerCyclicShift.topSum_isStarProjection height e
      (fun b => (he.block b).star) (fun b => (he.block b).mul) he.cross
  · exact TowerCyclicShift.sub_cyclicSum_eq_mul_topSum_of_towerEntries height e U
      (fun b => setProjection θ (s b) (hs b)) (fun _ _ _ => rfl)
      (fun b => (he.block b).mul) he.cross hcomplete
  · exact TowerCyclicShift.norm_sub_cyclicSum_le_two height e U U_mem_unitary
      (fun b => (he.block b).star) (fun b => (he.block b).mul) he.cross hcomplete

theorem towerCyclicOperator_vacuum_error_sq_le
    (θ : ℝ) (s : β → Set Circle) (hs : ∀ b, MeasurableSet (s b)) (height : β → ℕ)
    (hdisj : Pairwise (fun a b : Σ c, Fin (height c + 1) =>
      Disjoint (towerLevel θ (s a.1) a.2) (towerLevel θ (s b.1) b.2)))
    (hcover : ∀ x : Circle, ∃ b, ∃ i : Fin (height b + 1), x ∈ towerLevel θ (s b) i)
    (N : ℕ) (hN : 0 < N) (hheight : ∀ b, N ≤ height b + 1) :
    ‖towerCyclicOperator θ s hs height vacuum - U vacuum‖ ^ 2 ≤ 4 / (N : ℝ) := by
  classical
  let e := towerMatrixEntries θ s hs (fun b => height b + 1)
  have he := towerMatrixEntries_isBlockMatrixUnitFamily θ s hs (fun b => height b + 1) hdisj
  have hprop := towerCyclicOperator_properties θ s hs height hdisj hcover
  have hagree : towerCyclicOperator θ s hs height * (1 - towerTopProjection θ s hs height) =
      U * (1 - towerTopProjection θ s hs height) := by
    have hz : (U - towerCyclicOperator θ s hs height) *
        (1 - towerTopProjection θ s hs height) = 0 := by
      rw [mul_sub, mul_one, ← hprop.2.2.2.1, sub_self]
    exact (sub_eq_zero.mp (by simpa only [sub_mul] using hz)).symm
  exact TowerTraceBounds.norm_sub_apply_sq_le_four_div_height e he
    (vacuum_faithfulTracial θ)
    (fun b i j => (finiteTowerAlgebra_le θ s hs (fun c => height c + 1)) (towerEntry_mem_finiteTowerAlgebra
      θ s hs (fun c => height c + 1) b i.isLt j.isLt))
    (fun b => Fin.last (height b))
    (sum_towerMatrixEntries_diagonal_eq_one θ s hs _ hdisj hcover)
    N hN (fun b => by simpa using hheight b)
    (le_of_eq (CStarRing.norm_of_mem_unitary hprop.2.1))
    (le_of_eq (CStarRing.norm_of_mem_unitary U_mem_unitary)) hagree

theorem towerCyclicOperator_tendsto_apply
    (κ : ℕ → Type*) [∀ n, Fintype (κ n)] (θ : ℝ)
    (s : ∀ n, κ n → Set Circle) (hs : ∀ n b, MeasurableSet (s n b))
    (height : ∀ n, κ n → ℕ)
    (hdisj : ∀ n, Pairwise (fun a b : Σ c, Fin (height n c + 1) =>
      Disjoint (towerLevel θ (s n a.1) a.2) (towerLevel θ (s n b.1) b.2)))
    (hcover : ∀ n (x : Circle), ∃ b, ∃ i : Fin (height n b + 1),
      x ∈ towerLevel θ (s n b) i)
    (hheight : ∀ n b, n + 1 ≤ height n b + 1) (v : Hilbert) :
    Tendsto (fun n => towerCyclicOperator θ (s n) (hs n) (height n) v)
      atTop (𝓝 (U v)) := by
  have hprop (n : ℕ) := towerCyclicOperator_properties θ (s n) (hs n) (height n)
    (hdisj n) (hcover n)
  have hbound : Tendsto (fun n : ℕ => 4 / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one, div_eq_mul_inv, one_mul, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (4 : ℝ)
  have hsq : Tendsto (fun n =>
      ‖towerCyclicOperator θ (s n) (hs n) (height n) vacuum - U vacuum‖ ^ 2)
      atTop (𝓝 0) :=
    squeeze_zero (fun _ => sq_nonneg _) (fun n =>
      towerCyclicOperator_vacuum_error_sq_le θ (s n) (hs n) (height n)
        (hdisj n) (hcover n) (n + 1) (Nat.zero_lt_succ n) (hheight n)) hbound
  have hvac : Tendsto (fun n => towerCyclicOperator θ (s n) (hs n) (height n) vacuum)
      atTop (𝓝 (U vacuum)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hsq
  exact strong_tendsto_of_vacuum_of_bounded θ
    (fun n => (finiteTowerAlgebra_le θ (s n) (hs n) _ (hprop n).1))
    (U_mem_algebra θ) hvac
    (Eventually.of_forall fun n => le_of_eq (CStarRing.norm_of_mem_unitary (hprop n).2.1)) v

end Invariant233.Rotation

end

end OAI
