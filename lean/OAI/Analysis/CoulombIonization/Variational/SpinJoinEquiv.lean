import Mathlib
import OAI.Analysis.CoulombIonization.Variational.Slices

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace CoulombAtom

def spinJoinEquiv (N M : ℕ) : (Spins N × Spins M) ≃ Spins (N+M) :=
  (Equiv.sumPiEquivProdPi (fun _ : Fin N ⊕ Fin M => Fin 2)).symm.trans
    (Equiv.piCongrLeft (fun _ : Fin (N+M) => Fin 2) finSumFinEquiv)

@[simp] lemma spinJoinEquiv_apply {N M : ℕ} (s : Spins N) (t : Spins M) :
    spinJoinEquiv N M (s,t) = joinLists s t := by
  funext i
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective i
  change (Equiv.piCongrLeft (fun _ : Fin (N+M) => Fin 2) finSumFinEquiv)
    ((Equiv.sumPiEquivProdPi (fun _ : Fin N ⊕ Fin M => Fin 2)).symm (s,t))
      (finSumFinEquiv j) = Sum.elim s t (finSumFinEquiv.symm (finSumFinEquiv j))
  rw [Equiv.piCongrLeft_apply_apply, Equiv.symm_apply_apply]
  cases j <;> rfl

lemma sum_spin_join {N M : ℕ} (f : Spins (N+M) → ℝ) :
    ∑ t : Spins M, ∑ s : Spins N, f (joinLists s t) = ∑ u, f u := by
  have hh := Equiv.sum_comp (spinJoinEquiv N M) f
  rw [Fintype.sum_prod_type, Finset.sum_comm] at hh
  simpa only [spinJoinEquiv_apply] using hh

lemma configurationJoin_apply_prod {N M : ℕ} (p : Configuration N × Configuration M) :
    configurationJoin N M p = joinLists p.1 p.2 := by
  rcases p with ⟨x,y⟩
  exact configurationJoin_apply x y

lemma integrable_join {N M : ℕ} {f : Configuration (N+M) → ℝ}
    (hf : Integrable f) : Integrable (fun p : Configuration N × Configuration M =>
      f (joinLists p.1 p.2)) := by
  simpa only [Function.comp_def, configurationJoin_apply_prod] using
    (configurationJoin_preserving N M).integrable_comp_of_integrable hf

lemma integral_join {N M : ℕ} {f : Configuration (N+M) → ℝ}
    (hf : Integrable f) :
    (∫ y : Configuration M, ∫ x : Configuration N, f (joinLists x y)) = ∫ z, f z := by
  have hj := integrable_join (N := N) (M := M) hf
  have he := (configurationJoin_preserving N M).integral_comp
    (configurationJoin N M).toHomeomorph.measurableEmbedding f
  simp only [configurationJoin_apply_prod] at he
  rw [Measure.volume_eq_prod] at hj he
  exact (integral_prod_symm _ hj).symm.trans he

lemma coreSlice_mass_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevFermion ψ) (t : Spins M) :
    Integrable (fun y => formMass (coreSlice ψ t y)) := by
  apply integrable_finsetSum
  intro s _
  simpa only [coreSlice] using
    (integrable_join (N := N) (M := M) (hψ.1 (joinLists s t)).norm.integrable_sq).integral_prod_right

lemma integral_coreSlice_mass {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevFermion ψ) :
    (∑ t : Spins M, ∫ y, formMass (coreSlice ψ t y)) = formMass ψ := by
  simp only [formMass, coreSlice]
  have h (s : Spins N) (t : Spins M) :
      Integrable (fun y : Configuration M => ∫ x : Configuration N,
        ‖ψ.value (joinLists s t) (joinLists x y)‖ ^ 2) :=
    (integrable_join (N := N) (M := M) (hψ.1 (joinLists s t)).norm.integrable_sq).integral_prod_right
  simp_rw [integral_finsetSum _ (fun s _ => h s _)]
  simp_rw [integral_join (hψ.1 _).norm.integrable_sq]
  exact sum_spin_join (fun u => ∫ z, ‖ψ.value u z‖ ^ 2)

lemma coreSlice_energy_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevFermion ψ) (Z : ℝ) (t : Spins M) :
    Integrable (fun y => formEnergy Z (coreSlice ψ t y)) := by
  have hk (s : Spins N) (i : Fin N) (a : Fin 3) :
      Integrable (fun y : Configuration M => ∫ x : Configuration N,
        ‖(coreSlice ψ t y).gradient s i a x‖ ^ 2) := by
    exact (integrable_join (N := N) (M := M)
      (hψ.2.1 (joinLists s t) (finSumFinEquiv (Sum.inl i)) a).norm.integrable_sq).integral_prod_right
  have hn (s : Spins N) (i : Fin N) :
      Integrable (fun y : Configuration M => ∫ x : Configuration N,
        ‖(coreSlice ψ t y).value s x‖ ^ 2 / ‖x i‖) := by
    have hh := (integrable_join (N := N) (M := M)
      (nuclear_integrable (finSumFinEquiv (Sum.inl i)) (hψ.1 (joinLists s t))
        (hψ.2.1 (joinLists s t) _) (hψ.2.2.1 (joinLists s t) _))).integral_prod_right
    simpa only [coreSlice, joinLists_left] using hh
  have hp (s : Spins N) (i j : Fin N) (hij : i < j) :
      Integrable (fun y : Configuration M => ∫ x : Configuration N,
        ‖(coreSlice ψ t y).value s x‖ ^ 2 / ‖x i-x j‖) := by
    have hne : (finSumFinEquiv (Sum.inl i) : Fin (N+M)) ≠ finSumFinEquiv (Sum.inl j) :=
      fun he => (ne_of_lt hij) (Sum.inl.inj (finSumFinEquiv.injective he))
    have hh := (integrable_join (N := N) (M := M)
      (pair_integrable (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) hne
        (hψ.1 (joinLists s t)) (hψ.2.1 (joinLists s t) _) (hψ.2.2.1 (joinLists s t) _))).integral_prod_right
    simpa only [coreSlice, joinLists_left] using hh
  unfold formEnergy
  apply Integrable.add
  · apply Integrable.sub
    · exact (integrable_finsetSum _ (fun s _ => integrable_finsetSum _ (fun i _ =>
        integrable_finsetSum _ (fun a _ => hk s i a)))).const_mul _
    · exact (integrable_finsetSum _ (fun s _ => integrable_finsetSum _ (fun i _ =>
        hn s i))).const_mul _
  · apply integrable_finsetSum; intro s _
    apply integrable_finsetSum; intro i _
    apply integrable_finsetSum; intro j _
    split_ifs with hij
    · exact hp s i j hij
    · exact integrable_zero _ _ _

theorem integrated_core_energy {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevFermion ψ) {Z : ℝ} (hZ : 0 ≤ Z) :
    energy Z N * formMass ψ ≤ ∑ t : Spins M, ∫ y, formEnergy Z (coreSlice ψ t y) := by
  rw [← integral_coreSlice_mass hψ, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  rw [← integral_const_mul]
  exact integral_mono_ae ((coreSlice_mass_integrable hψ t).const_mul _)
    (coreSlice_energy_integrable hψ Z t) (conditional_core_energy hψ t hZ)

theorem weighted_core_energy {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevFermion ψ) {Z : ℝ} (hZ : 0 ≤ Z)
    (w : Configuration M → ℝ) (hw : AEStronglyMeasurable w)
    (hw0 : ∀ᵐ y, 0 ≤ w y) {C : ℝ} (hwC : ∀ᵐ y, ‖w y‖ ≤ C) :
    energy Z N * (∑ t : Spins M, ∫ y, w y * formMass (coreSlice ψ t y)) ≤
      ∑ t : Spins M, ∫ y, w y * formEnergy Z (coreSlice ψ t y) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  rw [← integral_const_mul]
  apply integral_mono_ae (((coreSlice_mass_integrable hψ t).bdd_mul hw hwC).const_mul _)
    ((coreSlice_energy_integrable hψ Z t).bdd_mul hw hwC)
  filter_upwards [conditional_core_energy hψ t hZ, hw0] with y hy hy0
  simpa only [mul_left_comm (energy Z N) (w y)] using
    mul_le_mul_of_nonneg_left hy hy0

end CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

end

end OAI
