import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.Form

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
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
namespace CoulombAtom

def coreKinetic {N M : ℕ} (ψ : FormVector (N+M)) : ℝ :=
  (1/2:ℝ) * ∑ s, ∑ i : Fin N, ∑ a, ∫ z, ‖ψ.gradient s (finSumFinEquiv (Sum.inl i)) a z‖^2

def coreNuclear {N M : ℕ} (ψ : FormVector (N+M)) : ℝ :=
  ∑ s, ∑ i : Fin N, ∫ z, ‖ψ.value s z‖^2 / ‖z (finSumFinEquiv (Sum.inl i))‖

def outNuclear {N M : ℕ} (ψ : FormVector (N+M)) : ℝ :=
  ∑ s, ∑ i : Fin M, ∫ z, ‖ψ.value s z‖^2 / ‖z (finSumFinEquiv (Sum.inr i))‖

def coreRepulsion {N M : ℕ} (ψ : FormVector (N+M)) : ℝ :=
  ∑ s, ∑ i : Fin N, ∑ j : Fin N, if i < j then
    ∫ z, ‖ψ.value s z‖^2 / ‖z (finSumFinEquiv (Sum.inl i))-z (finSumFinEquiv (Sum.inl j))‖ else 0

lemma integral_core_kinetic {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) :
    (∑ t : Spins M, ∫ y, formKinetic (coreSlice ψ t y)) = coreKinetic ψ := by
  have hi (s : Spins N) (t : Spins M) (i : Fin N) (a : Fin 3) :
      Integrable (fun y : Configuration M => ∫ x : Configuration N,
        ‖(coreSlice ψ t y).gradient s i a x‖^2) :=
    (integrable_join (N := N) (M := M)
      (hψ.2.1 (joinLists s t) (finSumFinEquiv (Sum.inl i)) a).norm.integrable_sq).integral_prod_right
  unfold formKinetic coreKinetic
  simp_rw [integral_const_mul, integral_finsetSum _ (fun s _ => integrable_finsetSum _
    (fun i _ => integrable_finsetSum _ (fun a _ => hi s _ i a))),
    integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun a _ => hi _ _ i a)),
    integral_finsetSum _ (fun a _ => hi _ _ _ a)]
  simp only [coreSlice]
  simp_rw [integral_join (hψ.2.1 _ _ _).norm.integrable_sq]
  rw [← Finset.mul_sum]
  congr 1
  exact sum_spin_join (N := N) (M := M) (fun u => ∑ i : Fin N, ∑ a : Fin 3,
    ∫ z, ‖ψ.gradient u (finSumFinEquiv (Sum.inl i)) a z‖^2)

lemma integral_core_nuclear {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) :
    (∑ t : Spins M, ∫ y, formNuclear (coreSlice ψ t y)) = coreNuclear ψ := by
  have hi (s : Spins N) (t : Spins M) (i : Fin N) :
      Integrable (fun y : Configuration M => ∫ x : Configuration N,
        ‖(coreSlice ψ t y).value s x‖^2 / ‖x i‖) := by
    have hh := (integrable_join (N := N) (M := M)
      (nuclear_integrable (finSumFinEquiv (Sum.inl i)) (hψ.1 (joinLists s t))
        (hψ.2.1 (joinLists s t) _) (hψ.2.2 (joinLists s t) _))).integral_prod_right
    simpa only [coreSlice, joinLists_left] using hh
  unfold formNuclear coreNuclear
  simp_rw [integral_finsetSum _ (fun s _ => integrable_finsetSum _ (fun i _ => hi s _ i)),
    integral_finsetSum _ (fun i _ => hi _ _ i)]
  have he (s : Spins N) (t : Spins M) (i : Fin N) :
      (∫ y : Configuration M, ∫ x : Configuration N,
        ‖(coreSlice ψ t y).value s x‖^2 / ‖x i‖) =
      ∫ z, ‖ψ.value (joinLists s t) z‖^2 / ‖z (finSumFinEquiv (Sum.inl i))‖ := by
    simpa only [coreSlice, joinLists_left] using
      integral_join (N := N) (M := M)
        (nuclear_integrable (finSumFinEquiv (Sum.inl i)) (hψ.1 (joinLists s t))
          (hψ.2.1 (joinLists s t) _) (hψ.2.2 (joinLists s t) _))
  simp_rw [he]
  exact sum_spin_join (N := N) (M := M) (fun u => ∑ i : Fin N,
    ∫ z, ‖ψ.value u z‖^2 / ‖z (finSumFinEquiv (Sum.inl i))‖)

lemma integral_core_repulsion {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) :
    (∑ t : Spins M, ∫ y, formRepulsion (coreSlice ψ t y)) = coreRepulsion ψ := by
  have hi (s : Spins N) (t : Spins M) (i j : Fin N) (hij : i < j) :
      Integrable (fun y : Configuration M => ∫ x : Configuration N,
        ‖(coreSlice ψ t y).value s x‖^2 / ‖x i-x j‖) := by
    have hne : (finSumFinEquiv (Sum.inl i) : Fin (N+M)) ≠ finSumFinEquiv (Sum.inl j) :=
      fun hh => (ne_of_lt hij) (Sum.inl.inj (finSumFinEquiv.injective hh))
    have hh := (integrable_join (N := N) (M := M)
      (pair_integrable _ _ hne (hψ.1 (joinLists s t))
        (hψ.2.1 (joinLists s t) _) (hψ.2.2 (joinLists s t) _))).integral_prod_right
    simpa only [coreSlice, joinLists_left] using hh
  have hit (s : Spins N) (t : Spins M) (i j : Fin N) :
      Integrable (fun y => if i < j then ∫ x,
        ‖(coreSlice ψ t y).value s x‖^2 / ‖x i-x j‖ else 0) := by
    split_ifs with hij
    · exact hi s t i j hij
    · exact integrable_zero _ _ _
  unfold formRepulsion coreRepulsion
  simp_rw [integral_finsetSum _ (fun s _ => integrable_finsetSum _
      (fun i _ => integrable_finsetSum _ (fun j _ => hit s _ i j))),
    integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hit _ _ i j)),
    integral_finsetSum _ (fun j _ => hit _ _ _ j)]
  have he (s : Spins N) (t : Spins M) (i j : Fin N) :
      (∫ y : Configuration M, if i < j then ∫ x,
        ‖(coreSlice ψ t y).value s x‖^2 / ‖x i-x j‖ else 0) =
      if i < j then ∫ z, ‖ψ.value (joinLists s t) z‖^2 /
        ‖z (finSumFinEquiv (Sum.inl i))-z (finSumFinEquiv (Sum.inl j))‖ else 0 := by
    split_ifs with hij
    · have hne : (finSumFinEquiv (Sum.inl i) : Fin (N+M)) ≠ finSumFinEquiv (Sum.inl j) :=
        fun hh => (ne_of_lt hij) (Sum.inl.inj (finSumFinEquiv.injective hh))
      simpa only [coreSlice, joinLists_left] using
        integral_join (N := N) (M := M)
          (pair_integrable _ _ hne (hψ.1 (joinLists s t))
            (hψ.2.1 (joinLists s t) _) (hψ.2.2 (joinLists s t) _))
    · exact integral_zero _ _
  simp_rw [he]
  exact sum_spin_join (N := N) (M := M) (fun u => ∑ i : Fin N, ∑ j : Fin N,
    if i < j then ∫ z, ‖ψ.value u z‖^2 /
        ‖z (finSumFinEquiv (Sum.inl i))-z (finSumFinEquiv (Sum.inl j))‖ else 0)

lemma coreSlice_parts_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) :
    Integrable (fun y => formKinetic (coreSlice ψ t y)) ∧
    Integrable (fun y => formNuclear (coreSlice ψ t y)) ∧
    Integrable (fun y => formRepulsion (coreSlice ψ t y)) := by
  have hk (s : Spins N) (i : Fin N) (a : Fin 3) :
      Integrable (fun y : Configuration M => ∫ x : Configuration N,
        ‖(coreSlice ψ t y).gradient s i a x‖^2) :=
    (integrable_join (N := N) (M := M)
      (hψ.2.1 (joinLists s t) (finSumFinEquiv (Sum.inl i)) a).norm.integrable_sq).integral_prod_right
  have hn (s : Spins N) (i : Fin N) :
      Integrable (fun y : Configuration M => ∫ x : Configuration N,
        ‖(coreSlice ψ t y).value s x‖^2 / ‖x i‖) := by
    simpa only [coreSlice, joinLists_left] using (integrable_join (N := N) (M := M)
      (nuclear_integrable (finSumFinEquiv (Sum.inl i)) (hψ.1 (joinLists s t))
        (hψ.2.1 (joinLists s t) _) (hψ.2.2 (joinLists s t) _))).integral_prod_right
  have hp (s : Spins N) (i j : Fin N) (hij : i < j) :
      Integrable (fun y : Configuration M => ∫ x : Configuration N,
        ‖(coreSlice ψ t y).value s x‖^2 / ‖x i-x j‖) := by
    have hne : (finSumFinEquiv (Sum.inl i) : Fin (N+M)) ≠ finSumFinEquiv (Sum.inl j) :=
      fun hh => (ne_of_lt hij) (Sum.inl.inj (finSumFinEquiv.injective hh))
    simpa only [coreSlice, joinLists_left] using (integrable_join (N := N) (M := M)
      (pair_integrable _ _ hne (hψ.1 (joinLists s t))
        (hψ.2.1 (joinLists s t) _) (hψ.2.2 (joinLists s t) _))).integral_prod_right
  refine ⟨?_, ?_, ?_⟩
  · exact (integrable_finsetSum _ (fun s _ => integrable_finsetSum _
      (fun i _ => integrable_finsetSum _ (fun a _ => hk s i a)))).const_mul _
  · exact integrable_finsetSum _ (fun s _ => integrable_finsetSum _ (fun i _ => hn s i))
  · apply integrable_finsetSum; intro s _
    apply integrable_finsetSum; intro i _
    apply integrable_finsetSum; intro j _
    split_ifs with hij
    · exact hp s i j hij
    · exact integrable_zero _ _ _

lemma integrated_core_parts {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (Z : ℝ) :
    (∑ t : Spins M, ∫ y, formEnergy Z (coreSlice ψ t y)) =
      coreKinetic ψ - Z * coreNuclear ψ + coreRepulsion ψ := by
  have he (t : Spins M) : (∫ y, formEnergy Z (coreSlice ψ t y)) =
      (∫ y, formKinetic (coreSlice ψ t y)) - Z * (∫ y, formNuclear (coreSlice ψ t y)) +
      (∫ y, formRepulsion (coreSlice ψ t y)) := by
    simp only [formEnergy_parts]
    rw [integral_add (f := fun y => formKinetic (coreSlice ψ t y) - Z * formNuclear (coreSlice ψ t y))
      (g := fun y => formRepulsion (coreSlice ψ t y)) ((coreSlice_parts_integrable hψ t).1.sub
      ((coreSlice_parts_integrable hψ t).2.1.const_mul Z))
      (coreSlice_parts_integrable hψ t).2.2,
      integral_sub (f := fun y => formKinetic (coreSlice ψ t y))
        (g := fun y => Z * formNuclear (coreSlice ψ t y)) (coreSlice_parts_integrable hψ t).1
        ((coreSlice_parts_integrable hψ t).2.1.const_mul Z), integral_const_mul]
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    integral_core_kinetic hψ, integral_core_nuclear hψ, integral_core_repulsion hψ]

lemma sum_embedding_le {α β : Type*} [Fintype α] [Fintype β]
    (e : α ↪ β) (f : β → ℝ) (hf : ∀ b, 0 ≤ f b) :
    (∑ a, f (e a)) ≤ ∑ b, f b := by
  classical
  rw [← Finset.sum_map]
  exact Finset.sum_le_univ_sum_of_nonneg hf

lemma coreKinetic_le {N M : ℕ} (ψ : FormVector (N+M)) :
    coreKinetic ψ ≤ formKinetic ψ := by
  unfold coreKinetic formKinetic
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum; intro s _
  apply sum_embedding_le ⟨fun i : Fin N => finSumFinEquiv (Sum.inl i),
    fun _ _ h => Sum.inl.inj (finSumFinEquiv.injective h)⟩
    (fun i : Fin (N+M) => ∑ a, ∫ z, ‖ψ.gradient s i a z‖^2)
  intro i
  exact Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _

lemma coreRepulsion_le {N M : ℕ} (ψ : FormVector (N+M)) :
    coreRepulsion ψ ≤ formRepulsion ψ := by
  classical
  let e : Fin N ↪ Fin (N+M) := ⟨fun i => finSumFinEquiv (Sum.inl i),
    fun _ _ h => Sum.inl.inj (finSumFinEquiv.injective h)⟩
  have ho (i j : Fin N) : e i < e j ↔ i < j := Iff.rfl
  let f := fun (s : Spins (N+M)) (i j : Fin (N+M)) =>
    if i < j then ∫ z, ‖ψ.value s z‖^2 / ‖z i-z j‖ else 0
  have hf (s : Spins (N+M)) (i j : Fin (N+M)) : 0 ≤ f s i j := by
    dsimp [f]
    split_ifs
    · exact integral_nonneg fun z => div_nonneg (sq_nonneg _) (norm_nonneg _)
    · exact le_refl _
  unfold coreRepulsion formRepulsion
  apply Finset.sum_le_sum; intro s _
  calc
    _ = ∑ i : Fin N, ∑ j : Fin N, f s (e i) (e j) := by simp only [f,ho]; rfl
    _ ≤ ∑ i : Fin N, ∑ j : Fin (N+M), f s (e i) j := by
      exact Finset.sum_le_sum fun i _ => sum_embedding_le e (f s (e i)) (hf s (e i))
    _ ≤ ∑ i : Fin (N+M), ∑ j : Fin (N+M), f s i j :=
      sum_embedding_le e (fun i => ∑ j, f s i j)
        (fun i => Finset.sum_nonneg fun j _ => hf s i j)

lemma formNuclear_core_out {N M : ℕ} (ψ : FormVector (N+M)) :
    formNuclear ψ = coreNuclear ψ + outNuclear ψ := by
  unfold formNuclear coreNuclear outNuclear
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro s _
  rw [← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]

theorem exterior_energy_lower {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (Z : ℝ) :
    -Z * outNuclear ψ ≤ formEnergy Z ψ -
      (∑ t : Spins M, ∫ y, formEnergy Z (coreSlice ψ t y)) := by
  rw [integrated_core_parts hψ Z,formEnergy_parts,formNuclear_core_out]
  have hk := coreKinetic_le ψ
  have hp := coreRepulsion_le ψ
  linarith

lemma outNuclear_le {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) {R : ℝ} (hR : 0 < R)
    (hs : ∀ s z i, ‖z (finSumFinEquiv (Sum.inr i))‖ < R → ψ.value s z = 0) :
    outNuclear ψ ≤ (M : ℝ)/R * formMass ψ := by
  have hi (s : Spins (N+M)) (i : Fin M) :
      (∫ z, ‖ψ.value s z‖^2 / ‖z (finSumFinEquiv (Sum.inr i))‖) ≤
      R⁻¹ * (∫ z, ‖ψ.value s z‖^2) := by
    rw [← integral_const_mul]
    apply integral_mono
      (nuclear_integrable _ (hψ.1 s) (hψ.2.1 s _) (hψ.2.2 s _))
      ((hψ.1 s).norm.integrable_sq.const_mul R⁻¹)
    intro z
    dsimp only
    by_cases hz : ψ.value s z = 0
    · simp only [hz,norm_zero,zero_pow (by decide : 2 ≠ 0),zero_div,mul_zero,le_refl]
    · have hr := le_of_not_gt (fun hh => hz (hs s z i hh))
      rw [← div_eq_inv_mul]
      exact div_le_div_of_nonneg_left (sq_nonneg _) hR hr
  calc
    _ ≤ ∑ s : Spins (N+M), ∑ _i : Fin M, R⁻¹ * (∫ z, ‖ψ.value s z‖^2) :=
      Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun i _ => hi s i
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,formMass]
      simp_rw [← mul_assoc,← Finset.mul_sum]
      rw [div_eq_mul_inv]

end CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators

end

end OAI
