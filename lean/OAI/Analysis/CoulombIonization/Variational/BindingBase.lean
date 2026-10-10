import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.ActualMasterCenterComparison

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

lemma linear_hardy_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure]
    (P : E →L[ℝ] Space) (v : Fin 3 → E)
    (hPv : ∀ a, P (v a) = EuclideanSpace.single a 1)
    {f : E → ℂ} {g : Fin 3 → E → ℂ} (hf : MemLp f 2) (hg : ∀ a, MemLp (g a) 2)
    (hweak : ∀ a (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ y, f y * Complex.ofReal (lineDeriv ℝ φ y (v a))) =
        -(∫ y, g a y * (φ y : ℂ))) :
    Integrable (fun x => ‖f x‖ ^ 2 / (4 * ‖P x‖ ^ 2)) ∧
      (∫ x, ‖f x‖ ^ 2 / (4 * ‖P x‖ ^ 2)) ≤ ∑ a, ∫ x, ‖g a x‖ ^ 2 := by
  obtain ⟨hi,hb⟩ := linear_hardy_integrable_bound P v hPv hf hg hweak
  have he : (fun x => ‖f x‖^2/(4*‖P x‖^2)) =
      fun x => (1/4:ℝ)*(‖f x‖^2/‖P x‖^2) := by funext x; ring
  rw [he]
  refine ⟨hi.const_mul _,?_⟩
  rw [integral_const_mul]
  linarith

open MeasureTheory Filter
open scoped Topology BigOperators

section

lemma sectorGraphPermutation_fixed {N : ℕ} (F : fermionGraph N)
    (π : Equiv.Perm (Fin N)) : sectorGraphPermutation π F.val = F.val := by
  apply sectorGraphValue_injective N
  rw [sectorGraphPermutation_value]
  exact (mem_fermionSpace _).mp F.property π

lemma sectorGraphPermutation_component {N : ℕ} (F : SectorGraph N)
    (π : Equiv.Perm (Fin N)) (s : Spins N) (k : Option (Fin N × Fin 3)) :
    ((sectorGraphPermutation π F) s).val k = (((Equiv.Perm.sign π : ℤ) : ℂ)) •
      Lp.compMeasurePreserving (permuteConfiguration π) (permuteConfiguration_preserving π)
        ((F (s ∘ π)).val (k.map fun j => (π.symm j.1,j.2))) := rfl

lemma complex_sign_norm {N : ℕ} (π : Equiv.Perm (Fin N)) :
    ‖(((Equiv.Perm.sign π : ℤ) : ℂ))‖ = 1 := by
  have hs := congrArg norm (complex_sign_sq π)
  rw [norm_pow, norm_one] at hs
  nlinarith [norm_nonneg (((Equiv.Perm.sign π : ℤ) : ℂ))]

lemma graphComponent_permutation_norm {N : ℕ} (F : fermionGraph N)
    (π : Equiv.Perm (Fin N)) (s : Spins N) (k : Option (Fin N × Fin 3)) :
    ∀ᵐ x : Configuration N, ‖graphComponent (s ∘ π)
      (k.map fun j => (π.symm j.1,j.2)) F (x ∘ π)‖ = ‖graphComponent s k F x‖ := by
  have he := congrArg (fun G : SectorGraph N => (G s).val k)
    (sectorGraphPermutation_fixed F π)
  rw [sectorGraphPermutation_component] at he
  have ha := Lp.coeFn_smul (((Equiv.Perm.sign π : ℤ) : ℂ))
    (Lp.compMeasurePreserving (permuteConfiguration π) (permuteConfiguration_preserving π)
      ((F.val (s ∘ π)).val (k.map fun j => (π.symm j.1,j.2))))
  have hb := Lp.coeFn_compMeasurePreserving
    ((F.val (s ∘ π)).val (k.map fun j => (π.symm j.1,j.2))) (permuteConfiguration_preserving π)
  rw [he] at ha
  filter_upwards [ha, hb] with x hx hy
  simp only [graphComponent_apply]
  rw [hx, Pi.smul_apply, norm_smul, complex_sign_norm, one_mul, hy]
  simp only [Function.comp_apply, permuteConfiguration_apply]

lemma graphComponent_permutation_integral {N : ℕ} (F : fermionGraph N)
    (π : Equiv.Perm (Fin N)) (s : Spins N) (k : Option (Fin N × Fin 3))
    (w : Configuration N → ℝ) :
    (∫ x, w x * ‖graphComponent (s ∘ π) (k.map fun j => (π.symm j.1,j.2)) F x‖ ^ 2) =
      ∫ x, w (x ∘ π) * ‖graphComponent s k F x‖ ^ 2 := by
  rw [← (permuteConfiguration_preserving π).integral_comp
    (permuteConfiguration π).toHomeomorph.measurableEmbedding
    (fun x => w x * ‖graphComponent (s ∘ π) (k.map fun j => (π.symm j.1,j.2)) F x‖ ^ 2)]
  apply integral_congr_ae
  filter_upwards [graphComponent_permutation_norm F π s k] with x hx
  simp only [permuteConfiguration_apply, hx]

lemma sum_spins_permutation {N : ℕ} (π : Equiv.Perm (Fin N)) (f : Spins N → ℝ) :
    (∑ s : Spins N, f (s ∘ π)) = ∑ s, f s := by
  let e : Spins N ≃ Spins N :=
    { toFun := fun s => s ∘ π
      invFun := fun s => s ∘ π.symm
      left_inv := fun s => by funext i; simp
      right_inv := fun s => by funext i; simp }
  exact Equiv.sum_comp e f

lemma graphComponent_permutation_sum_integral {N : ℕ} (F : fermionGraph N)
    (π : Equiv.Perm (Fin N)) (k : Option (Fin N × Fin 3))
    (w : Configuration N → ℝ) :
    (∑ s : Spins N, ∫ x, w x *
      ‖graphComponent s (k.map fun j => (π.symm j.1,j.2)) F x‖ ^ 2) =
      ∑ s : Spins N, ∫ x, w (x ∘ π) * ‖graphComponent s k F x‖ ^ 2 := by
  rw [← sum_spins_permutation π (fun s => ∫ x, w x *
    ‖graphComponent s (k.map fun j => (π.symm j.1,j.2)) F x‖ ^ 2)]
  exact Finset.sum_congr rfl (fun s _ => graphComponent_permutation_integral F π s k w)

def quantumEnergyDensity {N : ℕ} (Z : ℝ) (ψ : FormVector N) (s : Spins N)
    (x : Configuration N) : ℝ :=
  (1/2:ℝ) * (∑ i, ∑ a, ‖ψ.gradient s i a x‖ ^ 2) -
    Z * (∑ i, ‖ψ.value s x‖ ^ 2 / ‖x i‖) +
    (1/2:ℝ) * (∑ i, ∑ j, if i ≠ j then ‖ψ.value s x‖ ^ 2 / ‖x i-x j‖ else 0)

lemma SobolevFermion.quantumEnergyDensity_integrable {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (Z : ℝ) (s : Spins N) :
    Integrable (quantumEnergyDensity Z ψ s) := by
  classical
  have hn (i : Fin N) := nuclear_integrable i (hψ.1 s) (hψ.2.1 s i) (hψ.2.2.1 s i)
  have hp (i j : Fin N) (hij : i ≠ j) := pair_integrable i j hij (hψ.1 s)
    (hψ.2.1 s i) (hψ.2.2.1 s i)
  apply Integrable.add
  · exact ((integrable_finsetSum _ (fun i _ => integrable_finsetSum _
      (fun a _ => (hψ.2.1 s i a).norm.integrable_sq))).const_mul _).sub
      ((integrable_finsetSum _ (fun i _ => hn i)).const_mul _)
  · apply Integrable.const_mul
    apply integrable_finsetSum; intro i _
    apply integrable_finsetSum; intro j _
    split_ifs with hij
    · exact hp i j hij
    · exact integrable_zero _ _ _

lemma formEnergy_eq_density {N : ℕ} {ψ : FormVector N} (hψ : SobolevFermion ψ) (Z : ℝ) :
    formEnergy Z ψ = ∑ s, ∫ x, quantumEnergyDensity Z ψ s x := by
  classical
  have hn (s : Spins N) (i : Fin N) := nuclear_integrable i (hψ.1 s)
    (hψ.2.1 s i) (hψ.2.2.1 s i)
  have hp (s : Spins N) (i j : Fin N) : Integrable (fun x =>
      if i ≠ j then ‖ψ.value s x‖ ^ 2 / ‖x i-x j‖ else 0) := by
    split_ifs with hij
    · exact pair_integrable i j hij (hψ.1 s) (hψ.2.1 s i) (hψ.2.2.1 s i)
    · exact integrable_zero _ _ _
  have hk (s : Spins N) := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun a _ => (hψ.2.1 s i a).norm.integrable_sq))
  have hns (s : Spins N) := integrable_finsetSum Finset.univ (fun i _ => hn s i)
  have hps (s : Spins N) := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hp s i j))
  have he (s : Spins N) : (∫ x, quantumEnergyDensity Z ψ s x) =
      (1/2:ℝ) * (∑ i, ∑ a, ∫ x, ‖ψ.gradient s i a x‖ ^ 2) -
      Z * (∑ i, ∫ x, ‖ψ.value s x‖ ^ 2 / ‖x i‖) +
      (1/2:ℝ) * (∑ i, ∑ j, ∫ x,
        if i ≠ j then ‖ψ.value s x‖ ^ 2 / ‖x i-x j‖ else 0) := by
    unfold quantumEnergyDensity
    have hsum := integral_add (((hk s).const_mul (1/2:ℝ)).sub ((hns s).const_mul Z))
      ((hps s).const_mul (1/2:ℝ))
    have hsub := integral_sub ((hk s).const_mul (1/2:ℝ)) ((hns s).const_mul Z)
    simp only [Pi.sub_apply] at hsum hsub
    rw [hsum, hsub]
    simp only [integral_const_mul]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun a _ =>
      (hψ.2.1 s i a).norm.integrable_sq)), integral_finsetSum _ (fun i _ => hn s i),
      integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hp s i j))]
    simp_rw [integral_finsetSum _ (fun a _ => (hψ.2.1 s _ a).norm.integrable_sq),
      integral_finsetSum _ (fun j _ => hp s _ j)]
  simp_rw [he]
  have hint (s : Spins N) (i j : Fin N) :
      (∫ x, if i ≠ j then ‖ψ.value s x‖ ^ 2 / ‖x i-x j‖ else 0) =
      if i ≠ j then (∫ x, ‖ψ.value s x‖ ^ 2 / ‖x i-x j‖) else 0 := by
    split_ifs <;> simp
  simp_rw [hint]
  have hs (s : Spins N) (i j : Fin N) :
      (∫ x, ‖ψ.value s x‖ ^ 2 / ‖x i-x j‖) =
      ∫ x, ‖ψ.value s x‖ ^ 2 / ‖x j-x i‖ := by simp only [norm_sub_rev]
  simp_rw [← sum_pairs_half _ (hs _) ]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rfl

def quantumCoreDensity {N : ℕ} (Z : ℝ) (ψ : FormVector N) (i : Fin N) (s : Spins N)
    (x : Configuration N) : ℝ :=
  (1/2:ℝ) * (∑ j, if j ≠ i then ∑ a, ‖ψ.gradient s j a x‖ ^ 2 else 0) -
    Z * (∑ j, if j ≠ i then ‖ψ.value s x‖ ^ 2 / ‖x j‖ else 0) +
    (1/2:ℝ) * (∑ j, ∑ k,
      if j ≠ i ∧ k ≠ i ∧ j ≠ k then ‖ψ.value s x‖ ^ 2 / ‖x j-x k‖ else 0)

lemma SobolevFermion.quantumCoreDensity_integrable {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (Z : ℝ) (i : Fin N) (s : Spins N) :
    Integrable (quantumCoreDensity Z ψ i s) := by
  classical
  have hk : Integrable (fun x => ∑ j, if j ≠ i then ∑ a, ‖ψ.gradient s j a x‖ ^ 2 else 0) := by
    apply integrable_finsetSum; intro j _
    split_ifs
    · exact integrable_finsetSum _ (fun a _ => (hψ.2.1 s j a).norm.integrable_sq)
    · exact integrable_zero _ _ _
  have hn : Integrable (fun x => ∑ j, if j ≠ i then ‖ψ.value s x‖ ^ 2 / ‖x j‖ else 0) := by
    apply integrable_finsetSum; intro j _
    split_ifs
    · exact nuclear_integrable j (hψ.1 s) (hψ.2.1 s j) (hψ.2.2.1 s j)
    · exact integrable_zero _ _ _
  have hp : Integrable (fun x => ∑ j, ∑ k,
      if j ≠ i ∧ k ≠ i ∧ j ≠ k then ‖ψ.value s x‖ ^ 2 / ‖x j-x k‖ else 0) := by
    apply integrable_finsetSum; intro j _
    apply integrable_finsetSum; intro k _
    split_ifs with hij
    · exact pair_integrable j k hij.2.2 (hψ.1 s) (hψ.2.1 s j) (hψ.2.2.1 s j)
    · exact integrable_zero _ _ _
  exact ((hk.const_mul _).sub (hn.const_mul _)).add (hp.const_mul _)

def exteriorCoordinates {N M : ℕ} (x : Configuration (N+M)) : Configuration M :=
  fun j => x (finSumFinEquiv (Sum.inr j))

lemma exteriorCoordinates_join {N M : ℕ} (x : Configuration N) (y : Configuration M) :
    exteriorCoordinates (joinLists x y) = y := by
  funext j
  exact joinLists_right x y j

lemma exteriorCoordinates_continuous {N M : ℕ} :
    Continuous (@exteriorCoordinates N M) := by
  apply continuous_pi; intro j
  exact continuous_apply _

lemma weighted_integral_join {N M : ℕ} {f : Configuration (N+M) → ℝ}
    (hf : Integrable f) (w : Configuration M → ℝ) (hw : Continuous w)
    {C : ℝ} (hwC : ∀ y, ‖w y‖ ≤ C) :
    (∫ y : Configuration M, w y * ∫ x : Configuration N, f (joinLists x y)) =
      ∫ z, w (exteriorCoordinates z) * f z := by
  have hg : Integrable (fun z => w (exteriorCoordinates z) * f z) :=
    hf.bdd_mul (hw.comp exteriorCoordinates_continuous).aestronglyMeasurable
      (Eventually.of_forall fun z => hwC _)
  rw [← integral_join (N := N) (M := M) hg]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    simp only [exteriorCoordinates_join, integral_const_mul]

lemma weighted_sum_integral_join {N M : ℕ} {f : Spins (N+M) → Configuration (N+M) → ℝ}
    (hf : ∀ u, Integrable (f u)) (w : Configuration M → ℝ) (hw : Continuous w)
    {C : ℝ} (hwC : ∀ y, ‖w y‖ ≤ C) :
    (∑ t : Spins M, ∫ y, w y * (∑ s : Spins N, ∫ x, f (joinLists s t) (joinLists x y))) =
      ∑ u : Spins (N+M), ∫ z, w (exteriorCoordinates z) * f u z := by
  have hi (s : Spins N) (t : Spins M) :
      Integrable (fun y : Configuration M => w y * ∫ x : Configuration N,
        f (joinLists s t) (joinLists x y)) :=
    (integrable_join (hf (joinLists s t))).integral_prod_right.bdd_mul
      hw.aestronglyMeasurable (Eventually.of_forall hwC)
  simp_rw [Finset.mul_sum, integral_finsetSum _ (fun s _ => hi s _),
    weighted_integral_join (hf _) w hw hwC]
  exact sum_spin_join (fun u => ∫ z, w (exteriorCoordinates z) * f u z)

lemma quantumCoreDensity_last {N : ℕ} (Z : ℝ) (ψ : FormVector (N+1))
    (s : Spins N) (t : Spins 1) (x : Configuration N) (y : Configuration 1) :
    quantumCoreDensity Z ψ (Fin.last N) (joinLists s t) (joinLists x y) =
      quantumEnergyDensity Z (coreSlice ψ t y) s x := by
  classical
  unfold quantumCoreDensity quantumEnergyDensity
  simp only [Fin.sum_univ_castSucc, ne_eq, not_true_eq_false, ite_false, Fin.castSucc_ne_last,
    not_false_eq_true, ite_true, add_zero, and_false, and_true, Fin.castSucc_inj]
  simp only [true_and, false_and, ite_false, Finset.sum_const_zero, add_zero]
  have hl (i : Fin N) : joinLists x y i.castSucc = x i := joinLists_left x y i
  simp only [hl, coreSlice, finSumFinEquiv_apply_left]
  rfl

lemma coreSlice_energy_weighted_reconstruction {N : ℕ} {ψ : FormVector (N+1)}
    (hψ : SobolevFermion ψ) (Z : ℝ) (w : Configuration 1 → ℝ) (hw : Continuous w)
    {C : ℝ} (hwC : ∀ y, ‖w y‖ ≤ C) :
    (∑ t : Spins 1, ∫ y, w y * formEnergy Z (coreSlice ψ t y)) =
      ∑ s : Spins (N+1), ∫ z, w (exteriorCoordinates z) * quantumCoreDensity Z ψ (Fin.last N) s z := by
  rw [← weighted_sum_integral_join
    (fun s => hψ.quantumCoreDensity_integrable Z (Fin.last N) s) w hw hwC]
  apply Finset.sum_congr rfl
  intro t _
  apply integral_congr_ae
  filter_upwards [hψ.ae_coreSlice t] with y hy
  rw [formEnergy_eq_density hy]
  simp only [quantumCoreDensity_last]

lemma coreSlice_mass_weighted_reconstruction {N : ℕ} {ψ : FormVector (N+1)}
    (hψ : SobolevFermion ψ) (w : Configuration 1 → ℝ) (hw : Continuous w)
    {C : ℝ} (hwC : ∀ y, ‖w y‖ ≤ C) :
    (∑ t : Spins 1, ∫ y, w y * formMass (coreSlice ψ t y)) =
      ∑ s : Spins (N+1), ∫ z, w (exteriorCoordinates z) * ‖ψ.value s z‖ ^ 2 := by
  exact weighted_sum_integral_join (fun s => (hψ.1 s).norm.integrable_sq) w hw hwC

lemma weighted_core_last {N : ℕ} {ψ : FormVector (N+1)} (hψ : SobolevFermion ψ)
    {Z : ℝ} (hZ : 0 ≤ Z) (w : Configuration 1 → ℝ) (hw : Continuous w)
    (hw0 : ∀ y, 0 ≤ w y) {C : ℝ} (hwC : ∀ y, ‖w y‖ ≤ C) :
    energy Z N * (∑ s, ∫ z, w (exteriorCoordinates z) * ‖ψ.value s z‖ ^ 2) ≤
      ∑ s, ∫ z, w (exteriorCoordinates z) * quantumCoreDensity Z ψ (Fin.last N) s z := by
  rw [← coreSlice_mass_weighted_reconstruction hψ w hw hwC,
    ← coreSlice_energy_weighted_reconstruction hψ Z w hw hwC]
  exact weighted_core_energy hψ hZ w hw.aestronglyMeasurable
    (Eventually.of_forall hw0) (Eventually.of_forall hwC)

lemma graphFormVector_value_eq {N : ℕ} (F : fermionGraph N) (s : Spins N) (x : Configuration N) :
    (graphFormVector F).value s x = graphComponent s none F x := rfl

lemma graphFormVector_gradient_eq {N : ℕ} (F : fermionGraph N) (s : Spins N)
    (i : Fin N) (a : Fin 3) (x : Configuration N) :
    (graphFormVector F).gradient s i a x = graphComponent s (some (i,a)) F x := rfl

attribute [local irreducible] graphComponent graphFormVector

lemma sum_excluding_perm {α : Type*} [Fintype α] [DecidableEq α]
    (π : Equiv.Perm α) (i : α) (f : α → ℝ) :
    (∑ j, if j ≠ i then f (π j) else 0) = ∑ j, if j ≠ π i then f j else 0 := by
  rw [← Equiv.sum_comp π (fun j => if j ≠ π i then f j else 0)]
  simp only [ne_eq, π.injective.eq_iff]

lemma sum_pairs_excluding_perm {α : Type*} [Fintype α] [DecidableEq α]
    (π : Equiv.Perm α) (i : α) (f : α → α → ℝ) :
    (∑ j, ∑ k, if j ≠ i ∧ k ≠ i ∧ j ≠ k then f (π j) (π k) else 0) =
      ∑ j, ∑ k, if j ≠ π i ∧ k ≠ π i ∧ j ≠ k then f j k else 0 := by
  rw [← Equiv.sum_comp π (fun j => ∑ k,
    if j ≠ π i ∧ k ≠ π i ∧ j ≠ k then f j k else 0)]
  apply Finset.sum_congr rfl; intro j _
  rw [← Equiv.sum_comp π (fun k =>
    if π j ≠ π i ∧ k ≠ π i ∧ π j ≠ k then f (π j) k else 0)]
  simp only [ne_eq, π.injective.eq_iff]

lemma quantumCoreDensity_reindex {N : ℕ} (Z : ℝ) (ψ φ : FormVector N)
    (π : Equiv.Perm (Fin N)) (i : Fin N) (s t : Spins N) (x y : Configuration N)
    (hv : ‖φ.value t y‖ = ‖ψ.value s x‖)
    (hg : ∀ j a, ‖φ.gradient t j a y‖ = ‖ψ.gradient s (π j) a x‖)
    (hc : ∀ j, y j = x (π j)) :
    quantumCoreDensity Z φ i t y = quantumCoreDensity Z ψ (π i) s x := by
  classical
  unfold quantumCoreDensity
  simp only [hg, hv, hc]
  rw [sum_excluding_perm π i (fun j => ∑ a, ‖ψ.gradient s j a x‖ ^ 2),
    sum_excluding_perm π i (fun j => ‖ψ.value s x‖ ^ 2 / ‖x j‖),
    sum_pairs_excluding_perm π i (fun j k => ‖ψ.value s x‖ ^ 2 / ‖x j-x k‖)]

lemma graphFormVector_permutation_norm {N : ℕ} (F : fermionGraph N)
    (π : Equiv.Perm (Fin N)) (s : Spins N) :
    ∀ᵐ x : Configuration N,
      ‖(graphFormVector F).value (s ∘ π) (x ∘ π)‖ = ‖(graphFormVector F).value s x‖ ∧
      ∀ j a, ‖(graphFormVector F).gradient (s ∘ π) j a (x ∘ π)‖ =
        ‖(graphFormVector F).gradient s (π j) a x‖ := by
  have hg (j : Fin N) (a : Fin 3) : ∀ᵐ x : Configuration N,
      ‖(graphFormVector F).gradient (s ∘ π) j a (x ∘ π)‖ =
        ‖(graphFormVector F).gradient s (π j) a x‖ := by
    simpa only [graphFormVector_gradient_eq, Option.map_some, Equiv.symm_apply_apply]
      using graphComponent_permutation_norm F π s (some (π j,a))
  have hv : ∀ᵐ x : Configuration N,
      ‖(graphFormVector F).value (s ∘ π) (x ∘ π)‖ = ‖(graphFormVector F).value s x‖ := by
    simpa only [graphFormVector_value_eq, Option.map_none] using graphComponent_permutation_norm F π s none
  exact hv.and (ae_all_iff.mpr fun j => ae_all_iff.mpr fun a => hg j a)

lemma quantumCoreDensity_permutation {N : ℕ} (Z : ℝ) (F : fermionGraph N)
    (π : Equiv.Perm (Fin N)) (i : Fin N) (s : Spins N) :
    ∀ᵐ x : Configuration N,
      quantumCoreDensity Z (graphFormVector F) i (s ∘ π) (x ∘ π) =
      quantumCoreDensity Z (graphFormVector F) (π i) s x := by
  filter_upwards [graphFormVector_permutation_norm F π s] with x hx
  exact quantumCoreDensity_reindex Z _ _ π i s (s ∘ π) x (x ∘ π) hx.1 hx.2 (fun _ => rfl)

lemma weighted_core_permutation {N : ℕ} (Z : ℝ) (F : fermionGraph N)
    (π : Equiv.Perm (Fin N)) (i : Fin N) (w : Space → ℝ) :
    (∑ s, ∫ x, w (x i) * quantumCoreDensity Z (graphFormVector F) i s x) =
      ∑ s, ∫ x, w (x (π i)) * quantumCoreDensity Z (graphFormVector F) (π i) s x := by
  rw [← sum_spins_permutation π (fun s => ∫ x, w (x i) *
    quantumCoreDensity Z (graphFormVector F) i s x)]
  apply Finset.sum_congr rfl; intro s _
  rw [← (permuteConfiguration_preserving π).integral_comp
    (permuteConfiguration π).toHomeomorph.measurableEmbedding
    (fun x => w (x i) * quantumCoreDensity Z (graphFormVector F) i (s ∘ π) x)]
  apply integral_congr_ae
  filter_upwards [quantumCoreDensity_permutation Z F π i s] with x hx
  simp only [permuteConfiguration_apply, Function.comp_apply, hx]

lemma weighted_core_coordinate {N : ℕ} (F : fermionGraph (N+1)) {Z : ℝ} (hZ : 0 ≤ Z)
    (i : Fin (N+1)) (w : Space → ℝ) (hw : Continuous w) (hw0 : ∀ y, 0 ≤ w y)
    {C : ℝ} (hwC : ∀ y, ‖w y‖ ≤ C) :
    energy Z N * (∑ s, ∫ x, w (x i) * ‖graphComponent s none F x‖ ^ 2) ≤
      ∑ s, ∫ x, w (x i) * quantumCoreDensity Z (graphFormVector F) i s x := by
  classical
  have hh := weighted_core_last (graphFormVector_sobolev F) hZ
    (fun y => w (y 0)) (hw.comp (continuous_apply 0)) (fun y => hw0 (y 0))
    (fun y => hwC (y 0))
  have he (x : Configuration (N+1)) : exteriorCoordinates x 0 = x (Fin.last N) := rfl
  simp only [he, graphFormVector_value_eq] at hh
  let π : Equiv.Perm (Fin (N+1)) := Equiv.swap (Fin.last N) i
  have hi : π (Fin.last N) = i := Equiv.swap_apply_left _ _
  rw [weighted_core_permutation Z F π (Fin.last N) w, hi] at hh
  have hm := graphComponent_permutation_sum_integral F π none
    (fun x => w (x (Fin.last N)))
  simp only [Option.map_none, Function.comp_apply, hi] at hm
  rw [hm] at hh
  exact hh

end

lemma sum_excluding_add {α : Type*} [Fintype α] [DecidableEq α] (i : α) (f : α → ℝ) :
    (∑ j, if j ≠ i then f j else 0) + f i = ∑ j, f j := by
  have hh (j : α) : (if j ≠ i then f j else 0) + (if j = i then f j else 0) = f j := by
    by_cases h : j = i <;> simp [h]
  simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using
    Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun j _ => hh j)

lemma pairs_excluding_add {α : Type*} [Fintype α] [DecidableEq α] (i : α)
    (f : α → α → ℝ) (hs : ∀ j k, f j k = f k j) (hii : f i i = 0) :
    (∑ j, ∑ k, if j ≠ i ∧ k ≠ i then f j k else 0) + 2 * (∑ k, f i k) =
      ∑ j, ∑ k, f j k := by
  have hinner (j : α) : (∑ k, if k ≠ i then f j k else 0) + f j i = ∑ k, f j k :=
    sum_excluding_add i (f j)
  have houter := sum_excluding_add i (fun j => ∑ k, if k ≠ i then f j k else 0)
  have hr := sum_excluding_add i (f i)
  rw [hii, add_zero] at hr
  have hc : (∑ j, f j i) = ∑ j, f i j := Finset.sum_congr rfl (fun j _ => hs j i)
  have hd : (∑ j, if j ≠ i then ∑ k, if k ≠ i then f j k else 0 else 0) =
      ∑ j, ∑ k, if j ≠ i ∧ k ≠ i then f j k else 0 := by
    apply Finset.sum_congr rfl; intro j _
    by_cases h : j = i <;> simp [h]
  rw [hd, hr] at houter
  have he := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun j _ => hinner j)
  rw [Finset.sum_add_distrib, hc] at he
  linarith

lemma quantumEnergyDensity_delete {N : ℕ} (Z : ℝ) (ψ : FormVector N)
    (i : Fin N) (s : Spins N) (x : Configuration N) :
    quantumEnergyDensity Z ψ s x = quantumCoreDensity Z ψ i s x +
      (1/2:ℝ) * (∑ a, ‖ψ.gradient s i a x‖ ^ 2) - Z * (‖ψ.value s x‖ ^ 2 / ‖x i‖) +
      (∑ j, if i ≠ j then ‖ψ.value s x‖ ^ 2 / ‖x i-x j‖ else 0) := by
  classical
  have hk := sum_excluding_add i (fun j => ∑ a, ‖ψ.gradient s j a x‖ ^ 2)
  have hn := sum_excluding_add i (fun j => ‖ψ.value s x‖ ^ 2 / ‖x j‖)
  let f := fun j k : Fin N => if j ≠ k then ‖ψ.value s x‖ ^ 2 / ‖x j-x k‖ else 0
  have hs (j k : Fin N) : f j k = f k j := by
    dsimp [f]
    by_cases h : j = k
    · simp [h]
    · simp [h, Ne.symm h, norm_sub_rev]
  have hp := pairs_excluding_add i f hs (by simp [f])
  have he (j k : Fin N) : (if j ≠ i ∧ k ≠ i then f j k else 0) =
      if j ≠ i ∧ k ≠ i ∧ j ≠ k then ‖ψ.value s x‖ ^ 2 / ‖x j-x k‖ else 0 := by
    simp only [f]; split_ifs <;> simp_all
  simp only [he] at hp
  unfold quantumEnergyDensity quantumCoreDensity
  change _ = _
  dsimp only [f] at hp
  rw [← hk, ← hn, ← hp]
  ring


open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

end CoulombAtom

end

end OAI
