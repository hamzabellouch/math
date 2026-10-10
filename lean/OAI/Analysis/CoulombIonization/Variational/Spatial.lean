import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.QuantumSectorNearMinimizer
import OAI.Analysis.CoulombIonization.FormDomain.Forms

namespace OAI

noncomputable section

namespace CoulombAtom

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
section
variable {N : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)

lemma spatial_coordinate_derivative (b : Fin 2) (i j : Fin N) (a : Fin 3)
    (x : Configuration N) :
    lineDeriv ℝ (fun y : Configuration N => (p b).value (y i)) x (direction j a) =
      if j = i then lineDeriv ℝ (p b).value (x i) (spaceDirections a) else 0 := by
  classical
  have h := ((p b).regular.differentiable (by simp) (x i)).hasFDerivAt.comp
    x (electronProjection i).hasFDerivAt
  change HasFDerivAt (fun y : Configuration N => (p b).value (y i)) _ x at h
  rw [h.differentiableAt.lineDeriv_eq_fderiv, h.fderiv]
  change fderiv ℝ (p b).value (x i) (direction j a i) = _
  by_cases hij : j = i
  · subst j
    simp only [↓reduceIte, direction, Pi.single_eq_same, spaceDirections]
    exact ((p b).regular.differentiable (by simp) (x i)).lineDeriv_eq_fderiv.symm
  · simp [direction, hij, Ne.symm hij]

def spatialProductValue (b : Fin N → Fin 2) (x : Configuration N) : ℝ :=
  ∏ i, (p (b i)).value (x i)

lemma spatialProduct_regular (b : Fin N → Fin 2) :
    ContDiff ℝ ∞ (spatialProductValue p b) :=
  contDiff_prod fun i _ => (p (b i)).regular.comp (electronProjection i).contDiff

lemma spatialProduct_derivative (b : Fin N → Fin 2) (i : Fin N) (a : Fin 3)
    (x : Configuration N) :
    lineDeriv ℝ (spatialProductValue p b) x (direction i a) =
      (∏ k ∈ Finset.univ.erase i, (p (b k)).value (x k)) *
        lineDeriv ℝ (p (b i)).value (x i) (spaceDirections a) := by
  classical
  have hg (k : Fin N) := ((p (b k)).regular.differentiable (by simp) (x k)).hasFDerivAt.comp
    x (electronProjection k).hasFDerivAt
  have hh := HasFDerivAt.finsetProd (u := Finset.univ) (fun k _ => hg k)
  change HasFDerivAt (spatialProductValue p b) _ x at hh
  rw [hh.differentiableAt.lineDeriv_eq_fderiv, hh.fderiv]
  simp only [sum_apply, smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · congr 1
    change fderiv ℝ (p (b i)).value (x i) (direction i a i) = _
    rw [direction, Pi.single_eq_same]
    exact ((p (b i)).regular.differentiable (by simp) (x i)).lineDeriv_eq_fderiv.symm
  · intro k _ hki
    change _ * fderiv ℝ (p (b k)).value (x k) (direction i a k) = 0
    simp [direction, hki]
  · simp

variable (hp : ∀ x, ∑ h : Fin 2, (p h).value x ^ 2 = 1)
include hp

lemma spatial_factor_bound (h : Fin 2) (x : Space) : |(p h).value x| ≤ 1 := by
  have hh : (p h).value x ^ 2 ≤ 1 := by
    rw [← hp x]
    exact Finset.single_le_sum (f := fun j : Fin 2 => (p j).value x ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ h)
  nlinarith [sq_abs ((p h).value x), abs_nonneg ((p h).value x)]

lemma spatial_product_sub_bound (b : Fin N → Fin 2) (x : Configuration N)
    (s : Finset (Fin N)) : |∏ i ∈ s, (p (b i)).value (x i)| ≤ 1 := by
  rw [Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun _ _ => spatial_factor_bound p hp _ _)

def spatialProduct (b : Fin N → Fin 2) : SmoothMultiplier (sectorDirections N) where
  value := spatialProductValue p b
  regular := spatialProduct_regular p b
  bound := ⟨1, fun x => spatial_product_sub_bound p hp b x Finset.univ⟩
  gradient_bound := by
    intro j
    obtain ⟨C,hC⟩ := (p (b j.1)).gradient_bound j.2
    refine ⟨C, fun x => ?_⟩
    change |lineDeriv ℝ (spatialProductValue p b) x (direction j.1 j.2)| ≤ C
    rw [spatialProduct_derivative, abs_mul]
    exact (mul_le_mul_of_nonneg_right (spatial_product_sub_bound p hp b x _)
      (abs_nonneg _)).trans (by simpa only [one_mul] using hC (x j.1))

lemma spatial_square_partition (x : Configuration N) :
    ∑ b : Fin N → Fin 2, (spatialProduct p hp b).value x ^ 2 = 1 := by
  change (∑ b : Fin N → Fin 2, (∏ i, (p (b i)).value (x i)) ^ 2) = 1
  simp_rw [← Finset.prod_pow]
  rw [← Fintype.prod_sum (f := fun (i : Fin N) (b : Fin 2) => (p b).value (x i) ^ 2)]
  simp only [hp, Finset.prod_const_one]

theorem spatial_cut_mass {ψ : FormVector N} (hψ : SobolevVector ψ) :
    ∑ b : Fin N → Fin 2, formMass (multiplyForm (spatialProduct p hp b) ψ) = formMass ψ :=
  finite_partition_mass (spatialProduct p hp) (spatial_square_partition p hp) hψ

theorem spatial_cut_energy {ψ : FormVector N} (hψ : SobolevVector ψ) (Z : ℝ) :
    (∑ b : Fin N → Fin 2, formEnergy Z (multiplyForm (spatialProduct p hp b) ψ)) =
      formEnergy Z ψ + ∑ b : Fin N → Fin 2, formMultiplierError (spatialProduct p hp b) ψ :=
  finite_partition_energy (spatialProduct p hp) (spatial_square_partition p hp) hψ Z

end

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

def CoreAntisymmetric {N M : ℕ} (ψ : FormVector (N+M)) : Prop :=
  ∀ (π : Equiv.Perm (Fin N)) (s : Spins (N+M)), ∀ᵐ x,
    ψ.value (s ∘ corePerm M π) (x ∘ corePerm M π) =
      (((Equiv.Perm.sign π : ℤ) : ℂ) * ψ.value s x)

lemma SobolevFermion.coreAntisymmetric {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevFermion ψ) : CoreAntisymmetric ψ := by
  intro π s
  simpa only [corePerm_sign] using hψ.2.2.2 (corePerm M π) s

theorem SobolevVector.ae_coreSlice {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) : ∀ᵐ y, SobolevVector (coreSlice ψ t y) := by
  have hv (s : Spins N) : ∀ᵐ y, MemLp ((coreSlice ψ t y).value s) 2 := by
    have hh := (hψ.1 (joinLists s t)).comp_measurePreserving (configurationJoin_preserving N M)
    simpa only [Function.comp_apply, configurationJoin_apply, coreSlice] using memLp_slice_left hh
  have hg (s : Spins N) (i : Fin N) (a : Fin 3) :
      ∀ᵐ y, MemLp ((coreSlice ψ t y).gradient s i a) 2 := by
    have hh := (hψ.2.1 (joinLists s t) (finSumFinEquiv (Sum.inl i)) a).comp_measurePreserving
      (configurationJoin_preserving N M)
    simpa only [Function.comp_apply, configurationJoin_apply, coreSlice] using memLp_slice_left hh
  have hw (s : Spins N) (i : Fin N) (a : Fin 3) :
      ∀ᵐ y, IsWeakDerivative (direction i a) ((coreSlice ψ t y).value s)
        ((coreSlice ψ t y).gradient s i a) := by
    have hh := (hψ.2.2 (joinLists s t) (finSumFinEquiv (Sum.inl i)) a).pullback
      (configurationJoin N M) (configurationJoin_preserving N M) (configurationJoin_direction i a)
    simpa only [Function.comp_apply, configurationJoin_apply, coreSlice] using hh.slice_left
      ((hψ.1 (joinLists s t)).comp_measurePreserving (configurationJoin_preserving N M))
      ((hψ.2.1 (joinLists s t) (finSumFinEquiv (Sum.inl i)) a).comp_measurePreserving
        (configurationJoin_preserving N M))
  filter_upwards [ae_all_iff.mpr hv, ae_all_iff.mpr (fun s => ae_all_iff.mpr
      (fun i => ae_all_iff.mpr (hg s i))), ae_all_iff.mpr (fun s => ae_all_iff.mpr
      (fun i => ae_all_iff.mpr (hw s i)))] with y hyv hyg hyw
  exact ⟨hyv,hyg,hyw⟩

theorem CoreAntisymmetric.ae_coreSlice {N M : ℕ} {ψ : FormVector (N+M)}
    (ha : CoreAntisymmetric ψ) (hψ : SobolevVector ψ) (t : Spins M) :
    ∀ᵐ y, SobolevFermion (coreSlice ψ t y) := by
  have hs (π : Equiv.Perm (Fin N)) (s : Spins N) : ∀ᵐ y, ∀ᵐ x,
      (coreSlice ψ t y).value (s ∘ π) (x ∘ π) =
        (((Equiv.Perm.sign π : ℤ) : ℂ) * (coreSlice ψ t y).value s x) := by
    have hh := (configurationJoin_preserving N M).quasiMeasurePreserving.ae
      (ha π (joinLists s t))
    have hh' : ∀ᵐ z : Configuration N × Configuration M,
        (coreSlice ψ t z.2).value (s ∘ π) (z.1 ∘ π) =
          (((Equiv.Perm.sign π : ℤ) : ℂ) * (coreSlice ψ t z.2).value s z.1) := by
      filter_upwards [hh] with z hz
      rcases z with ⟨x,y⟩
      simpa only [configurationJoin_apply, joinLists_corePerm, coreSlice] using hz
    rw [Measure.volume_eq_prod] at hh'
    exact Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hh')
  filter_upwards [hψ.ae_coreSlice t, ae_all_iff.mpr (fun π => ae_all_iff.mpr (hs π))]
    with y hy hya
  exact ⟨hy.1,hy.2.1,hy.2.2,hya⟩

lemma CoreAntisymmetric.multiply {N M : ℕ} {ψ : FormVector (N+M)}
    (ha : CoreAntisymmetric ψ) (q : SmoothMultiplier (sectorDirections (N+M)))
    (hq : ∀ (π : Equiv.Perm (Fin N)) x, q.value (x ∘ corePerm M π) = q.value x) :
    CoreAntisymmetric (multiplyForm q ψ) := by
  intro π s
  filter_upwards [ha π s] with x hx
  change (q.value (x ∘ corePerm M π) : ℂ) * ψ.value (s ∘ corePerm M π)
    (x ∘ corePerm M π) = _ * ((q.value x : ℂ) * ψ.value s x)
  rw [hq, hx]
  ring

lemma spatialProduct_invariant {N : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (b : Fin N → Fin 2) (π : Equiv.Perm (Fin N)) (hb : b ∘ π = b) (x : Configuration N) :
    spatialProductValue p b (x ∘ π) = spatialProductValue p b x := by
  unfold spatialProductValue
  have hh : (∏ i, (p (b i)).value ((x ∘ π) i)) =
      ∏ i, (p (b (π i))).value (x (π i)) := by
    apply Finset.prod_congr rfl
    intro i _
    rw [show b (π i) = b i from congrFun hb i]
    rfl
  exact hh.trans (Equiv.prod_comp π (fun i => (p (b i)).value (x i)))

def coreCutLabels (N M : ℕ) : Fin (N+M) → Fin 2 :=
  joinLists (fun _ : Fin N => 0) (fun _ : Fin M => 1)

lemma coreCutLabels_invariant {N M : ℕ} (π : Equiv.Perm (Fin N)) :
    coreCutLabels N M ∘ corePerm M π = coreCutLabels N M := by
  unfold coreCutLabels
  rw [joinLists_corePerm]
  rfl

theorem spatial_coreSlice_fermion {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevFermion ψ) (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ h : Fin 2, (p h).value x ^ 2 = 1) (t : Spins M) :
    ∀ᵐ y, SobolevFermion
      (coreSlice (multiplyForm (spatialProduct p hp (coreCutLabels N M)) ψ) t y) := by
  apply CoreAntisymmetric.ae_coreSlice
  · apply hψ.coreAntisymmetric.multiply
    intro π x
    exact spatialProduct_invariant p _ (corePerm M π) (coreCutLabels_invariant π) x
  · exact hψ.sobolevVector.multiply _

theorem spatial_coreSlice_priced {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevFermion ψ) (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ h : Fin 2, (p h).value x ^ 2 = 1) (t : Spins M)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    ∀ᵐ y, let q := coreSlice (multiplyForm (spatialProduct p hp (coreCutLabels N M)) ψ) t y
      priceEnergy (energy Z) lam * formMass q ≤ formEnergy Z q + lam * N * formMass q :=
  (spatial_coreSlice_fermion hψ p hp t).mono fun _ h => h.priced_lower_bound hZ hlam

lemma binary_product_square_sum {N : ℕ} (q : Fin N → Fin 2 → ℝ)
    (hq : ∀ k, ∑ h, q k h ^ 2 = 1) (i : Fin N) (r : Fin 2 → ℝ) :
    (∑ b : Fin N → Fin 2, ((∏ k ∈ Finset.univ.erase i, q k (b k)) * r (b i)) ^ 2) =
      ∑ h : Fin 2, r h ^ 2 := by
  classical
  have he (b : Fin N → Fin 2) :
      ((∏ k ∈ Finset.univ.erase i, q k (b k)) * r (b i)) ^ 2 =
        ∏ k : Fin N, if k = i then r (b k) ^ 2 else q k (b k) ^ 2 := by
    rw [mul_pow, ← Finset.prod_pow]
    rw [← Finset.prod_erase_mul Finset.univ
      (fun k => if k = i then r (b k) ^ 2 else q k (b k) ^ 2) (Finset.mem_univ i)]
    simp only [↓reduceIte]
    congr 1
    apply Finset.prod_congr rfl
    intro k hk
    exact (ite_eq_right (Finset.mem_erase.mp hk).1).symm
  simp_rw [he]
  rw [← Fintype.prod_sum (f := fun (k : Fin N) (h : Fin 2) =>
    if k = i then r h ^ 2 else q k h ^ 2)]
  rw [Finset.prod_eq_single i]
  · simp
  · intro k _ hki
    simpa only [ite_eq_right hki] using hq k
  · simp

end CoulombAtom

end

end OAI
