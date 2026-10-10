import Mathlib
import OAI.Analysis.Conductivity.Flux.TwoFluxColumns

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity

section

theorem exists_adapted_spatial_basis
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (hdim : Module.finrank ℝ E = 3)
    (D : E →L[ℝ] (Fin 2 → ℝ)) (hD : Function.Surjective D) :
    ∃ v : Module.Basis (Fin 3) ℝ E,
      D (v 0) = Pi.single 0 1 ∧ D (v 1) = Pi.single 1 1 ∧ D (v 2) = 0 := by
  classical
  obtain ⟨Q, hQ⟩ := ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional hD
  have hk := D.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hD, finrank_top,
    Module.finrank_pi, Fintype.card_fin, hdim] at hk
  have hkp : 0 < Module.finrank ℝ D.ker := by omega
  obtain ⟨w, hw⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hkp
  have hw0 : (w : E) ≠ 0 := fun h => hw (Subtype.ext h)
  have hDw : D (w : E) = 0 := w.property
  let v : Fin 3 → E := ![Q (Pi.single 0 1), Q (Pi.single 1 1), w]
  have hv : LinearIndependent ℝ v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hs : c 0 • Q (Pi.single 0 1) + c 1 • Q (Pi.single 1 1) + c 2 • (w : E) = 0 := by
      simpa [v, Fin.sum_univ_succ, add_assoc] using hc
    have hh := congrArg D hs
    simp only [map_add, map_smul, hQ (Pi.single 0 1), hQ (Pi.single 1 1), hDw,
      smul_zero, add_zero, map_zero] at hh
    have h0 : c 0 = 0 := by simpa using congr_fun hh 0
    have h1 : c 1 = 0 := by simpa using congr_fun hh 1
    have h2 : c 2 = 0 := by
      simp only [h0, h1, zero_smul, zero_add] at hs
      exact (smul_eq_zero.mp hs).resolve_right hw0
    intro i
    fin_cases i <;> assumption
  let b := basisOfLinearIndependentOfCardEqFinrank hv (by simpa using hdim.symm)
  have hb : (b : Fin 3 → E) = v := coe_basisOfLinearIndependentOfCardEqFinrank hv _
  refine ⟨b, ?_, ?_, ?_⟩
  · rw [hb]
    exact hQ _
  · rw [hb]
    exact hQ _
  · rw [hb]
    exact hDw

open Filter Topology

def rawTwoSpatial {E : Type*} [AddCommGroup E] [Module ℝ E]
    (v : Fin 3 → E) (r : Fin 5 → ℝ) : Fin 2 → E :=
  ![r 0 • v 0 + r 1 • v 1 + r 3 • v 2,
    r 1 • v 0 + r 2 • v 1 + r 4 • v 2]

lemma rawTwoSpatial_symmetry
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Fin 3 → E) (D : E →L[ℝ] (Fin 2 → ℝ))
    (h0 : D (v 0) = Pi.single 0 1) (h1 : D (v 1) = Pi.single 1 1)
    (h2 : D (v 2) = 0) (r : Fin 5 → ℝ) :
    D (rawTwoSpatial v r 0) 1 = D (rawTwoSpatial v r 1) 0 := by
  simp [rawTwoSpatial, map_add, map_smul, h0, h1, h2]

lemma adapted_basis_coordinate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Module.Basis (Fin 3) ℝ E) (D : E →L[ℝ] (Fin 2 → ℝ))
    (h0 : D (v 0) = Pi.single 0 1) (h1 : D (v 1) = Pi.single 1 1)
    (h2 : D (v 2) = 0) (x : E) (i : Fin 2) :
    D x i = v.repr x i.castSucc := by
  have hx := congrArg D (v.sum_repr x)
  rw [Fin.sum_univ_three] at hx
  simp only [map_add, map_smul, h0, h1, h2, smul_zero, add_zero] at hx
  fin_cases i
  · simpa using (congr_fun hx 0).symm
  · simpa using (congr_fun hx 1).symm

lemma exists_rawTwoSpatial
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Module.Basis (Fin 3) ℝ E) (D : E →L[ℝ] (Fin 2 → ℝ))
    (h0 : D (v 0) = Pi.single 0 1) (h1 : D (v 1) = Pi.single 1 1)
    (h2 : D (v 2) = 0) (R : Fin 2 → E)
    (hR : D (R 0) 1 = D (R 1) 0) :
    ∃ r : Fin 5 → ℝ, rawTwoSpatial v r = R := by
  have hs : v.repr (R 0) 1 = v.repr (R 1) 0 := by
    simpa [adapted_basis_coordinate v D h0 h1 h2] using hR
  refine ⟨![v.repr (R 0) 0, v.repr (R 0) 1, v.repr (R 1) 1,
    v.repr (R 0) 2, v.repr (R 1) 2], ?_⟩
  funext i
  fin_cases i
  · change v.repr (R 0) 0 • v 0 + v.repr (R 0) 1 • v 1 + v.repr (R 0) 2 • v 2 = R 0
    simpa only [Fin.sum_univ_three] using v.sum_repr (R 0)
  · change v.repr (R 0) 1 • v 0 + v.repr (R 1) 1 • v 1 + v.repr (R 1) 2 • v 2 = R 1
    rw [hs]
    simpa only [Fin.sum_univ_three] using v.sum_repr (R 1)

lemma rawTwoSpatial_symbol
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Fin 3 → E) (L : E →L[ℝ] ℝ) (r : Fin 5 → ℝ) :
    divSymbolTwo (fun i => L (v i)) *ᵥ r = fun j => L (rawTwoSpatial v r j) := by
  ext j
  fin_cases j <;> simp [rawTwoSpatial, divSymbolTwo, Matrix.mulVec,
    dotProduct, Fin.sum_univ_succ, map_add, map_smul] <;> ring

lemma smooth_rawTwoSpatial
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Fin 3 → E) (G : Fin 5 → SmoothScalar E) (j : Fin 2) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => rawTwoSpatial v (fun i => (G i).val x) j) := by
  fin_cases j <;>
    exact (((smoothScalar_contDiff (G _)).smul contDiff_const).add
      ((smoothScalar_contDiff (G _)).smul contDiff_const)).add
        ((smoothScalar_contDiff (G _)).smul contDiff_const)

lemma support_rawTwoSpatial
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Fin 3 → E) (G : Fin 5 → SmoothScalar E) {K : Set E}
    (hK : IsClosed K) (hG : ∀ i, tsupport (G i).val ⊆ K) (j : Fin 2) :
    tsupport (fun x => rawTwoSpatial v (fun i => (G i).val x) j) ⊆ K := by
  apply closure_minimal _ hK
  intro x hx
  by_contra hn
  have hz (i : Fin 5) : (G i).val x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun ht => hn (hG i ht))
  apply hx
  fin_cases j <;> simp [rawTwoSpatial, hz]

lemma rawTwoSpatial_pairing
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Fin 3 → E) (G : Fin 5 → SmoothScalar E) (ψ : SmoothScalar E)
    (j : Fin 2) (x : E) :
    fderiv ℝ ψ.val x (rawTwoSpatial v (fun i => (G i).val x) j) =
      ∑ i, (twoFluxColumns G j i).val x * (smoothDirection (v i) ψ).val x := by
  fin_cases j <;> simp [rawTwoSpatial, twoFluxColumns, smoothDirection,
    Fin.sum_univ_succ, map_add, map_smul, add_assoc]

end

open MeasureTheory Filter Topology

lemma uniform_zero_smul_vector {X I E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {l : Filter I} {f : I → X → ℝ} (v : E)
    (hf : TendstoUniformly f (fun _ => 0) l) :
    TendstoUniformly (fun i x => f i x • v) (fun _ => 0) l := by
  simpa [Function.comp_def] using
    ((ContinuousLinearMap.id ℝ ℝ).smulRight v).uniformContinuous.comp_tendstoUniformly hf

lemma rawTwoSpatial_error
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Fin 3 → E) (g r : Fin 5 → ℝ) (z : ℝ) (j : Fin 2) :
    rawTwoSpatial v g j - z • rawTwoSpatial v r j =
      rawTwoSpatial v (fun i => g i - r i * z) j := by
  fin_cases j <;> simp [rawTwoSpatial, sub_smul, mul_smul, smul_add] <;> module

lemma rawTwoSpatial_error_tendsto
    {X I E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {l : Filter I} (v : Fin 3 → E) (G : I → X → Fin 5 → ℝ)
    (r : Fin 5 → ℝ) (z : I → X → ℝ)
    (hG : ∀ i, TendstoUniformly (fun k x => G k x i - r i * z k x)
      (fun _ => 0) l) (j : Fin 2) :
    TendstoUniformly (fun k x => rawTwoSpatial v (G k x) j - z k x • rawTwoSpatial v r j)
      (fun _ => 0) l := by
  simp_rw [rawTwoSpatial_error]
  have hc (i : Fin 5) (a : Fin 3) := uniform_zero_smul_vector (v a) (hG i)
  fin_cases j
  · convert ((hc 0 0).add (hc 1 1)).add (hc 3 2) using 1 <;> ext <;> simp [rawTwoSpatial]
  · convert ((hc 1 0).add (hc 2 1)).add (hc 4 2) using 1 <;> ext <;> simp [rawTwoSpatial]

theorem exists_physical_two_flux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hdim : Module.finrank ℝ E = 3) (μ : Measure E) [μ.IsAddHaarMeasure]
    (D : E →L[ℝ] (Fin 2 → ℝ)) (hD : Function.Surjective D)
    (χ : SmoothScalar E) (hχ : HasCompactSupport χ.val)
    (L : E →L[ℝ] ℝ) (hL : L ≠ 0)
    (h : SmoothScalar ℝ) (hp : Function.Periodic h.val 1)
    (hm : ∫ t in (0 : ℝ)..1, h.val t = 0)
    (R : Fin 2 → E) (hRs : D (R 0) 1 = D (R 1) 0)
    (hRn : ∀ j, L (R j) = 0) :
    ∃ F : ℝ → Fin 2 → E → E,
      (∀ k j, ContDiff ℝ (↑(⊤ : ℕ∞)) (F k j)) ∧
      (∀ k j, tsupport (F k j) ⊆ tsupport χ.val) ∧
      (∀ k x, D (F k 0 x) 1 = D (F k 1 x) 0) ∧
      (∀ k j (ψ : E → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
        (∫ x, fderiv ℝ ψ x (F k j x) ∂μ) = 0) ∧
      ∀ j, TendstoUniformly
        (fun k x => F k j x - (χ.val x * h.val (k * L x)) • R j)
        (fun _ => 0) atTop := by
  obtain ⟨v, h0, h1, h2⟩ := exists_adapted_spatial_basis hdim D hD
  obtain ⟨r, hr⟩ := exists_rawTwoSpatial v D h0 h1 h2 R hRs
  have hξ : (fun i => L (v i)) ≠ 0 := by
    intro hz
    apply hL
    ext x
    have hx := congrArg L (v.sum_repr x)
    simp only [map_sum, map_smul] at hx
    have hv (i : Fin 3) : L (v i) = 0 := congr_fun hz i
    simpa only [hv, smul_zero, Finset.sum_const_zero, _root_.zero_apply]
      using hx.symm
  have hsymbol : divSymbolTwo (fun i => L (v i)) *ᵥ r = 0 := by
    rw [rawTwoSpatial_symbol, hr]
    exact funext hRn
  obtain ⟨G, hdiv, hs, he⟩ := exists_localized_two_flux v χ L h r hχ hξ hsymbol hp hm
  let F : ℝ → Fin 2 → E → E := fun k j x => rawTwoSpatial v (fun i => (G k i).val x) j
  refine ⟨F, (fun k j => smooth_rawTwoSpatial v (G k) j),
    (fun k j => support_rawTwoSpatial v (G k) (isClosed_tsupport _) (hs k) j),
    (fun k x => rawTwoSpatial_symmetry v D h0 h1 h2 _), ?_, ?_⟩
  · intro k j ψ hψ
    let Ψ : SmoothScalar E := ⟨ψ, hψ⟩
    change (∫ x, fderiv ℝ Ψ.val x (rawTwoSpatial v (fun i => (G k i).val x) j) ∂μ) = 0
    simp_rw [rawTwoSpatial_pairing]
    apply smooth_divergence_zero_pairing μ v _ _ _ Ψ
    · have hc (i : Fin 5) : HasCompactSupport (G k i).val :=
        hχ.of_isClosed_subset (isClosed_tsupport _) (hs k i)
      intro i
      fin_cases j <;> fin_cases i <;> exact hc _
    · rw [twoFluxColumns_divergence, hdiv]
      rfl
  · intro j
    have ht := rawTwoSpatial_error_tendsto v (fun k x i => (G k i).val x) r
      (fun k x => χ.val x * h.val (k * L x)) he j
    simpa only [hr] using ht

end ScalarConductivity

end

end OAI
