import OAI.Probability.ContinuumTransition.BlockEnergy

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem gridBox_subset_translate_cube {u : ℝ} (_hu : 0 < u) (k : Lattice) :
    gridBox u k ⊆ (fun x : Space => x+gridCenter u k) '' cube u := by
  intro x hx
  refine ⟨x-gridCenter u k, ?_, sub_add_cancel _ _⟩
  intro i
  have hxi := hx i
  change -u/2 ≤ x i-u*((k i : ℝ)+1/2) ∧ x i-u*((k i : ℝ)+1/2) ≤ u/2
  constructor <;> linarith [hxi.1, hxi.2]

theorem volume_translate (A : Set Space) (a : Space) :
    volume ((fun x : Space => x+a) '' A) = volume A := by
  have he : (fun x : Space => x+a) '' A = (fun x : Space => x-a) ⁻¹' A := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [mem_preimage, add_sub_cancel_right] using hy
    · intro hx
      exact ⟨x-a, hx, sub_add_cancel _ _⟩
  rw [he, show (fun x : Space => x-a) = (fun x => x+(-a)) by funext; rw [sub_eq_add_neg],
    measure_preimage_add_right]

theorem setPartition_mono {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    {β B : ℝ} (hβ : 0 ≤ β)
    (hst : ∀ (n : ℕ) (x : Fin n → Space), ((-B*n : ℝ) : EReal) ≤ energy φ x)
    {A D : Set Space} (hD : volume D ≠ ⊤) (hAD : A ⊆ D) (n : ℕ) :
    setPartition φ β A n ≤ setPartition φ β D n := by
  unfold setPartition generalPartition
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  refine setIntegral_mono_set (integrableOn_symmetricWeight hφ hβ hst ?_)
    (Filter.Eventually.of_forall (symmetricWeight_nonneg φ β)) ?_
  · rw [volume_generalConfigurations]
    exact ENNReal.pow_ne_top hD
  · exact Filter.Eventually.of_forall (fun _ hx i => hAD (hx i))

theorem setPartition_gridBox_le {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    {β B u : ℝ} (hβ : 0 ≤ β) (hu : 0 < u)
    (hst : ∀ (n : ℕ) (x : Fin n → Space), ((-B*n : ℝ) : EReal) ≤ energy φ x)
    (k : Lattice) (n : ℕ) : setPartition φ β (gridBox u k) n ≤ partition φ β u n := by
  have hfin : volume ((fun x : Space => x+gridCenter u k) '' cube u) ≠ ⊤ := by
    rw [volume_translate, volume_cube]
    exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hh := setPartition_mono hφ hβ hst hfin (gridBox_subset_translate_cube hu k) n
  rw [setPartition_translate] at hh
  simp only [setPartition, generalPartition_eq_partition] at hh
  exact hh

theorem physicalProfile_ge_constant {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ) (r : ℝ) :
    -(t*(∑' n, σ n)*kernelHeight) ≤ physicalProfile t σ R r := by
  have ha := attraction_le ht hσ hR hs r
  have hc := coreProfile_nonneg t r
  change _ ≤ coreProfile t r-attraction t σ R r
  linarith

theorem quadraticBlock_lower {φ : ℝ → ℝ} {C γ : ℝ} (hC : 0 ≤ C) (hγ : 0 ≤ γ)
    (hφ : ∀ r, -C ≤ φ r) (q : ℕ) (x y : Space) :
    -(C+γ) ≤ quadraticBlock q φ γ x y := by
  unfold quadraticBlock blockCut
  split_ifs
  · linarith [hφ ‖x-y‖]
  · linarith

theorem volume_gridBlocks_ne_top {u : ℝ} (hu : 0 ≤ u) (s : Finset Lattice) :
    volume (⋃ k ∈ s, gridBox u k) ≠ ⊤ := by
  apply ne_top_of_le_ne_top ?_ (measure_biUnion_finset_le s (gridBox u))
  apply ENNReal.sum_ne_top.mpr
  intro k _
  rw [volume_gridBox hu]
  exact ENNReal.ofReal_ne_top

theorem quadraticBlock_familyTerm_le {t β μ γ : ℝ} (ht : 0 ≤ t) (hβ : 0 ≤ β)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n)/2 ≤ t^2/8)
    {q : ℕ} (hq : 0 < q) (k : Lattice) (n : ℕ) :
    familyTerm (gibbsFamily (quadraticBlock q (physicalProfile t σ R) γ) β (μ+β*γ/2))
      (gridBox ((q : ℝ)/4) k) n ≤
    quadraticGrandTerm (physicalProfile t σ R) β μ (β*γ/2*((q : ℝ)/4)^3) ((q : ℝ)/4) n := by
  have hu : 0 < (q : ℝ)/4 := by positivity
  rw [familyTerm_quadraticBlock hq]
  unfold quadraticGrandTerm
  rw [show β*γ/2*((q : ℝ)/4)^3*(n : ℝ)^2/((q : ℝ)/4)^3 = β*γ/2*(n : ℝ)^2 by field_simp]
  exact mul_le_mul_of_nonneg_left
    (setPartition_gridBox_le (measurable_radialPotential (measurable_physicalProfile t hσ hR hs))
      hβ hu (physicalProfile_stable ht hσ hR hs hsmall) k n) (Real.exp_pos _).le

theorem grandFinite_quadraticBlock_box {t β μ γ : ℝ} (ht : 0 ≤ t) (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n)/2 ≤ t^2/8) {q : ℕ} (hq : 0 < q)
    (hcoeff : β*γ/2*((q : ℝ)/4)^3 ≤
      β*(t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/(4+2/((q : ℝ)/4))^3) (k : Lattice) :
    GrandFinite (gibbsFamily (quadraticBlock q (physicalProfile t σ R) γ) β (μ+β*γ/2))
      (gridBox ((q : ℝ)/4) k) := by
  have hu : 0 < (q : ℝ)/4 := by positivity
  have hC : 0 ≤ t*(∑' n, σ n)*kernelHeight :=
    mul_nonneg (mul_nonneg ht (tsum_nonneg hσ)) kernelHeight_pos.le
  refine ⟨fun ι _ => integrableOn_gibbs_of_lower
    (measurable_quadraticBlock q (measurable_physicalProfile t hσ hR hs) γ)
    (add_nonneg hC hγ) hβ
    (quadraticBlock_lower hC hγ (physicalProfile_ge_constant ht hσ hR hs) q) ?_ ι, ?_⟩
  · rw [volume_gridBox hu.le]; exact ENNReal.ofReal_ne_top
  · exact Summable.of_nonneg_of_le (familyTerm_nonneg _ _ (gibbsFamily_nonneg _ _ _))
      (quadraticBlock_familyTerm_le ht hβ hσ hR hs hsmall hq k)
      (summable_quadraticGrandTerm ht hβ hu hσ hR hs hsmall hcoeff)

end ContinuumTemperature
end

end OAI
