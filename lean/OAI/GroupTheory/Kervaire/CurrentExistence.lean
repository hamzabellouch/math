import OAI.GroupTheory.Kervaire.IncidenceDegree

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder
open MeasureTheory Measure Set Filter
open scoped Topology
open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff
open ContinuousAlternatingMap
open scoped ContDiff
open MeasureTheory NormedSpace
open scoped ContDiff
open Module Set ContinuousAlternatingMap
open Matrix Module
open scoped ContDiff Matrix.Norms.L2Operator
open scoped ComplexOrder
open scoped ContDiff
open NormedSpace Complex
open scoped ContDiff Matrix.Norms.L2Operator
open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace KervaireCurrentExistence

variable {S E : Type*} [TopologicalSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {μ : Measure S} [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]

/-- The nonzero local degree forces a target point into the other endpoint's image.
All localization is justified by compactness, smooth bumps and positivity of Haar measure. -/
lemma mem_range_of_integral_invariant {f₀ f₁ : S → E} {j₀ j₁ : S → ℝ}
    (hf₀ : Continuous f₀) (hf₁ : Continuous f₁) (hj₀ : Continuous j₀)
    (y : E) (hex : ∃ x, f₀ x = y) (hpos : ∀ x, f₀ x = y → 0 < j₀ x)
    (hinv : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, φ (f₀ x) * j₀ x ∂μ) = ∫ x, φ (f₁ x) * j₁ x ∂μ) :
    y ∈ Set.range f₁ := by
  by_contra hmiss
  let K : Set E := f₀ '' {x | j₀ x ≤ 0} ∪ Set.range f₁
  have hK : IsCompact K := by
    apply IsCompact.union
    · exact (isClosed_le hj₀ continuous_const).isCompact.image hf₀
    · exact isCompact_range hf₁
  have hyK : y ∉ K := by
    rintro (⟨x, hx, hxy⟩ | hy)
    · exact (not_le_of_gt (hpos x hxy)) hx
    · exact hmiss hy
  obtain ⟨φ, hφs, hφcomp, hφ, hφrange, hφy⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (hK.isClosed.isOpen_compl.mem_nhds hyK)
  have hφzero (z : E) (hz : z ∈ K) : φ z = 0 := by
    by_contra hn
    exact hφs (subset_closure hn) hz
  have hnonneg (x : S) : 0 ≤ φ (f₀ x) * j₀ x := by
    by_cases hx : j₀ x ≤ 0
    · rw [hφzero _ (Or.inl ⟨x,hx,rfl⟩), zero_mul]
    · exact mul_nonneg (hφrange (mem_range_self _) |>.1) (le_of_not_ge hx)
  obtain ⟨x₀, hx₀⟩ := hex
  have hnonzero : φ (f₀ x₀) * j₀ x₀ ≠ 0 := by
    rw [hx₀, hφy, one_mul]
    exact (hpos x₀ hx₀).ne'
  have hgt : 0 < ∫ x, φ (f₀ x) * j₀ x ∂μ :=
    ((hφ.continuous.comp hf₀).mul hj₀).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (HasCompactSupport.of_compactSpace _) hnonneg hnonzero
  have hz : (∫ x, φ (f₁ x) * j₁ x ∂μ) = 0 := by
    apply integral_eq_zero_of_ae
    exact Filter.Eventually.of_forall fun x ↦ by
      change φ (f₁ x) * j₁ x = 0
      rw [hφzero _ (Or.inr (mem_range_self x)), zero_mul]
  rw [hinv φ hφ hφcomp, hz] at hgt
  exact lt_irrefl _ hgt

end KervaireCurrentExistence

namespace KervaireIncidenceCurrent
open MeasureTheory KervaireUnitaryHomotopy
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]

def modelMap : UMap (Mat K) (Mat (K ⊕ R)) where
  toFun X := diag X (-1)
  smooth := by
    simp only [diag_eq_corner]
    exact (in11 (K := K) (R := R)).contDiff.add contDiff_const
  unitary X := diag_unitary X.property (by constructor <;> simp)

lemma exists_incidence_of_homotopic_basis
    {IK IR IZ : Type*} [Fintype IK] [Fintype IR] [Fintype IZ]
    (bK : Basis IK ℝ (skewAdjoint.submodule ℝ (Mat K)))
    (bR : Basis IR ℝ (skewAdjoint.submodule ℝ (Mat R)))
    (bZ : Basis IZ ℝ (Matrix R K ℂ))
    {n : ℕ} (e : (IK ⊕ IR ⊕ IZ) ≃ Fin (n+1))
    (hbK : (KervaireSkewTrace.pairing (I := K)).IsOrthoᵢ bK)
    (hbR : (KervaireSkewTrace.pairing (I := R)).IsOrthoᵢ bR)
    (F : UMap (Mat K) (Mat (K ⊕ R))) (hF : Homotopic modelMap F) :
    ∃ p : unitary (Alg K R), incidence (timeless F) (0,(p : Alg K R)) = 1 := by
  classical
  let : CompactSpace (unitary (Alg K R)) := KervaireCompactUnitary.compactSpace
  let : MeasurableSpace (unitary (Alg K R)) := borel _
  let : BorelSpace (unitary (Alg K R)) := ⟨rfl⟩
  let μ : Measure (unitary (Alg K R)) := (Measure.haar (G := unitary (Alg K R))).inv
  let b := (horizontalBasis bK bR bZ).reindex e
  let c := modelVolumeBasis b
  have hn := KervaireCurrentExistence.mem_range_of_integral_invariant (μ := μ)
    (f₀ := fun p : unitary (Alg K R) ↦ incidence model (0,(p : Alg K R)))
    (f₁ := fun p : unitary (Alg K R) ↦ incidence (timeless F) (0,(p : Alg K R)))
    (j₀ := fun p : unitary (Alg K R) ↦ jacobian b c model 0 (p : Alg K R))
    (j₁ := fun p : unitary (Alg K R) ↦ jacobian b c (timeless F) 0 (p : Alg K R))
    ((contDiff_incidence contDiff_model).continuous.comp (continuous_const.prodMk continuous_subtype_val))
    ((contDiff_incidence (contDiff_timeless F)).continuous.comp (continuous_const.prodMk continuous_subtype_val))
    ((continuous_jacobian b c contDiff_model 0).comp continuous_subtype_val)
    1 ⟨gaugePoint 1 1,model_incidence_gauge 0 1 1⟩
    (model_jacobian_pos_fiber b 0) ?_
  · exact hn
  · intro φ hφ _
    have hi := current_eq_of_homotopic (μ := μ) bK bR bZ e hbK hbR
      (fun y ↦ φ y • tangentVolume c) (hφ.smul contDiff_const) hF
    have hm : timeless (modelMap (K := K) (R := R)) = (model : ℝ × Mat K → Mat (K ⊕ R)) := rfl
    simpa only [current,ContinuousAlternatingMap.smul_apply,smul_eq_mul,hm,jacobian,b] using hi

lemma skew_finrank_pos [Nonempty K] :
    0 < Module.finrank ℝ (skewAdjoint.submodule ℝ (Mat K)) := by
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  let a : skewAdjoint.submodule ℝ (Mat K) := ⟨Complex.I • (1 : Mat K),by
    change star (Complex.I • (1 : Mat K)) = -(Complex.I • (1 : Mat K))
    simp⟩
  refine ⟨a,?_⟩
  intro h
  have hz := congrArg (fun a : skewAdjoint.submodule ℝ (Mat K) ↦ (a : Mat K)) h
  have hi := congrFun (congrFun hz (Classical.arbitrary K)) (Classical.arbitrary K)
  simp [a] at hi

lemma exists_incidence_of_homotopic [Nonempty K]
    (F : UMap (Mat K) (Mat (K ⊕ R))) (hF : Homotopic modelMap F) :
    ∃ p : unitary (Alg K R), incidence (timeless F) (0,(p : Alg K R)) = 1 := by
  classical
  obtain ⟨bK,hbK⟩ := KervaireSkewTrace.exists_orthogonal_basis (I := K)
  obtain ⟨bR,hbR⟩ := KervaireSkewTrace.exists_orthogonal_basis (I := R)
  let bZ := Module.finBasis ℝ (Matrix R K ℂ)
  let J := Fin (Module.finrank ℝ (skewAdjoint.submodule ℝ (Mat K))) ⊕
    Fin (Module.finrank ℝ (skewAdjoint.submodule ℝ (Mat R))) ⊕ Fin (Module.finrank ℝ (Matrix R K ℂ))
  have hc : 0 < Fintype.card J := by
    simpa only [J,Fintype.card_sum,Fintype.card_fin] using
      lt_of_lt_of_le (skew_finrank_pos (K := K)) (Nat.le_add_right _ _)
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero hc.ne'
  let e : J ≃ Fin (n+1) := (Fintype.equivFin J).trans (finCongr hn)
  exact exists_incidence_of_homotopic_basis bK bR bZ e hbK hbR F hF

end KervaireIncidenceCurrent

end

end OAI
