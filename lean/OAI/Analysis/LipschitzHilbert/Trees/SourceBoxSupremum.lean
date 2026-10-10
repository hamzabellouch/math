import OAI.Analysis.LipschitzHilbert.Trees.SourceBoxReproduction

namespace OAI

/-! Actual suprema of packet values and their energy on disjoint cells.
The supremum includes zero, so an empty packet family contributes zero. -/
noncomputable section
open Set MeasureTheory Function
open scoped BigOperators ENNReal
namespace LipschitzHilbert

variable {X E ι : Type*} [NormedAddCommGroup E]

def packetNormValues (F : ι → X → E) (Q : Set X) : Set ℝ :=
  {r | r=0 ∨ ∃ a x, x∈Q ∧ r=‖F a x‖}

def packetNormSup (F : ι → X → E) (Q : Set X) : ℝ :=
  sSup (packetNormValues F Q)

theorem packetNormValues_bddAbove (F : ι → X → E) (Q : Set X)
    (B : ℝ) (hB : 0≤B) (hF : ∀ a x, x∈Q → ‖F a x‖≤B) :
    BddAbove (packetNormValues F Q) := by
  refine ⟨B,?_⟩
  rintro r (hr | ⟨a,x,hx,rfl⟩)
  · exact hr ▸ hB
  · exact hF a x hx

theorem packetNormSup_nonneg (F : ι → X → E) (Q : Set X)
    (B : ℝ) (hB : 0≤B) (hF : ∀ a x, x∈Q → ‖F a x‖≤B) :
    0≤packetNormSup F Q :=
  le_csSup (packetNormValues_bddAbove F Q B hB hF) (Or.inl rfl)

theorem packetNormSup_le (F : ι → X → E) (Q : Set X)
    (B : ℝ) (hB : 0≤B) (hF : ∀ a x, x∈Q → ‖F a x‖≤B) :
    packetNormSup F Q≤B := by
  unfold packetNormSup
  apply csSup_le (s:=packetNormValues F Q) ⟨0,Or.inl rfl⟩
  rintro r (hr | ⟨a,x,hx,rfl⟩)
  · exact hr ▸ hB
  · exact hF a x hx

variable [MeasurableSpace X]

/-- Integrating a common pointwise majorant controls a literal supremum
on any finite-measure cell. -/
theorem packetNormSup_cell_energy (μ : Measure X) (F : ι → X → E) (Q A : Set X)
    (hA : MeasurableSet A) (hAfin : μ A≠∞)
    (B C : ℝ) (hB : 0≤B) (hC : 0≤C)
    (hF : ∀ a x, x∈Q → ‖F a x‖≤B)
    (g : X → ℝ) (hg : MemLp g 2 μ) (hg0 : ∀ x, 0≤g x)
    (hpoint : ∀ᵐ z ∂μ, z∈A → ∀ a x, x∈Q → ‖F a x‖≤C*g z) :
    (packetNormSup F Q)^2*μ.real A≤C^2*∫ z in A, (g z)^2 ∂μ := by
  have hsup0 := packetNormSup_nonneg F Q B hB hF
  have : IsFiniteMeasure (μ.restrict A) := isFiniteMeasure_restrict.mpr hAfin
  have hi : (∫ _z in A, (packetNormSup F Q)^2 ∂μ)≤
      ∫ z in A, C^2*(g z)^2 ∂μ := by
    apply integral_mono_ae (integrable_const _) ((hg.restrict A).integrable_sq.const_mul _)
    filter_upwards [ae_restrict_of_ae hpoint,ae_restrict_mem hA] with z hz hzA
    have hs := packetNormSup_le F Q (C*g z) (mul_nonneg hC (hg0 z)) (hz hzA)
    simpa only [mul_pow] using pow_le_pow_left₀ hsup0 hs 2
  rw [integral_const,measureReal_restrict_apply_univ,smul_eq_mul,integral_const_mul] at hi
  simpa only [mul_comm] using hi

/-- Disjoint cell summation does not introduce a cell-count factor. -/
theorem packetNormSup_finite_energy {J : Type*} (μ : Measure X) (s : Finset J)
    (F : J → ι → X → E) (Q A : J → Set X)
    (hA : ∀ j∈s, MeasurableSet (A j)) (hAfin : ∀ j∈s, μ (A j)≠∞)
    (hdisj : Set.Pairwise (↑s) (Disjoint on A))
    (B C : ℝ) (hB : 0≤B) (hC : 0≤C)
    (hF : ∀ j∈s, ∀ a x, x∈Q j → ‖F j a x‖≤B)
    (g : X → ℝ) (hg : MemLp g 2 μ) (hg0 : ∀ x, 0≤g x)
    (hpoint : ∀ j∈s, ∀ᵐ z ∂μ, z∈A j → ∀ a x, x∈Q j → ‖F j a x‖≤C*g z) :
    (∑ j∈s, (packetNormSup (F j) (Q j))^2*μ.real (A j))≤
      C^2*∫ z, (g z)^2 ∂μ := by
  calc
    _ ≤ ∑ j∈s, C^2*∫ z in A j, (g z)^2 ∂μ :=
      Finset.sum_le_sum (fun j hj => packetNormSup_cell_energy μ (F j) (Q j) (A j)
        (hA j hj) (hAfin j hj) B C hB hC (hF j hj) g hg hg0 (hpoint j hj))
    _ = C^2*∫ z in ⋃ j∈s, A j, (g z)^2 ∂μ := by
      rw [←Finset.mul_sum,integral_biUnion_finset s hA hdisj (fun _ _ => hg.integrable_sq.integrableOn)]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (setIntegral_le_integral hg.integrable_sq (Filter.Eventually.of_forall (fun z => sq_nonneg (g z))))
      (sq_nonneg C)

end LipschitzHilbert

end

end OAI
