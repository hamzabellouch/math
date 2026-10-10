import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors
import OAI.MeasureTheory.FalconerCompletion.Angular.TensorCapTsupportCoord
import OAI.MeasureTheory.FalconerCompletion.Recursion.NominalRadius

namespace OAI

/-! Recursive policies and quantitative depth estimates. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.TreeND
open Set Metric MeasureTheory PlanarFalconer
open scoped ENNReal RealInnerProductSpace ContDiff Topology
variable {d : ℕ}

lemma descriptorGood_neg (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (m : ℝ → ℝ) (N : ℕ) (sig C : ℝ) (J i : ℕ) (P : CellPath d)
    (b : PolicyDescriptor) {w : EuclideanSpace ℝ (Fin d)}
    (hw : w ∈ descriptorGood ρ m N sig C J i P b) :
    -w ∈ descriptorGood ρ m N sig C J i P b := by
  classical
  cases b with
  | parallel g p =>
    have he : fullParallelCount ρ g p P (testWidth N J i p sig) (-w)=
        fullParallelCount ρ g p P (testWidth N J i p sig) w := by
      unfold fullParallelCount
      congr 1
      ext Q
      simp only [Finset.mem_filter,graphPerpND,inner_neg_right,neg_smul,smul_neg,neg_neg]
      constructor
      · intro h
        apply Finset.mem_filter.mpr
        exact h
      · intro h
        exact Finset.mem_filter.mp h
    exact ⟨by simpa only [norm_neg] using hw.1,by rw [he]; exact hw.2⟩
  | projection p t =>
    simpa only [descriptorGood,Set.mem_ofPred_eq,norm_neg,fullProjectionCollision,
      inner_neg_right,abs_neg] using hw

noncomputable def actualDescriptorMask (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (m : ℝ → ℝ) (N : ℕ) (sig C : ℝ) (J i : ℕ) (P : CellPath d)
    (b : PolicyDescriptor) : EuclideanSpace ℝ (Fin d) → ℝ :=
  evenBufferedMaskND (sourceMaskRadiusND d (descriptorLength b) ((2:ℝ)^N) sig)
    (descriptorGood ρ m N sig C J i P b)

lemma actualDescriptorMask_smooth (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (m : ℝ → ℝ) (N : ℕ) (sig C : ℝ) (J i : ℕ) (P : CellPath d)
    (b : PolicyDescriptor) : ContDiff ℝ ∞ (actualDescriptorMask ρ m N sig C J i P b) :=
  evenBufferedMaskND_contDiff _ _

lemma actualDescriptorMask_even (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (m : ℝ → ℝ) (N : ℕ) (sig C : ℝ) (J i : ℕ) (P : CellPath d)
    (b : PolicyDescriptor) : Function.Even (actualDescriptorMask ρ m N sig C J i P b) :=
  evenBufferedMaskND_even _ _

lemma actualDescriptorMask_bounds (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (m : ℝ → ℝ) (N : ℕ) (sig C : ℝ) (J i : ℕ) (P : CellPath d)
    (b : PolicyDescriptor) {w : EuclideanSpace ℝ (Fin d)} (hw : ‖w‖ ≤ 1) :
    0 ≤ actualDescriptorMask ρ m N sig C J i P b w ∧
      actualDescriptorMask ρ m N sig C J i P b w ≤ 1 :=
  evenBufferedMaskND_bounds (sourceMaskRadiusND_pos _ _ _ _) _ hw

lemma actualDescriptorMask_one (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (m : ℝ → ℝ) (N : ℕ) (sig C : ℝ) (J i : ℕ) (P : CellPath d)
    (b : PolicyDescriptor) {w : EuclideanSpace ℝ (Fin d)}
    (hw : w ∈ descriptorGood ρ m N sig C J i P b) :
    actualDescriptorMask ρ m N sig C J i P b w = 1 := by
  have hnorm : ‖w‖=1 := by cases b <;> exact hw.1
  exact evenBufferedMaskND_eq_one (sourceMaskRadiusND_pos _ _ _ _)
    (fun _ hv => descriptorGood_neg ρ m N sig C J i P b hv) hnorm.le hw

lemma sourceMaskRadiusND_near_nominal (N l : ℕ) (sig : ℝ) :
    2*(d+1:ℝ)*sourceMaskRadiusND d l ((2:ℝ)^N) sig ≤ nominalRadius N sig l := by
  have hD : 0 < sourceMaskScaleND l ((2:ℝ)^N) sig := sourceMaskScaleND_pos _ _ _
  have h₁ : 2*(d+1:ℝ)*sourceMaskRadiusND d l ((2:ℝ)^N) sig ≤
      (sourceMaskScaleND l ((2:ℝ)^N) sig)⁻¹ := by
    unfold sourceMaskRadiusND
    have hd : 2*(d+1:ℝ) ≤ 100*(d+1:ℝ)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) d]
    exact (mul_le_mul_of_nonneg_right hd (by positivity : 0 ≤
      (sourceMaskScaleND l ((2:ℝ)^N) sig)⁻¹/(100*(d+1:ℝ)^2))).trans_eq (by
        field_simp)
  apply h₁.trans
  apply le_min
  · exact (inv_le_one₀ hD).mpr (sourceMaskScaleND_one_le _ _ _)
  · simpa only [Nat.sub_zero,pow_zero,inv_one,one_mul,one_div] using
      (sourceMaskScaleND_inv_depth (g := 0) (p := l) (Nat.zero_le l)
        (R := (2:ℝ)^N) (σ := sig) (by positivity))

lemma uniform_actualDescriptorMask_support {sig : ℝ} (hsig : 0<sig) {J : ℕ} (hJ : 0<J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (ρ : Measure (EuclideanSpace ℝ (Fin d))), IsFiniteMeasure ρ →
      ∀ (m : ℝ → ℝ) (C : ℝ) (i : ℕ) (b : PolicyDescriptor), ValidDescriptor N b →
      ∀ P : CellPath d, P.length=descriptorAnchor b → ∀ k : ℕ,
      ∀ w : EuclideanSpace ℝ (Fin d), ‖w‖=1 →
      w ∈ tsupport (iteratedFDeriv ℝ k (actualDescriptorMask ρ m N sig C J i P b)) →
      w ∈ descriptorGood ρ m N sig C J (i+1) P b := by
  obtain ⟨N₀,h₀⟩ := uniform_descriptorGood_transfer (d := d) hsig hJ
  refine ⟨N₀,?_⟩
  intro N hN ρ hf m C i b hb P hP k w hw hsupport
  have hs : w ∈ tsupport (actualDescriptorMask ρ m N sig C J i P b) :=
    tsupport_iteratedFDeriv_subset k hsupport
  obtain ⟨v,hv,hd⟩ := evenBufferedMaskND_support_near (sourceMaskRadiusND_pos _ _ _ _)
    (fun _ hv => descriptorGood_neg ρ m N sig C J i P b hv) hs
  apply h₀ N hN ρ hf m C i b hb P hP v w hw _ hv
  rw [dist_comm]
  exact hd.trans (sourceMaskRadiusND_near_nominal N (descriptorLength b) sig)

lemma actualDescriptorMask_derivatives (d B : ℕ) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (ρ : Measure (EuclideanSpace ℝ (Fin d)))
      (m : ℝ → ℝ) (N : ℕ) (sig C : ℝ) (J i : ℕ) (P : CellPath d)
      (b : PolicyDescriptor) (k : ℕ), k ≤ B → ∀ w,
      ‖iteratedFDeriv ℝ k (actualDescriptorMask ρ m N sig C J i P b) w‖ ≤
        C₀*(sourceMaskScaleND (descriptorLength b) ((2:ℝ)^N) sig)^k := by
  obtain ⟨C₀,hC,h₀⟩ := evenBufferedMaskND_derivative_bound d B
  let A : ℝ := 100*(d+1)^2
  have hA : 1≤A := by dsimp [A]; nlinarith [sq_nonneg (d:ℝ),Nat.cast_nonneg (α := ℝ) d]
  refine ⟨C₀*A^B,by positivity,?_⟩
  intro ρ m N sig C J i P b k hk w
  have he : (sourceMaskRadiusND d (descriptorLength b) ((2:ℝ)^N) sig)⁻¹=
      A*sourceMaskScaleND (descriptorLength b) ((2:ℝ)^N) sig := by
    rw [sourceMaskRadiusND,inv_div,div_inv_eq_mul]
  apply (h₀ _ _ (sourceMaskRadiusND_pos _ _ _ _) k hk w).trans
  rw [he,mul_pow,← mul_assoc]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hA hk) hC)
      (pow_nonneg (sourceMaskScaleND_pos _ _ _).le k)

end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

end OAI
