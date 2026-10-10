import Mathlib
import OAI.Geometry.PrescribedPotential.QuasilinearFamilyBootstrap

namespace OAI

/-! Compact Coefficient Bootstrap. -/

section

noncomputable section
open Set Filter Topology Finset Module
open scoped ContDiff
namespace HigherJet
variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  {ι α : Type*} [Fintype ι]
local instance compactHessianNorm : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance compactHessianSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance
lemma quasilinear_compact_coefficient_bootstrap (B : G →L[ℝ] (E →L[ℝ] E →L[ℝ] F) →L[ℝ] F)
    {U : Set E} (hU : IsOpen U) (e : OrthonormalBasis ι ℝ E)
    (u r : α → E → F) (a : F → G) (b : F × (E →L[ℝ] F) → F)
    (τ : α → E → E ≃L[ℝ] E)
    (hu : ∀ s, ContDiffOn ℝ ∞ (u s) U) (hr : ∀ s, ContDiffOn ℝ ∞ (r s) U)
    (ha : ∀ s y, y ∈ U → ContDiffAt ℝ ∞ a (u s y))
    (hb : ∀ s y, y ∈ U → ContDiffAt ℝ ∞ b (firstJet (u s) y))
    (heq : ∀ s y, y ∈ U → B (a (u s y)) (hessian (u s) y) = r s y+b (firstJet (u s) y))
    (hframe : ∀ s x, x ∈ U → ∀ H : E →L[ℝ] E →L[ℝ] F,
      B (a (u s x)) H = ∑ i, H (τ s x (e i)) (τ s x (e i)))
    (hframes : ∀ K, IsCompact K → K ⊆ U → ∃ C : ℝ, 0 ≤ C ∧ ∀ s x, x ∈ K →
      ‖(τ s x).toContinuousLinearMap‖ ≤ C ∧ ‖(τ s x).symm.toContinuousLinearMap‖ ≤ C)
    (hcompact : ∀ K, IsCompact K → K ⊆ U → ∃ P : Set (F × (E →L[ℝ] F)), IsCompact P ∧
      (∀ s x, x ∈ K → firstJet (u s) x ∈ P) ∧
      (∀ p ∈ P, ContDiffAt ℝ ∞ a p.1 ∧ ContDiffAt ℝ ∞ b p))
    (hrbounds : ∀ m K, IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ j, j ≤ m → ∀ s x, x ∈ K →
      ‖iteratedFDeriv ℝ j (r s) x‖ ≤ C) :
    ∀ m, 1 ≤ m → ∀ K, IsCompact K → K ⊆ U →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s x, x ∈ K → ‖iteratedFDeriv ℝ m (u s) x‖ ≤ C := by
  apply quasilinear_family_bootstrap B hU e u r a b τ hu hr ha hb heq hframe hframes
  intro m K hK hKU
  obtain ⟨P,hP,hmem,hsm⟩ := hcompact K hK hKU
  obtain ⟨A,hA,ha'⟩ := compact_coefficient_jets (hP.image continuous_fst)
    (fun y hy => by obtain ⟨p,hp,rfl⟩ := hy; exact (hsm p hp).1) m
  obtain ⟨Q,hQ,hb'⟩ := compact_coefficient_jets hP (fun y hy => (hsm y hy).2) m
  obtain ⟨J,hJ⟩ := hP.exists_bound_of_continuousOn (continuous_snd.continuousOn : ContinuousOn (fun p : F × (E →L[ℝ] F) => p.2) P)
  obtain ⟨R,hR⟩ := hrbounds m K hK hKU
  let T : ℝ := ∑ j ∈ range (m+1), (Fintype.card (OrderedFinpartition j) : ℝ)
  have hT : 0 ≤ T := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  let C := 1+‖B‖+A+Q+max J 0+max R 0+T
  have hC : 1 ≤ C := by dsimp [C]; linarith [norm_nonneg B,le_max_right J 0,le_max_right R 0]
  have hcB : ‖B‖ ≤ C := by dsimp [C]; linarith [le_max_right J 0,le_max_right R 0]
  have hcA : A ≤ C := by dsimp [C]; linarith [norm_nonneg B,le_max_right J 0,le_max_right R 0]
  have hcQ : Q ≤ C := by dsimp [C]; linarith [norm_nonneg B,le_max_right J 0,le_max_right R 0]
  have hcJ : J ≤ C := by dsimp [C]; linarith [norm_nonneg B,le_max_left J 0,le_max_right R 0]
  have hcR : R ≤ C := by dsimp [C]; linarith [norm_nonneg B,le_max_right J 0,le_max_left R 0]
  have hcT : T ≤ C := by dsimp [C]; linarith [norm_nonneg B,le_max_right J 0,le_max_right R 0]
  refine ⟨C,hC,hcB,fun j hj => ?_,fun s x hx => ?_⟩
  · exact (Finset.single_le_sum (fun i _ => Nat.cast_nonneg (α := ℝ) (Fintype.card (OrderedFinpartition i)))
      (mem_range.mpr (by omega))).trans hcT
  · have hp := hmem s x hx
    refine ⟨?_,fun j hj => (ha' j hj _ ⟨firstJet (u s) x,hp,rfl⟩).trans hcA,
      fun j hj => (hb' j hj _ hp).trans hcQ,fun j hj => (hR j hj s x hx).trans hcR⟩
    simpa only [norm_iteratedFDeriv_one,firstJet] using (hJ _ hp).trans hcJ
end HigherJet

end
end

end OAI
