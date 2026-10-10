import Mathlib
import OAI.Geometry.PrescribedPotential.QuasilinearHighResiduals
import OAI.Geometry.PrescribedPotential.ResidualFamilyBootstrap

namespace OAI

/-! Quasilinear Family Bootstrap. -/

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

local instance hessianNormedAdd : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance hessianNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance

lemma energy_bounds_finite_norms {U : Set E} (hU : IsOpen U) (e : OrthonormalBasis ι ℝ E)
    {u : α → E → F} (hu : ∀ a, ContDiffOn ℝ ∞ (u a) U) {K : Set E} (hKU : K ⊆ U)
    (m : ℕ) (hlo : ∀ j, 1 ≤ j → j < m → EnergyBound (fun j a x => jetEnergy e j (u a) x) j K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j, 1 ≤ j → j < m → ∀ a x, x ∈ K → ‖iteratedFDeriv ℝ j (u a) x‖ ≤ C := by
  classical
  have he (j : Fin m) : ∃ C : ℝ, 0 ≤ C ∧ (1 ≤ j.val → ∀ a x, x ∈ K → ‖iteratedFDeriv ℝ j.val (u a) x‖ ≤ C) := by
    by_cases hj : 1 ≤ j.val
    · obtain ⟨R,hR,hr⟩ := hlo j hj j.isLt
      obtain ⟨C,hC,hc⟩ := norm_iteratedFDeriv_le_jetEnergy (F := F) e.toBasis j.val
      exact ⟨C*Real.sqrt R,by positivity,fun _ a x hx => (hc U hU (u a) (hu a) x (hKU hx)).trans
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hr a x hx)) hC.le)⟩
    · exact ⟨0,le_rfl,fun h => False.elim (hj h)⟩
  choose C hC hc using he
  refine ⟨∑ j, C j,Finset.sum_nonneg (fun j _ => hC j),fun j hj hjm a x hx => ?_⟩
  exact (hc ⟨j,hjm⟩ hj a x hx).trans (Finset.single_le_sum (fun i _ => hC i) (Finset.mem_univ _))

lemma quasilinear_family_bootstrap (B : G →L[ℝ] (E →L[ℝ] E →L[ℝ] F) →L[ℝ] F)
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
    (hcoeff : ∀ m K, IsCompact K → K ⊆ U → ∃ C : ℝ, 1 ≤ C ∧ ‖B‖ ≤ C ∧
      (∀ j, j ≤ m → (Fintype.card (OrderedFinpartition j) : ℝ) ≤ C) ∧ ∀ s x, x ∈ K →
      ‖iteratedFDeriv ℝ 1 (u s) x‖ ≤ C ∧
      (∀ j, j ≤ m → ‖iteratedFDeriv ℝ j a (u s x)‖ ≤ C) ∧
      (∀ j, j ≤ m → ‖iteratedFDeriv ℝ j b (firstJet (u s) x)‖ ≤ C) ∧
      (∀ j, j ≤ m → ‖iteratedFDeriv ℝ j (r s) x‖ ≤ C)) :
    ∀ m, 1 ≤ m → ∀ K, IsCompact K → K ⊆ U →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s x, x ∈ K → ‖iteratedFDeriv ℝ m (u s) x‖ ≤ C := by
  apply residual_family_bootstrap hU e u τ hu hframes
  · intro K hK hKU
    obtain ⟨C,hC,_,_,hc⟩ := hcoeff 1 K hK hKU
    exact ⟨C,by linarith,fun s x hx => (hc s x hx).1⟩
  · intro K hK hKU
    obtain ⟨C,hC,hB,hP,hc⟩ := hcoeff 2 K hK hKU
    have hC0 : 0 ≤ C := by linarith
    let R1 := 2*C+C^2+C^3
    let R2 := C+3*C^2+5*C^3+C^4+C^5
    have hR1 : 0 ≤ R1 := by dsimp [R1]; positivity
    have hR2 : 0 ≤ R2 := by dsimp [R2]; positivity
    refine ⟨R1+R2,add_nonneg hR1 hR2,fun s x hx => ?_⟩
    obtain ⟨hl1,hl2⟩ := quasilinear_low_residuals B hU (hu s) (hr s) (ha s) (hb s)
      (heq s) (hKU hx) (fun i => τ s x (e i)) (hframe s x (hKU hx)) e hC0 hB (hP 2 le_rfl)
      (hc s x hx).1 (hc s x hx).2.1 (hc s x hx).2.2.1 (hc s x hx).2.2.2
    exact ⟨fun σ => (hl1 σ).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hR2) (by positivity)),
      fun σ => (hl2 σ).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hR1) (by positivity))⟩
  · intro m hm K hK hKU hlo
    obtain ⟨C0,hC0,hB,hP,hc⟩ := hcoeff m K hK hKU
    obtain ⟨C1,hC1,hlo'⟩ := energy_bounds_finite_norms hU e hu hKU m hlo
    let C := C0+C1
    have hC : 1 ≤ C := by dsimp [C]; linarith
    have hc0 : C0 ≤ C := by dsimp [C]; linarith
    have hc1 : C1 ≤ C := by dsimp [C]; linarith
    refine ⟨C+C^(m+2)*C+C*2^m*C^(m+2)*C,by
      have hCnonneg : 0 ≤ C := by linarith
      positivity,fun s x hx => ?_⟩
    exact quasilinear_high_residual B hU (hu s) (hr s) (ha s) (hb s) (heq s) (hKU hx)
      (fun i => τ s x (e i)) (hframe s x (hKU hx)) e hm hC (hB.trans hc0)
      (fun j hj => (hP j hj).trans hc0) (fun j hj hjm => (hlo' j hj hjm s x hx).trans hc1)
      (fun j hj => ((hc s x hx).2.1 j hj).trans hc0)
      (fun j hj => ((hc s x hx).2.2.1 j hj).trans hc0) (((hc s x hx).2.2.2 m le_rfl).trans hc0)
end HigherJet

end
end

end OAI
