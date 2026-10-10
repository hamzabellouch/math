import Mathlib
import OAI.Geometry.PrescribedPotential.HigherJetComposition
import OAI.Geometry.PrescribedPotential.QuasilinearLowResiduals

namespace OAI

/-! Quasilinear High Residuals. -/

section

 

noncomputable section
open Set Filter Topology Finset
open scoped ContDiff
namespace HigherJet
variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
local instance highHessianNormed : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance highHessianSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance

lemma coefficient_prefactor {m i : ℕ} (hi : i ≤ m) {C : ℝ} (hC : 1 ≤ C)
    (hP : (Fintype.card (OrderedFinpartition i) : ℝ) ≤ C) :
    (Fintype.card (OrderedFinpartition i) : ℝ)*C*C^i ≤ C^(m+2) := by
  calc
    _ ≤ C*C*C^i := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hP (by linarith)) (by positivity)
    _ = C^(i+2) := by ring
    _ ≤ C^(m+2) := pow_le_pow_right₀ hC (by omega)

lemma high_coefficient_bounds {u : E → F} {a : F → G} {b : F × (E →L[ℝ] F) → F} {x : E}
    (hu : ContDiffAt ℝ ∞ u x) (ha : ContDiffAt ℝ ∞ a (u x))
    (hb : ContDiffAt ℝ ∞ b (firstJet u x)) {m : ℕ} (hm : 3 ≤ m) {C : ℝ} (hC : 1 ≤ C)
    (hP : ∀ i, i ≤ m → (Fintype.card (OrderedFinpartition i) : ℝ) ≤ C)
    (hulow : ∀ j, 0 < j → j < m → ‖iteratedFDeriv ℝ j u x‖ ≤ C)
    (haj : ∀ j, j ≤ m → ‖iteratedFDeriv ℝ j a (u x)‖ ≤ C)
    (hbj : ∀ j, j ≤ m → ‖iteratedFDeriv ℝ j b (firstJet u x)‖ ≤ C) :
    (∀ i, 0 < i → i < m → ‖iteratedFDeriv ℝ i (a ∘ u) x‖ ≤ C^(m+2)) ∧
    ‖iteratedFDeriv ℝ m (a ∘ u) x‖ ≤ C^(m+2)*(1+‖iteratedFDeriv ℝ m u x‖) ∧
    ‖iteratedFDeriv ℝ m (b ∘ firstJet u) x‖ ≤
      C^(m+2)*C*(1+‖iteratedFDeriv ℝ m u x‖+‖iteratedFDeriv ℝ (m+1) u x‖) := by
  have hC0 : 0 ≤ C := by linarith
  refine ⟨?_,?_,?_⟩
  · intro i hi him
    have h := composition_top_jet_bound hu ha (m := i) (r := i+1) (by omega) hC
      (show (1:ℝ) ≤ 1 by rfl) hC0
      (fun j hj hji => hulow j hj (by omega))
      (fun j hj hji => by omega) (fun j hj => haj j (by omega))
    simpa only [mul_one] using h.trans (by simpa only [mul_one] using coefficient_prefactor (Nat.le_of_lt him) hC (hP i (Nat.le_of_lt him)))
  · exact (composition_top_jet_bound hu ha (m := m) (r := m) (by omega) hC
      (le_add_of_nonneg_right (norm_nonneg _)) hC0 hulow
      (fun j hj hjm => by
        have he : j=m := by omega
        rw [he]
        exact le_add_of_nonneg_left zero_le_one)
      haj).trans (mul_le_mul_of_nonneg_right (coefficient_prefactor (le_refl m) hC (hP m le_rfl)) (by positivity))
  · let T := C+‖iteratedFDeriv ℝ m u x‖+‖iteratedFDeriv ℝ (m+1) u x‖
    have hT : 1 ≤ T := by dsimp [T]; linarith [norm_nonneg (iteratedFDeriv ℝ m u x),norm_nonneg (iteratedFDeriv ℝ (m+1) u x)]
    have hlow (j : ℕ) (hj : 0 < j) (hjm : j < m-1) : ‖iteratedFDeriv ℝ j (firstJet u) x‖ ≤ C := by
      rw [norm_firstJet_deriv hu]
      exact max_le (hulow j hj (by omega)) (hulow (j+1) (by omega) (by omega))
    have hhigh (j : ℕ) (hj : m-1 ≤ j) (hjm : j ≤ m) : ‖iteratedFDeriv ℝ j (firstJet u) x‖ ≤ T := by
      rw [norm_firstJet_deriv hu]
      by_cases he : j=m
      · subst j
        dsimp [T]
        exact max_le (by linarith [norm_nonneg (iteratedFDeriv ℝ (m+1) u x)]) (by linarith [norm_nonneg (iteratedFDeriv ℝ m u x)])
      · have he : j+1=m := by omega
        rw [he]
        dsimp [T]
        exact max_le ((hulow j (by omega) (by omega)).trans (by linarith [norm_nonneg (iteratedFDeriv ℝ m u x),norm_nonneg (iteratedFDeriv ℝ (m+1) u x)]))
          (by linarith [norm_nonneg (iteratedFDeriv ℝ (m+1) u x)])
    apply (composition_top_jet_bound (firstJet_smoothAt hu) hb (r := m-1) (by omega) hC hT hC0 hlow hhigh hbj).trans
    have ht : T ≤ C*(1+‖iteratedFDeriv ℝ m u x‖+‖iteratedFDeriv ℝ (m+1) u x‖) := by
      dsimp [T]
      nlinarith only [mul_nonneg (by linarith : 0 ≤ C-1) (norm_nonneg (iteratedFDeriv ℝ m u x)),
        mul_nonneg (by linarith : 0 ≤ C-1) (norm_nonneg (iteratedFDeriv ℝ (m+1) u x))]
    exact (mul_le_mul (coefficient_prefactor (le_refl m) hC (hP m le_rfl)) ht (by linarith) (by positivity)).trans_eq (by ring)

variable {ι : Type*} [Fintype ι]
lemma quasilinear_high_residual (B : G →L[ℝ] (E →L[ℝ] E →L[ℝ] F) →L[ℝ] F)
    {U : Set E} (hU : IsOpen U) {u r : E → F} {a : F → G} {b : F × (E →L[ℝ] F) → F}
    (hu : ContDiffOn ℝ ∞ u U) (hr : ContDiffOn ℝ ∞ r U)
    (ha : ∀ y ∈ U, ContDiffAt ℝ ∞ a (u y))
    (hb : ∀ y ∈ U, ContDiffAt ℝ ∞ b (firstJet u y))
    (heq : ∀ y ∈ U, B (a (u y)) (hessian u y) = r y+b (firstJet u y))
    {x : E} (hx : x ∈ U) (v : ι → E)
    (hframe : ∀ H : E →L[ℝ] E →L[ℝ] F, B (a (u x)) H = ∑ i, H (v i) (v i))
    (e : OrthonormalBasis ι ℝ E) {m : ℕ} (hm : 3 ≤ m) {C : ℝ} (hC : 1 ≤ C) (hB : ‖B‖ ≤ C)
    (hP : ∀ i, i ≤ m → (Fintype.card (OrderedFinpartition i) : ℝ) ≤ C)
    (hulow : ∀ j, 0 < j → j < m → ‖iteratedFDeriv ℝ j u x‖ ≤ C)
    (haj : ∀ j, j ≤ m → ‖iteratedFDeriv ℝ j a (u x)‖ ≤ C)
    (hbj : ∀ j, j ≤ m → ‖iteratedFDeriv ℝ j b (firstJet u x)‖ ≤ C)
    (hrj : ‖iteratedFDeriv ℝ m r x‖ ≤ C) :
    ∀ σ : Fin m → ι, ‖frameLaplace v (jetFamily e m u σ) x‖ ≤
      (C+C^(m+2)*C+C*2^m*C^(m+2)*C)*(1+‖iteratedFDeriv ℝ m u x‖+‖iteratedFDeriv ℝ (m+1) u x‖) := by
  have hC0 : 0 ≤ C := by linarith
  have hac : ContDiffOn ℝ ∞ (a ∘ u) U := fun y hy => ((ha y hy).comp y (hu.contDiffAt (hU.mem_nhds hy))).contDiffWithinAt
  have hbc : ContDiffOn ℝ ∞ (b ∘ firstJet u) U := fun y hy => ((hb y hy).comp y (firstJet_smoothAt (hu.contDiffAt (hU.mem_nhds hy)))).contDiffWithinAt
  obtain ⟨halow,hatop,hbtop⟩ := high_coefficient_bounds (hu.contDiffAt (hU.mem_nhds hx)) (ha x hx) (hb x hx) hm hC hP hulow haj hbj
  let T := 1+‖iteratedFDeriv ℝ m u x‖+‖iteratedFDeriv ℝ (m+1) u x‖
  have hT : 1 ≤ T := by dsimp [T]; linarith [norm_nonneg (iteratedFDeriv ℝ m u x),norm_nonneg (iteratedFDeriv ℝ (m+1) u x)]
  have hprod (i : ℕ) (hi : 0 < i) (him : i ≤ m) :
      ‖iteratedFDeriv ℝ i (a ∘ u) x‖*‖iteratedFDeriv ℝ (m-i) (hessian u) x‖ ≤ (C^(m+2)*C)*T := by
    rw [norm_hessian_deriv]
    by_cases he : i=m
    · subst i
      have hm2 : m-m+2=2 := by omega
      rw [hm2]
      have h2 := hulow 2 (by decide) (by omega)
      have hh : 1+‖iteratedFDeriv ℝ m u x‖ ≤ T := by dsimp [T]; exact le_add_of_nonneg_right (norm_nonneg _)
      calc
        _ ≤ (C^(m+2)*(1+‖iteratedFDeriv ℝ m u x‖))*C := mul_le_mul hatop h2 (norm_nonneg _) (by positivity)
        _ = (C^(m+2)*C)*(1+‖iteratedFDeriv ℝ m u x‖) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hh (by positivity)
    · have hi' : i < m := by omega
      have hh : ‖iteratedFDeriv ℝ (m-i+2) u x‖ ≤ C*T := by
        by_cases h1 : i=1
        · subst i
          have he : m-1+2=m+1 := by omega
          rw [he]
          exact (show ‖iteratedFDeriv ℝ (m+1) u x‖ ≤ T by dsimp [T]; linarith [norm_nonneg (iteratedFDeriv ℝ m u x)]).trans (le_mul_of_one_le_left (by linarith) hC)
        · by_cases h2 : i=2
          · subst i
            have he : m-2+2=m := by omega
            rw [he]
            exact (show ‖iteratedFDeriv ℝ m u x‖ ≤ T by dsimp [T]; linarith [norm_nonneg (iteratedFDeriv ℝ (m+1) u x)]).trans (le_mul_of_one_le_left (by linarith) hC)
          · exact (hulow _ (by omega) (by omega)).trans (le_mul_of_one_le_right hC0 hT)
      exact (mul_le_mul (halow i hi hi') hh (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have hcomm := frozen_product_tame_bound B hU hac (hessian_smoothOn hU hu) hx m
    (show 0 ≤ C^(m+2)*C by positivity) (show 0 ≤ T by linarith) hprod
  intro σ
  have hnorm := (frozen_equation_jet_norm B hU hu (hr.add hbc) hac heq hx v hframe e m σ).trans
    (add_le_add (norm_iteratedFDeriv_add_le (hr.contDiffAt (hU.mem_nhds hx)) (hbc.contDiffAt (hU.mem_nhds hx)) m) le_rfl)
  have hcomm' : ‖iteratedFDeriv ℝ m (fun y => B (a (u y)-a (u x)) (hessian u y)) x‖ ≤ (C*2^m*C^(m+2)*C)*T :=
    hcomm.trans (by nlinarith only [mul_le_mul_of_nonneg_right hB (show 0 ≤ 2^m*(C^(m+2)*C)*T by positivity)])
  have hr' : ‖iteratedFDeriv ℝ m r x‖ ≤ C*T := hrj.trans (le_mul_of_one_le_right hC0 hT)
  change _ ≤ (C+C^(m+2)*C+C*2^m*C^(m+2)*C)*T
  change _ ≤ C^(m+2)*C*T at hbtop
  exact (hnorm.trans (add_le_add (add_le_add hr' hbtop) hcomm')).trans_eq (by ring)
end HigherJet

end
end

end OAI
