import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarPrimitiveBounds
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarBranchAnchors

namespace OAI

/-! Effective rational bounds for dependence of one entire branch on its
source point. The same bound covers all eight anchors and all partial pulses. -/

noncomputable section
namespace ForcedComputation.Recorder.Planar

open ShearFlows PlanarHamiltonian PlanarRouting Set
open scoped BigOperators

def branchExpansion (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) : ℚ :=
  ∑ k : Fin 8, (⟨b, ownPhase k⟩ : Action M hM).primitive.growth

def branchGrowth (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) : ℚ := (branchExpansion M hM b) ^ 8

def branchRadius (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) : ℚ := routingCollar M hM / (2 * branchGrowth M hM b)

theorem primitive_growth_le_expansion (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) (k : Fin 8) :
    (⟨b, ownPhase k⟩ : Action M hM).primitive.growth ≤ branchExpansion M hM b := by
  unfold branchExpansion
  apply Finset.single_le_sum (s := Finset.univ)
    (f := fun j : Fin 8 => (⟨b, ownPhase j⟩ : Action M hM).primitive.growth)
  · intro j _
    exact (by norm_num : (0 : ℚ) ≤ 1).trans (Primitive.growth_one_le _)
  · exact Finset.mem_univ k

theorem branchExpansion_one_le (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) : 1 ≤ branchExpansion M hM b :=
  (Primitive.growth_one_le _).trans (primitive_growth_le_expansion M hM b 0)

theorem branchGrowth_one_le (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) : 1 ≤ branchGrowth M hM b := by
  exact one_le_pow₀ (branchExpansion_one_le M hM b)

theorem branchRadius_pos (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) : 0 < branchRadius M hM b :=
  div_pos (routingCollar_pos M hM)
    (mul_pos (by norm_num) (lt_of_lt_of_le (by norm_num) (branchGrowth_one_le M hM b)))

theorem branchAnchor_sub_bound (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) (x y : Plane) (k : Fin 9) :
    ‖branchAnchors M hM b x k - branchAnchors M hM b y k‖ ≤
      (branchExpansion M hM b : ℝ) ^ k.val * ‖x - y‖ := by
  have hE : (1 : ℝ) ≤ branchExpansion M hM b := by exact_mod_cast branchExpansion_one_le M hM b
  have hE₀ : (0 : ℝ) ≤ branchExpansion M hM b := le_trans (by norm_num) hE
  refine Fin.induction ?_ ?_ k
  · simp only [branchAnchors_first, Fin.val_zero, pow_zero, one_mul, le_refl]
  · intro j ih
    let p := (⟨b, ownPhase j⟩ : Action M hM).primitive
    have hp₀ : (0 : ℝ) ≤ p.growth := by exact_mod_cast
      ((by norm_num : (0 : ℚ) ≤ 1).trans p.growth_one_le)
    have hp : (p.growth : ℝ) ≤ branchExpansion M hM b := by
      exact_mod_cast primitive_growth_le_expansion M hM b j
    rw [← branchAnchors_endpoint M hM b x j, ← branchAnchors_endpoint M hM b y j]
    calc
      ‖p.endpoint (branchAnchors M hM b x j.castSucc) -
          p.endpoint (branchAnchors M hM b y j.castSucc)‖ ≤
          (p.growth : ℝ) * ‖branchAnchors M hM b x j.castSucc -
            branchAnchors M hM b y j.castSucc‖ := p.endpoint_sub_bound _ _
      _ ≤ (p.growth : ℝ) * ((branchExpansion M hM b : ℝ) ^ j.val * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left ih hp₀
      _ ≤ (branchExpansion M hM b : ℝ) * ((branchExpansion M hM b : ℝ) ^ j.val * ‖x - y‖) :=
        mul_le_mul_of_nonneg_right hp (mul_nonneg (pow_nonneg hE₀ _) (norm_nonneg _))
      _ = (branchExpansion M hM b : ℝ) ^ j.succ.val * ‖x - y‖ := by
        simp only [Fin.val_succ, pow_succ]
        ring

theorem branchAnchor_sub_uniform (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) (x y : Plane) (k : Fin 9) :
    ‖branchAnchors M hM b x k - branchAnchors M hM b y k‖ ≤
      (branchGrowth M hM b : ℝ) * ‖x - y‖ := by
  have hE : (1 : ℝ) ≤ branchExpansion M hM b := by exact_mod_cast branchExpansion_one_le M hM b
  have hk : k.val ≤ 8 := by omega
  have hg : (branchExpansion M hM b : ℝ) ^ k.val ≤ (branchGrowth M hM b : ℝ) := by
    simpa only [branchGrowth, Rat.cast_pow] using pow_le_pow_right₀ hE hk
  exact (branchAnchor_sub_bound M hM b x y k).trans
    (mul_le_mul_of_nonneg_right hg (norm_nonneg _))

theorem branchPath_sub_uniform (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) (x y : Plane) (k : Fin 8)
    (θ : ℝ → ℝ) (t : ℝ) (hθ : θ t ∈ Icc (0 : ℝ) 1) :
    ‖(⟨b, ownPhase k⟩ : Action M hM).primitive.path θ (branchAnchors M hM b x k.castSucc) t -
      (⟨b, ownPhase k⟩ : Action M hM).primitive.path θ (branchAnchors M hM b y k.castSucc) t‖ ≤
      (branchGrowth M hM b : ℝ) * ‖x - y‖ := by
  let p := (⟨b, ownPhase k⟩ : Action M hM).primitive
  have hE : (1 : ℝ) ≤ branchExpansion M hM b := by exact_mod_cast branchExpansion_one_le M hM b
  have hE₀ : (0 : ℝ) ≤ branchExpansion M hM b := le_trans (by norm_num) hE
  have hp₀ : (0 : ℝ) ≤ p.growth := by exact_mod_cast
    ((by norm_num : (0 : ℚ) ≤ 1).trans p.growth_one_le)
  have hp : (p.growth : ℝ) ≤ branchExpansion M hM b := by
    exact_mod_cast primitive_growth_le_expansion M hM b k
  have hk : k.val + 1 ≤ 8 := k.isLt
  have hg : (branchExpansion M hM b : ℝ) ^ (k.val + 1) ≤ (branchGrowth M hM b : ℝ) := by
    simpa only [branchGrowth, Rat.cast_pow] using pow_le_pow_right₀ hE hk
  calc
    _ ≤ (p.growth : ℝ) * ‖branchAnchors M hM b x k.castSucc - branchAnchors M hM b y k.castSucc‖ :=
      p.path_sub_bound _ _ θ t hθ
    _ ≤ (p.growth : ℝ) * ((branchExpansion M hM b : ℝ) ^ k.val * ‖x - y‖) :=
      mul_le_mul_of_nonneg_left (branchAnchor_sub_bound M hM b x y k.castSucc) hp₀
    _ ≤ (branchExpansion M hM b : ℝ) * ((branchExpansion M hM b : ℝ) ^ k.val * ‖x - y‖) :=
      mul_le_mul_of_nonneg_right hp (mul_nonneg (pow_nonneg hE₀ _) (norm_nonneg _))
    _ = (branchExpansion M hM b : ℝ) ^ (k.val + 1) * ‖x - y‖ := by rw [pow_succ]; ring
    _ ≤ (branchGrowth M hM b : ℝ) * ‖x - y‖ := mul_le_mul_of_nonneg_right hg (norm_nonneg _)

theorem growth_mul_radius (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) :
    (branchGrowth M hM b : ℝ) * (branchRadius M hM b : ℝ) = (routingCollar M hM : ℝ) / 2 := by
  have hg : (branchGrowth M hM b : ℝ) ≠ 0 := by
    have h : (1 : ℝ) ≤ branchGrowth M hM b := by exact_mod_cast branchGrowth_one_le M hM b
    linarith
  simp only [branchRadius, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat]
  field_simp

theorem branchAnchor_dist_lt_collar (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) {x y : Plane}
    (hxy : dist x y < (branchRadius M hM b : ℝ)) (k : Fin 9) :
    dist (branchAnchors M hM b x k) (branchAnchors M hM b y k) < (routingCollar M hM : ℝ) / 2 := by
  have hg : (0 : ℝ) < branchGrowth M hM b := by
    have h : (1 : ℝ) ≤ branchGrowth M hM b := by exact_mod_cast branchGrowth_one_le M hM b
    linarith
  calc
    _ ≤ (branchGrowth M hM b : ℝ) * dist x y := by
      simpa only [dist_eq_norm] using branchAnchor_sub_uniform M hM b x y k
    _ < (branchGrowth M hM b : ℝ) * (branchRadius M hM b : ℝ) := mul_lt_mul_of_pos_left hxy hg
    _ = _ := growth_mul_radius M hM b

theorem branchPath_dist_lt_collar (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) {x y : Plane}
    (hxy : dist x y < (branchRadius M hM b : ℝ)) (k : Fin 8)
    (θ : ℝ → ℝ) (t : ℝ) (hθ : θ t ∈ Icc (0 : ℝ) 1) :
    dist ((⟨b, ownPhase k⟩ : Action M hM).primitive.path θ (branchAnchors M hM b x k.castSucc) t)
      ((⟨b, ownPhase k⟩ : Action M hM).primitive.path θ (branchAnchors M hM b y k.castSucc) t) <
        (routingCollar M hM : ℝ) / 2 := by
  have hg : (0 : ℝ) < branchGrowth M hM b := by
    have h : (1 : ℝ) ≤ branchGrowth M hM b := by exact_mod_cast branchGrowth_one_le M hM b
    linarith
  calc
    _ ≤ (branchGrowth M hM b : ℝ) * dist x y := by
      simpa only [dist_eq_norm] using branchPath_sub_uniform M hM b x y k θ t hθ
    _ < (branchGrowth M hM b : ℝ) * (branchRadius M hM b : ℝ) := mul_lt_mul_of_pos_left hxy hg
    _ = _ := growth_mul_radius M hM b

def branchNeighborhood (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) : Set Plane :=
  {y | ∃ x ∈ (instruction M hM b).source.carrier, dist y x < (branchRadius M hM b : ℝ)}

theorem source_subset_branchNeighborhood (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) :
    (instruction M hM b).source.carrier ⊆ branchNeighborhood M hM b := by
  intro x hx
  refine ⟨x, hx, ?_⟩
  simpa only [dist_self] using (show (0 : ℝ) < branchRadius M hM b by exact_mod_cast branchRadius_pos M hM b)

end ForcedComputation.Recorder.Planar

end

end OAI
