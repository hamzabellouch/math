import OAI.MeasureTheory.Falconer.Estimates.RootLeibniz
import OAI.MeasureTheory.Falconer.Shells.HighShellNormalization
import OAI.MeasureTheory.Falconer.Fourier.GraphKernelBounds

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem root_assignment_budgets (d e : RootEndpointData) (k : RootMaskIndex → ℕ)
    (K : ℕ) (hk : ∑ b ∈ rootMaskIndices d e, k b ≤ K) :
    (∑ b ∈ d.S, k (.inl b)) ≤ K ∧ (∑ b ∈ e.S, k (.inr b)) ≤ K := by
  simp only [rootMaskIndices,Finset.sum_disjSum] at hk
  constructor <;> omega

theorem root_assignment_scale (d e : RootEndpointData) (N j : ℕ) {sig : ℝ} (hsig : 0 ≤ sig)
    (hL₁ : ∀ b ∈ d.S, descriptorLength b ≤ N/2)
    (hL₂ : ∀ b ∈ e.S, descriptorLength b ≤ N/2)
    {b : ℂ × (RootMaskIndex → ℕ)} (hb : b ∈ inverseLeibnizTerms j (rootMaskIndices d e)) :
    rootAssignmentScale d e N sig b.2 ≤ (2:ℝ)^((j:ℝ)*(N:ℝ)) := by
  have hh := high_shell_extracted_scale (rootMaskIndices d e) rootMaskDescriptor b.2 (v := (N:ℝ)) hsig N 0 N j
  simp only [Nat.cast_zero,sub_zero] at hh
  apply hh
  · intro a ha
    have ha' : descriptorLength (rootMaskDescriptor a) ≤ N/2 := by
      cases a with
      | inl a => exact hL₁ a (by simpa [rootMaskIndices] using ha)
      | inr a => exact hL₂ a (by simpa [rootMaskIndices] using ha)
    have hn : 2*descriptorLength (rootMaskDescriptor a) ≤ N := by omega
    exact_mod_cast hn
  · exact Nat.cast_nonneg N
  · nlinarith [mul_nonneg hsig (Nat.cast_nonneg (α := ℝ) N)]
  · exact inverseLeibnizTerms_budget j _ hb

theorem root_assignment_scale_absorbed (d e : RootEndpointData) (N j : ℕ) {sig : ℝ}
    (hsig : 0 ≤ sig)
    (hL₁ : ∀ b ∈ d.S, descriptorLength b ≤ N/2)
    (hL₂ : ∀ b ∈ e.S, descriptorLength b ≤ N/2)
    {b : ℂ × (RootMaskIndex → ℕ)} (hb : b ∈ inverseLeibnizTerms j (rootMaskIndices d e)) :
    0 ≤ (2:ℝ)^(-(j:ℝ)*(N:ℝ))*rootAssignmentScale d e N sig b.2 ∧
    (2:ℝ)^(-(j:ℝ)*(N:ℝ))*rootAssignmentScale d e N sig b.2 ≤ 1 := by
  have hpos : 0 ≤ rootAssignmentScale d e N sig b.2 :=
    Finset.prod_nonneg (fun c _ => pow_nonneg (inv_nonneg.mpr (sourceAngularRadius_pos _ _ _).le) _)
  refine ⟨mul_nonneg (by positivity) hpos,?_⟩
  apply (mul_le_mul_of_nonneg_left (root_assignment_scale d e N j hsig hL₁ hL₂ hb)
    (by positivity : 0 ≤ (2:ℝ)^(-(j:ℝ)*(N:ℝ)))).trans_eq
  rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  convert Real.rpow_zero 2 using 2
  ring

theorem root_inverseLeibniz_cost (d e : RootEndpointData) (N j : ℕ)
    (hd : d.S.card ≤ (N+1)^3+1) (he : e.S.card ≤ (N+1)^3+1) :
    ((inverseLeibnizTerms j (rootMaskIndices d e)).map (fun b => ‖b.1‖)).sum ≤
      (inverseStationaryExpr j).cost * (4*((N:ℝ)+1)^3)^(2*j) := by
  apply (inverseLeibnizTerms_cost j _).trans
  apply mul_le_mul_of_nonneg_left _ (inverseStationaryExpr j).cost_nonneg
  apply pow_le_pow_left₀ (by positivity)
  have hd' : (d.S.card:ℝ) ≤ ((N:ℝ)+1)^3+1 := by exact_mod_cast hd
  have he' : (e.S.card:ℝ) ≤ ((N:ℝ)+1)^3+1 := by exact_mod_cast he
  have hp : 1 ≤ ((N:ℝ)+1)^3 := one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) N])
  simp only [rootMaskIndices,Finset.card_disjSum,Nat.cast_add]
  apply max_le <;> linarith

namespace RootEndpointData

theorem symbol_measurable (d : RootEndpointData) (N : ℕ) (sig : ℝ) (k : PolicyDescriptor → ℕ) :
    Measurable (fun z : Plane × UnitCircle => d.symbol N sig k (fun _ => 1) z.1 z.2) :=
  measurable_inheritedCircleSymbol _ _ _ _ _ _ _ _ _ _ _ _ measurable_const

theorem symbol_norm (d : RootEndpointData) (hd : 0 < d.Q.side) (N : ℕ) (sig : ℝ)
    (k : PolicyDescriptor → ℕ) (K : ℕ) (hk : ∑ b ∈ d.S, k b ≤ K) (x : Plane) (dir : UnitCircle) :
    ‖d.symbol N sig k (fun _ => 1) x dir‖ ≤ symbolDerivativeConstant K^K :=
  inheritedCircleSymbol_norm_le _ _ _ _ hd _ _ _ _ _ _ _ _ K hk x (by simp) dir

end RootEndpointData

end PlanarFalconer

end OAI
