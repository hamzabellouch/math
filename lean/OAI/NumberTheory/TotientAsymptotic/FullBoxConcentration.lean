import OAI.NumberTheory.TotientAsymptotic.PhaseBandTransfer
import OAI.NumberTheory.TotientAsymptotic.FullPrimeGrid
import OAI.NumberTheory.TotientAsymptotic.ConcentrationTail

namespace OAI

/-! Concentration for the actual phase bands in the enlarged full simplex. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory

namespace TotientAsymptotic

def fullBoxSimplex (x : ℝ) (N : ℕ) : Set (Fin N → ℝ) :=
  enlargedSimplex N (B x) (1+simplexBoxError 4 (m x))
    (fun i => 1+simplexBoxError 4 (m x-(i.val+1)))

def phaseCoordinateBad (x : ℝ) {N : ℕ} (i : Fin N) : Set (Fin N → ℝ) :=
  {u | u i < (91/100 : ℝ)*bandScale x (i.val+1) ∨
    (109/100 : ℝ)*bandScale x (i.val+1) < u i}

/-- Ford concentration at the actual manuscript phase bands, with the
Jacobian and truncation costs explicit. -/
theorem full_box_coordinate_concentration (hford : FordCoordinateConcentrationInput) :
    ∃ C c : ℝ, ∃ N₀ : ℕ, 0 < C ∧ 0 < c ∧
    ∀ {x : ℝ} {H N : ℕ}, N₀ ≤ N → 0 < B x → H ≤ m x →
      m x-P H=N+2 → P H+2 ≤ H → 100*P H ≤ H →
      Real.exp (simplexBoxTail 4 H) ≤ (102/100 : ℝ) →
      (∀ k < m x, (99/100 : ℝ)*fullSimplexCenter (m x) (B x) k ≤ bandScale x k ∧
        bandScale x k ≤ (101/100 : ℝ)*fullSimplexCenter (m x) (B x) k) →
    ∀ i : Fin (N+2), i.val < R x H →
      volume.real (fullBoxSimplex x (N+2) ∩ phaseCoordinateBad x i) ≤
        Real.exp (simplexBoxTail 4 (P H))*C*
          Real.exp (-c*(N+2-(i.val+1) : ℕ))*G x (N+2) := by
  obtain ⟨C, c, N₀, hC, hc, hconc⟩ := scaled_coarse_concentration hford
  refine ⟨C, c, N₀, hC, hc, ?_⟩
  intro x H N hN hB hHm hdim hPH h100 hsmall hcenter i hi
  let β : ℕ → ℝ := fun r => 1+simplexBoxError 4 (m x-r)
  let κ : Fin (N+2) → ℝ := enlargementScale β
  have hβ : ∀ r, 1 ≤ β r := fun r => by
    dsimp [β]
    linarith [simplexBoxError_nonneg (by norm_num : (0 : ℝ)≤4) (m x-r)]
  have hκ : ∀ j, 0 < κ j := enlargementScale_pos hβ
  have hik : i.val+1 < m x := by unfold R at hi; omega
  have hiN : i.val < N := by unfold R at hi; omega
  have hi100 : 100*P H ≤ m x-(i.val+1) := by unfold R at hi; omega
  have hk1 : 1 ≤ κ i := Finset.one_le_prod₀ (fun r _ => hβ r)
  have hkhi : κ i ≤ (102/100 : ℝ) := by
    apply (reverse_enlargement_coordinate hHm (simplexBoxError 4)
      (simplexBoxError_nonneg (by norm_num)) (summable_simplexBoxError_weighted 4) i hi).trans
    rw [← simplexBoxTail_eq_tsum]
    exact hsmall
  have hb := hconc N hN (m x) (P H) (B x) hB hdim (β 0)
    (fun j => β (j.val+1)) κ (zero_lt_one.trans_le (hβ 0))
    (fun j => zero_lt_one.trans_le (hβ (j.val+1))) hκ
    (enlargementScale_top hβ) (enlargementScale_step hβ) i (bandScale x (i.val+1))
    hiN hi100 (hcenter _ hik).1 (hcenter _ hik).2 hk1 hkhi
  have hvol : volume.real (prefixRegion (N+2) (B x) 0 0) = G x (N+2) := by
    rw [measureReal_def, volume_zero_prefixRegion hB.le (by omega),
      ENNReal.toReal_ofReal (G_pos hB _).le]
  rw [hvol] at hb
  have hp := reverse_enlargement_jacobian (show P H ≤ m x by omega)
    (simplexBoxError 4) (simplexBoxError_nonneg (by norm_num))
    (summable_simplexBoxError_weighted 4)
  rw [hdim, ← simplexBoxTail_eq_tsum] at hp
  calc
    _ ≤ (∏ j, κ j)*(C*Real.exp (-c*(N+2-(i.val+1) : ℕ))*G x (N+2)) := by
      simpa only [fullBoxSimplex, phaseCoordinateBad, β, Nat.sub_zero] using hb
    _ ≤ Real.exp (simplexBoxTail 4 (P H))*
        (C*Real.exp (-c*(N+2-(i.val+1) : ℕ))*G x (N+2)) :=
      mul_le_mul_of_nonneg_right hp (mul_nonneg (mul_pos hC (Real.exp_pos _)).le (G_pos hB _).le)
    _ = _ := by ring

def retainedPhaseBad (x : ℝ) (H N : ℕ) (hRN : R x H ≤ N) : Set (Fin N → ℝ) :=
  ⋃ i : Fin (R x H), fullBoxSimplex x N ∩ phaseCoordinateBad x (Fin.castLE hRN i)

/-- The loss for all retained coordinates is an exponential tail in `H`,
with no growing dimension factor. -/
theorem full_box_retained_concentration (hford : FordCoordinateConcentrationInput) :
    ∃ C c : ℝ, ∃ N₀ : ℕ, 0 < C ∧ 0 < c ∧
    ∀ {x : ℝ} {H N : ℕ}, N₀ ≤ N → 0 < B x → H ≤ m x →
      m x-P H=N+2 → P H+2 ≤ H → 100*P H ≤ H → 2*P H ≤ H →
      Real.exp (simplexBoxTail 4 H) ≤ (102/100 : ℝ) →
      (∀ k < m x, (99/100 : ℝ)*fullSimplexCenter (m x) (B x) k ≤ bandScale x k ∧
        bandScale x k ≤ (101/100 : ℝ)*fullSimplexCenter (m x) (B x) k) →
      ∀ hRN : R x H ≤ N+2,
      volume.real (retainedPhaseBad x H (N+2) hRN) ≤
        (Real.exp (simplexBoxTail 4 (P H))*C*G x (N+2))*
          ((Real.exp (-c/2))^H/(1-Real.exp (-c/2))) := by
  obtain ⟨C, c, N₀, hC, hc, hconc⟩ := full_box_coordinate_concentration hford
  refine ⟨C, c, N₀, hC, hc, ?_⟩
  intro x H N hN hB hHm hdim hPH h100 hhalf hsmall hcenter hRN
  have heach (i : Fin (R x H)) :=
    hconc hN hB hHm hdim hPH h100 hsmall hcenter (Fin.castLE hRN i) i.isLt
  have hgeo := sum_retained_concentration hc hHm hhalf
  change (∑ i : Fin (R x H), Real.exp (-c*((m x-P H-(i.val+1) : ℕ) : ℝ))) ≤ _ at hgeo
  rw [hdim] at hgeo
  have hfactor : 0 ≤ Real.exp (simplexBoxTail 4 (P H))*C*G x (N+2) :=
    mul_nonneg (mul_pos (Real.exp_pos _) hC).le (G_pos hB _).le
  calc
    _ ≤ ∑ i : Fin (R x H), volume.real
        (fullBoxSimplex x (N+2) ∩ phaseCoordinateBad x (Fin.castLE hRN i)) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ i : Fin (R x H), Real.exp (simplexBoxTail 4 (P H))*C*
        Real.exp (-c*((N+2-(i.val+1) : ℕ) : ℝ))*G x (N+2) := by
      exact Finset.sum_le_sum (fun i _ => heach i)
    _ = (Real.exp (simplexBoxTail 4 (P H))*C*G x (N+2))*
        ∑ i : Fin (R x H), Real.exp (-c*((N+2-(i.val+1) : ℕ) : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hgeo hfactor

end TotientAsymptotic

end

end OAI
