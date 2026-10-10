import OAI.Dynamics.ConditionalShuffle.FiniteMinorization

namespace OAI

noncomputable section
open scoped BigOperators Classical
open Filter Topology
namespace Thorp.Conditional.Reset

lemma kernel_add (D b s t : ℕ) (x y : Injection D b) :
    kernel D b (s+t) x y = ∑ z, kernel D b s x z * kernel D b t z y := by
  unfold kernel
  rw [fairMass_test, fairMass_eq_mean, mean_history_add]
  apply mean_congr; intro ω
  rw [fairMass_eq_mean]
  apply mean_congr; intro η
  rw [Reachability.run_append, act_mul]

lemma reset_minorization (ρ : ℝ) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) :
    ∀ᶠ d : ℕ in atTop, ∀ (b : ℕ), (b : ℝ) ≤ (1-ρ)*(2^(d+2) : ℝ) →
      ∀ x y : Injection (d+2) b,
        (1-2*(1/2 : ℝ)^(8*(d+2))) / Fintype.card (Injection (d+2) b) ≤
          kernel (d+2) b (4*resetS ρ*(d+2)) x y := by
  filter_upwards [kernel_row_bound ρ hρ hρ₁, kernel_column_bound ρ hρ hρ₁] with d hr hc
  intro b hb x y
  let : Nonempty (Injection (d+2) b) := ⟨x⟩
  have hh := square_minorization (kernel (d+2) b (2*resetS ρ*(d+2)))
    (kernel_nonneg _ _ _) (kernel_row_sum _ _ _) (kernel_column_sum _ _ _)
    ((1/2 : ℝ)^(8*(d+2))) (hr b hb) (hc b hb) x y
  have ht : 4*resetS ρ*(d+2) = 2*resetS ρ*(d+2)+2*resetS ρ*(d+2) := by ring
  rw [ht, kernel_add]
  exact hh

def resetRho : ℝ := (2 : ℝ)⁻¹^20

def resetBlocks : ℕ := 128

def resetSuccess (D : ℕ) : ℝ := 1-2*(1/2 : ℝ)^(8*D)

lemma resetSuccess_pos (d : ℕ) : 0 < resetSuccess (d+2) := by
  have hh : (1/2 : ℝ)^(8*(d+2)) ≤ (1/2 : ℝ)^2 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  norm_num at hh
  unfold resetSuccess; linarith

lemma resetS_exact : resetS resetRho = 335544320 := by norm_num [resetS, resetRho]

lemma reset_time_exact : resetBlocks*(4*resetS resetRho+1) = 171798691968 := by
  rw [resetS_exact]; rfl

theorem reset_split :
    ∀ᶠ d : ℕ in atTop, ∀ (b : ℕ), (b : ℝ) ≤ (1-resetRho)*(2^(d+2) : ℝ) →
      ∀ x : Injection (d+2) b,
        (∀ y, 0 ≤ acceptance (kernel (d+2) b (4*resetS resetRho*(d+2))) (resetSuccess (d+2)) x y ∧
          acceptance (kernel (d+2) b (4*resetS resetRho*(d+2))) (resetSuccess (d+2)) x y ≤ 1) ∧
        (∀ y, markedKernel (kernel (d+2) b (4*resetS resetRho*(d+2))) (resetSuccess (d+2)) x (y,true) =
          resetSuccess (d+2) / Fintype.card (Injection (d+2) b)) ∧
        (∀ y, (∑ z : Bool, markedKernel (kernel (d+2) b (4*resetS resetRho*(d+2)))
          (resetSuccess (d+2)) x (y,z)) = kernel (d+2) b (4*resetS resetRho*(d+2)) x y) ∧
        (∑ z, markedKernel (kernel (d+2) b (4*resetS resetRho*(d+2))) (resetSuccess (d+2)) x z) = 1 := by
  filter_upwards [reset_minorization resetRho (by norm_num [resetRho]) (by norm_num [resetRho])] with d hd
  intro b hb x
  let : Nonempty (Injection (d+2) b) := ⟨x⟩
  have hm := hd b hb
  exact ⟨acceptance_bounds _ _ (resetSuccess_pos d) hm x,
    marked_true _ _ (resetSuccess_pos d) hm x,
    marked_marginal _ _ x, marked_sum _ _ (kernel_row_sum _ _ _) x⟩

end Thorp.Conditional.Reset

end

end OAI
