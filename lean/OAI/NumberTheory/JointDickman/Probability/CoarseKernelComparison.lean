import OAI.NumberTheory.JointDickman.Probability.FiniteKernelBilinear
import OAI.NumberTheory.JointDickman.Arithmetic.LogarithmicMarginal

namespace OAI

/-! # Uniform coarse replacement of both bounded endpoint tests -/

namespace JointDickman
open Finset Filter

noncomputable def coarseGroupAverage {D R : Type*} [Fintype R]
    (u : D × R → ℝ) (a : D × R) : ℝ := finiteResidueAverage (fun r => u (a.1,r))

theorem finiteResidueAverage_square_le {R : Type*} [Fintype R] [Nonempty R]
    (f : R → ℝ) :
    (Fintype.card R : ℝ)*finiteResidueAverage f^2 ≤ ∑ r, f r^2 := by
  have hn : (0 : ℝ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  have hh := sum_mul_sq_le_sq_mul_sq univ (fun _ : R => (1 : ℝ)) f
  simp only [one_mul,one_pow,sum_const,card_univ,nsmul_eq_mul,mul_one] at hh
  have he : (Fintype.card R : ℝ)*finiteResidueAverage f^2 =
      (∑ r, f r)^2/(Fintype.card R : ℝ) := by
    unfold finiteResidueAverage
    field_simp
  rw [he]
  exact (div_le_iff₀ hn).mpr (by simpa only [mul_comm] using hh)

theorem coarseGroupAverage_energy {D R : Type*} [Fintype D] [Fintype R] [Nonempty R]
    (u : D × R → ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (∑ a : D × R, δ*coarseGroupAverage u a^2) ≤ ∑ a : D × R, δ*u a^2 := by
  simp only [Fintype.sum_prod_type,coarseGroupAverage]
  apply sum_le_sum
  intro d _
  have hh := mul_le_mul_of_nonneg_left (finiteResidueAverage_square_le (fun r => u (d,r))) hδ
  simpa only [sum_const,card_univ,nsmul_eq_mul,mul_sum,mul_assoc,mul_left_comm] using hh

theorem fullPrimeMass_unit_energy (B : ℕ)
    (g : (auxiliaryPrimes B → Bool) → ℝ) (hg : ∀ x, |g x| ≤ 1) :
    (∑ x, fullPrimeMass (auxiliaryPrimes B) x*g x^2) ≤ 1 := by
  calc
    _ ≤ ∑ x, fullPrimeMass (auxiliaryPrimes B) x*1 := by
      apply sum_le_sum
      intro x _
      exact mul_le_mul_of_nonneg_left (show g x^2 ≤ 1 by have hx := abs_le.mp (hg x); nlinarith)
        (fullPrimeMass_nonneg _ (auxiliaryPrimes_prime B) x)
    _ = 1 := by simpa only [mul_one,fullPrimeMass] using
      bernoulliSiteMass_sum (fun p : auxiliaryPrimes B => 1/(p.val : ℝ))

/-- A fixed coarse partition works for all bounded endpoint tests and every
kernel with a prescribed weighted absolute row and column bound. -/
theorem groupedManuscriptChannel_bilinear_coarse
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, 0 < m ∧ ∀ᶠ B : ℕ in atTop,
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      ∀ K : (Fin m × Fin (channelBlockCount m B)) →
        (Fin m × Fin (channelBlockCount m B)) → ℝ,
      ∀ A : ℝ, 0 ≤ A →
      (∀ a, (∑ b, channelMesh (channelFineCount m B)*|K a b|) ≤ A) →
      (∀ b, (∑ a, channelMesh (channelFineCount m B)*|K a b|) ≤ A) →
      |finiteKernelBilinear (fun _ => channelMesh (channelFineCount m B)) K
          (groupedManuscriptChannel m B g) (groupedManuscriptChannel m B h)-
        finiteKernelBilinear (fun _ => channelMesh (channelFineCount m B)) K
          (coarseGroupAverage (groupedManuscriptChannel m B g))
          (coarseGroupAverage (groupedManuscriptChannel m B h))| ≤ A*ε := by
  obtain ⟨C,hC,hbound⟩ := groupedManuscriptChannel_square_bound hSD hSW hM hMP
  let η := (ε/(2*Real.sqrt C))^2
  have hroot : 0 < Real.sqrt C := Real.sqrt_pos.mpr hC
  have hη : 0 < η := sq_pos_of_pos (div_pos hε (mul_pos (by norm_num) hroot))
  obtain ⟨m,hm,hcoarse⟩ := groupedManuscriptChannel_coarse_compactness hSD hSW hM hMP hη
  refine ⟨m,hm,?_⟩
  filter_upwards [hcoarse,hbound m hm,eventually_gt_atTop 0] with B he hb hB
  have hk : 0 < channelBlockCount m B := by
    have hp := channelFineCount_pos hm hB
    change 0 < m*channelBlockCount m B at hp
    exact Nat.pos_of_ne_zero (by intro he; simp [he] at hp)
  let : NeZero (channelBlockCount m B) := ⟨hk.ne'⟩
  intro g h hg hh K A hA hrow hcol
  have hδ := (channelMesh_pos (channelFineCount_pos hm hB)).le
  have hge := (he g).trans (mul_le_of_le_one_right hη.le (fullPrimeMass_unit_energy B g hg))
  have hhe := (he h).trans (mul_le_of_le_one_right hη.le (fullPrimeMass_unit_energy B h hh))
  have hgn := (hb g).trans (mul_le_of_le_one_right hC.le (fullPrimeMass_unit_energy B g hg))
  have hhn := (hb h).trans (mul_le_of_le_one_right hC.le (fullPrimeMass_unit_energy B h hh))
  have hgcn := (coarseGroupAverage_energy (groupedManuscriptChannel m B g) hδ).trans hgn
  have hs := finiteKernelBilinear_stability (fun _ => channelMesh (channelFineCount m B))
    K (fun _ => hδ) hA hrow hcol (groupedManuscriptChannel m B g)
    (groupedManuscriptChannel m B h) (coarseGroupAverage (groupedManuscriptChannel m B g))
    (coarseGroupAverage (groupedManuscriptChannel m B h)) hge hhe hgcn hhn
  have hηroot : Real.sqrt η = ε/(2*Real.sqrt C) :=
    Real.sqrt_sq (div_nonneg hε.le (by positivity))
  have hconst : Real.sqrt η*Real.sqrt C+Real.sqrt C*Real.sqrt η = ε := by
    rw [hηroot]
    field_simp
    ring
  exact hs.trans_eq (by rw [hconst])

end JointDickman

end OAI
