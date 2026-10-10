import OAI.NumberTheory.Ostmann.Construction.SelectedDiagonalBadBudget
import OAI.NumberTheory.Ostmann.Construction.SelectedDiagonalBadOriginal
import OAI.NumberTheory.Ostmann.Construction.SelectedDiagonalBadSquare

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators Classical
open Filter
namespace Ostmann.Construction

theorem FinitePrior.mean_mono_support {α : Type*} [Fintype α] (μ : FinitePrior α)
    (f g : α→ℝ) (h : ∀x,μ.mass x≠0→f x≤g x) : μ.mean f≤μ.mean g := by
  apply Finset.sum_le_sum
  intro x hx
  by_cases hm : μ.mass x=0
  · simp only [hm,zero_mul,le_refl]
  · exact mul_le_mul_of_nonneg_left (h x hm) (μ.mass_nonneg x)

namespace InitialSourceChoice
open Conclusion Arithmetic.HistoryProductWindows
variable {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ} {E : Finset ℕ}

theorem selected_bad_covariance_le_single_energy (C : InitialSourceChoice d Bs BD Bz k L E)
    (spectator : PrimeSource) (s : ℕ) (X : ℝ) (l : ℕ) (hl : l<k)
    (hsep : C.CrossRoleSeparation spectator) :
    C.selectedDiagonalNormalizer l*(C.selectedBadCovarianceSum spectator s X l).re≤
      (C.selectedDiagonalNormalizer l*
        (Nat.card {e // diagonalBadPermutation (2*(bulkSize k L/2)) k l e}:ℝ)*
        Real.exp (nominalInheritedWidth k l+nominalRemovedWidth k l))*
        C.selectedDiagonalSingleEnergy spectator s X l := by
  rw [C.selectedBadCovarianceSum_original s l X spectator]
  let R : ℝ := C.selectedDiagonalNormalizer l*
    (Nat.card {e // diagonalBadPermutation (2*(bulkSize k L/2)) k l e}:ℝ)*
    Real.exp (nominalInheritedWidth k l+nominalRemovedWidth k l)
  calc
    _ ≤ (spectatorPrior spectator (2*s)).mean (fun ds =>
        (assignmentPrior C.sources (Template.extracted (l+1)
          (Template.current (Template.initial (2*(bulkSize k L/2)) k) l))).mean (fun u =>
          ∑p∈integerPivotCell C.giantCenter,R*(externalPivotWeight C.giantCenter p*
            C.selectedRemainingEnergy s l X (spectatorList spectator ds) p u))) := by
      apply FinitePrior.mean_mono
      intro ds
      apply FinitePrior.mean_mono_support
      intro u hu
      apply Finset.sum_le_sum
      intro p hp
      have h := C.fixed_bad_weighted_le_single_energy s l X (spectatorList spectator ds)
        hl p u hu (fun i => C.giant_sources_disjointMass spectator hsep _)
      simpa only [R,mul_assoc] using h
    _ = _ := by
      simp_rw [←Finset.mul_sum,FinitePrior.mean_mul_left]
      rfl

end InitialSourceChoice
open Conclusion Arithmetic.HistoryProductWindows

theorem selected_diagonal_bad_energy_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase →
      C.blockBase+favorableBlockWidth L≤Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀(spectator : PrimeSource),
      (∀p : spectator.Sample,Real.exp ((1/2000:ℝ)*L)≤Real.log (p:ℕ) ∧
        Real.log (p:ℕ)≤Real.exp ((1/1000:ℝ)*L)) →
      ∀(s : ℕ)(X : ℝ),∀l<k,
      C.selectedDiagonalNormalizer l*(C.selectedBadCovarianceSum spectator s X l).re≤
      Real.exp (-stepGap BD Bz k L l+
        (Real.log (bulkScale k)+(1/4:ℝ)*Real.log (((2^l:ℕ):ℝ))+37)*
          (((2^l:ℕ):ℝ)*(bulkSize k L:ℝ)))*C.selectedDiagonalSingleEnergy spectator s X l := by
  filter_upwards [selected_diagonal_bad_scalar_eventually d Bs BD Bz hk,
    initial_source_cross_role_separation_eventually d Bs BD Bz hk] with L hcost hsep
  intro E C hG hGu hcl hcu hb hd spectator hspec s X l hl
  refine (C.selected_bad_covariance_le_single_energy spectator s X l hl
    (hsep E C hG hcl hcu hb hd spectator hspec)).trans ?_
  exact mul_le_mul_of_nonneg_right (hcost E C hG hGu hcl hcu hb hd l hl.le)
    (C.selectedDiagonalSingleEnergy_nonneg spectator s X l)

end Ostmann.Construction

end

end OAI
