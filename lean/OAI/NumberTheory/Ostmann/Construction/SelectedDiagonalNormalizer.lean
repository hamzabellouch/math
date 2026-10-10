import OAI.NumberTheory.Ostmann.Construction.CounterpartNormalizationBound
import OAI.NumberTheory.Ostmann.Construction.SelectedDiagonalEnvironment

namespace OAI

open Erdos970

noncomputable section
open Filter
namespace Ostmann.Construction
open Conclusion
namespace InitialSourceChoice
variable {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ} {E : Finset ℕ}

theorem remainingNormalization_nonneg (C : InitialSourceChoice d Bs BD Bz k L E)
    (T : List SourceSlot) : 0≤C.remainingNormalization T := by
  apply mul_nonneg (inv_pos.mpr C.giantPositive).le
  apply List.prod_nonneg
  intro z hz
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hz
  exact CounterpartNormalizationBound.sourceNormalization_nonneg C q.origin

theorem selectedDiagonalNormalizer_nonneg (C : InitialSourceChoice d Bs BD Bz k L E)
    (l : ℕ) : 0≤C.selectedDiagonalNormalizer l :=
  mul_nonneg (C.remainingNormalization_nonneg _) (Real.exp_pos _).le
end InitialSourceChoice

theorem selected_diagonal_normalizer_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase →
      C.blockBase+favorableBlockWidth L≤Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀l : ℕ,C.selectedDiagonalNormalizer l≤
        Real.exp (-stepGap BD Bz k L l+(34-Real.log L)*((2:ℝ)^l*(bulkSize k L:ℝ))) := by
  filter_upwards [remainingNormalization_exp_bound_eventually d Bs BD Bz hk] with L hN
  intro E C hG hGu hcl hcu hb hd l
  have h := hN E C hG hGu hcl hcu hb hd l
  have hm : 2*(bulkSize k L/2)=bulkSize k L := by
    obtain ⟨n,hn⟩ := bulkSize_even k L
    omega
  unfold InitialSourceChoice.selectedDiagonalNormalizer
  rw [hm]
  calc
    _ ≤ Real.exp ((counterpartNormalizationConstant-Real.log L)*((2:ℝ)^l*(bulkSize k L:ℝ)))*
        Real.exp (-stepGap BD Bz k L l) := mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ ≤ Real.exp ((34-Real.log L)*((2:ℝ)^l*(bulkSize k L:ℝ)))*
        Real.exp (-stepGap BD Bz k L l) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right (sub_le_sub_right counterpartNormalizationConstant_le _) (by positivity)
    _ = _ := by rw [←Real.exp_add]; congr 1; ring

end Ostmann.Construction

end

end OAI
