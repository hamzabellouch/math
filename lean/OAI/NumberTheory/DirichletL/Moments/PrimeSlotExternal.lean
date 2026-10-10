import OAI.NumberTheory.DirichletL.Moments.PrimeSlotShift
import OAI.NumberTheory.DirichletL.Moments.PrimeSlotUniform

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff

namespace SevenEighths.CenteredMomentPrimeSlotExternal
open HeckeFamily HeckeRowClosure HeckeZeroSupremum CenteredExceptionalProfile HeckePrimeAnnular
open CenteredMomentPrimeSlot CenteredMomentPrimeSlotUniform CenteredMomentWholeSlotDeletion
open ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
variable (M:Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ) (hH:RayOrthogonality.globalUnits M≤H)
include hH

theorem actual_slots_external_uniform {ι:Type*} [Fintype ι]
    (W:ι→ℝ→ℂ) (a b:ι→ℝ) (ha:∀i,0<a i)
    (hWs:∀i,Function.support (W i)⊆Set.Icc (a i) (b i)) (hW:∀i,ContDiff ℝ ∞ (W i))
    (Lmod Lslot loss lo hi κ:ℝ) (hLm:0≤Lmod) (hLs:0≤Lslot) (hloss:0<loss)
    (hbeta:(51/100:ℝ)≤beta) (hκ:2*beta-1≤κ) :
    ∃degree:ℕ,∃C Z₀:ℝ,1≤C ∧ 1<Z₀ ∧ ∀i:ι,∀Z P:ℝ,Z₀≤Z → 1≤P → P≤Z^Lslot →
    ∀(η:Character) (Q:Ideal O) (m A z:O),Q≤M → m≠0 → A≠0 → z≠0 →
      goodLambda∣m → (2:O)∣m →
      (rowConductorBound η m 1 (A*z):ℝ)≤Z^Lmod →
      ¬FixedInducingRow η Q m A z →
      ∀σ t v V:ℝ,lo≤σ → σ≤hi → |v|≤V →
      ‖normalizedSlot η m A z (primePool M H (b i) P) (annularWeight (W i) P σ v) t P‖^2≤
        C*(1+|t|+V)^degree*Z^loss*P^κ := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,hbound⟩:=actual_slots_uniform M H hH W a b ha hWs hW
    Lmod Lslot loss lo hi κ hLm hLs hloss hbeta hκ
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro i Z P hZ hP hPcap η Q m A z hQ hm hA hz hmLam hm2 hcond hex σ t v V hσ hσhi hv
  obtain ⟨χ,hχ,hrow⟩:=exists_row_character_with_conductor η m 1 (A*z) hm one_ne_zero
    (mul_ne_zero hA hz) hmLam hm2
  rw [CenteredMomentPrimeSlotShift.normalizedSlot_norm_sq M H η χ m A z hrow (W i) (b i) P σ t v
    (zero_lt_one.trans_le hP),←CenteredMomentPrimeSlot.normalizedSlot_norm_sq M H η χ m A z hrow
      (W i) (b i) P σ (t+v) (zero_lt_one.trans_le hP)]
  apply (hbound i Z P hZ hP hPcap η Q m A z hQ hm hA hz hmLam hm2 hcond hex σ (t+v) hσ hσhi).trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans hP) _)
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans (hZ₀.le.trans hZ)) _)
  apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hC)
  exact pow_le_pow_left₀ (by positivity) (by linarith [abs_add_le t v]) _

end SevenEighths.CenteredMomentPrimeSlotExternal

end

end OAI
