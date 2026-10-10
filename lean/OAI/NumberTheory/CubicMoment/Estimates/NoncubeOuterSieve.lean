import OAI.NumberTheory.CubicMoment.Estimates.OuterCoreBlock
import OAI.NumberTheory.CubicMoment.Estimates.CubicFrequencyMassSplit
import OAI.NumberTheory.CubicMoment.Estimates.PrimePowerSupport

namespace OAI

/-! The full outer cubic-sieve estimate for finite noncube frequencies,
derived by covering with the actual core dyads and summing their bounds. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma lowNoncubeSupport_zero (J : ℝ) : lowNoncubeSupport 0 J = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro h hh
  obtain ⟨_,v,j,hv,_,hNv,_,_⟩ := mem_lowNoncubeSupport hh
  have hv1 := one_le_norm hv
  linarith

theorem noncube_outer_sieve {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S H : Finset Eisenstein) (B N : ℝ),
      1 ≤ B → 1 ≤ N →
      (∀ n ∈ S, primary n ∧ Squarefree n ∧ norm n ≤ N) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B ∧ ¬∃ z : Eisenstein, z^3 = h) →
      ∀ β : Eisenstein → ℂ,
      (∑ h ∈ H, ‖∑ n ∈ S, β n*cubicSymbol n h‖^2) ≤
        C*(2*B*N)^ε*(B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N)*
          ∑ n ∈ S, ‖β n‖^2 := by
  have he : 0 < ε/2 := by linarith
  obtain ⟨C,hC,hblock⟩ := outer_core_block_sieve he
  obtain ⟨D,hD,hlog⟩ := natLog_power_bound 2 he
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro S H B N hB hN hS hH β
  have hB0 := zero_le_one.trans hB
  have hN0 := zero_le_one.trans hN
  have hcount : ((largeCoreDyadicIndices 0 B).card:ℝ) ≤ D*B^(ε/2) := by
    calc
      _ ≤ ((Nat.log 2 ⌊B⌋₊+1:ℕ):ℝ)^2 := by
        exact_mod_cast largeCoreDyadicIndices_card 0 B
      _ ≤ D*(⌊B⌋₊:ℝ)^(ε/2) := hlog _ ((Nat.one_le_floor_iff B).mpr hB)
      _ ≤ D*B^(ε/2) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le hB0) he.le) hD.le
  have hsplit := noncube_frequency_mass_split (V := 0) H hH
    (fun h => ‖∑ n ∈ S, β n*cubicSymbol n h‖^2) (fun _ => sq_nonneg _)
  simp only [lowNoncubeSupport_zero,Finset.notMem_empty,Finset.filter_false,
    Finset.sum_empty,zero_add] at hsplit
  have hrows (z : ℕ × ℕ) (hz : z ∈ largeCoreDyadicIndices 0 B) :=
    hblock S (coreDyadicBlock B z.1 z.2) B N z.1 z.2 hB0 hN
      (Finset.mem_filter.mp hz).2.2 hS (fun _ h => h) β
  have hE : 0 ≤ ∑ n ∈ S, ‖β n‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hp : B^(ε/2)*(2*B*N)^(ε/2) ≤ (2*B*N)^ε := by
    calc
      _ ≤ (2*B*N)^(ε/2)*(2*B*N)^(ε/2) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
        apply Real.rpow_le_rpow hB0 _ he.le
        nlinarith
      _ = _ := by rw [← Real.rpow_add (by positivity : 0 < 2*B*N)]; congr 1; ring
  calc
    _ ≤ ∑ z ∈ largeCoreDyadicIndices 0 B,
        C*(2*B*N)^(ε/2)*(B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N)*
          ∑ n ∈ S, ‖β n‖^2 :=
      hsplit.trans (Finset.sum_le_sum hrows)
    _ = ((largeCoreDyadicIndices 0 B).card:ℝ)*
        (C*(2*B*N)^(ε/2)*(B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N)*
          ∑ n ∈ S, ‖β n‖^2) := by simp
    _ ≤ (D*B^(ε/2))*
        (C*(2*B*N)^(ε/2)*(B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N)*
          ∑ n ∈ S, ‖β n‖^2) := mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = (C*D)*(B^(ε/2)*(2*B*N)^(ε/2))*
        (B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N)*∑ n ∈ S, ‖β n‖^2 := by ring
    _ ≤ _ := by gcongr

end CubicFirstMoment

end

end OAI
