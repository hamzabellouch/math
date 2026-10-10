import OAI.NumberTheory.DirichletL.Reflection.ExtractedKernel

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ : Type*} [Fintype φ]

lemma hybridInner_frozen_dual_reindex (F : PrimeFamily φ)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal)) (jF : φ → ℕ) (e : φ → Fin 3)
    (A : Ideal Eis → Ideal Eis → ℂ) (nset bset : Finset (Ideal Eis))
    (hn : ∀ n ∈ nset, primaryGenerator n ≠ 0) (hb : ∀ b ∈ bset, primaryGenerator b ≠ 0)
    (K P : Ideal Eis) :
    hybridInner nset bset (frozenBranchColumn F jF e A) K P =
      ∑ n ∈ quotientSupport (frozenExtracted F jF e 1) nset,
        ∑ b ∈ quotientSupport (frozenExtracted F jF e 2) bset,
          frozenBranchColumn F jF e A ((frozenExtracted F jF e 1)*n) ((frozenExtracted F jF e 2)*b)*
            quadraticRow K (primaryGenerator (((frozenExtracted F jF e 1)*n)*((frozenExtracted F jF e 2)*b)))*
            inverseCubicKernel P ((frozenExtracted F jF e 1)*n)*
            (if IsCoprime P ((frozenExtracted F jF e 2)*b) then 1 else 0) := by
  simpa only [hybridInner,mul_assoc] using frozenBranchColumn_dual_reindex F hF jF e A
    (fun n b => quadraticRow K (primaryGenerator (n*b))*inverseCubicKernel P n*(if IsCoprime P b then 1 else 0))
    nset bset hn hb

theorem hybridRow_frozen_extraction (F : PrimeFamily φ)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal)) (jF : φ → ℕ) (e : φ → Fin 3)
    (A : Ideal Eis → Ideal Eis → ℂ) (nset bset Pset : Finset (Ideal Eis))
    (hn : ∀ n ∈ nset, primaryGenerator n ≠ 0) (hb : ∀ b ∈ bset, primaryGenerator b ≠ 0)
    (aP : Ideal Eis → ℂ) (K : Ideal Eis) (hK : Admissible K)
    (hP : ∀ P ∈ Pset, primaryGenerator P ≠ 0) :
    hybridRow Pset nset bset aP (frozenBranchColumn F jF e A) K =
      ((frozenBranchScale F jF e:ℂ)*extractedRowFactor (frozenExtracted F jF e 1) (frozenExtracted F jF e 2) K)*
        hybridRow Pset (quotientSupport (frozenExtracted F jF e 1) nset)
          (quotientSupport (frozenExtracted F jF e 2) bset)
          (fun P => aP P*extractedSlotFactor (frozenExtracted F jF e 1) (frozenExtracted F jF e 2) P)
          (extractedFrozenColumn F jF e A) K := by
  unfold hybridRow
  simp_rw [hybridInner_frozen_dual_reindex F hF jF e A nset bset hn hb]
  simp only [hybridInner,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP'
  apply Finset.sum_congr rfl
  intro n hn'
  apply Finset.sum_congr rfl
  intro b hb'
  rw [frozenBranchColumn_eq_normalized]
  have hh := forced_dual_kernel_factor (frozenExtracted F jF e 1) (frozenExtracted F jF e 2)
    K P n b hK (hP P hP')
  have he := congrArg (fun z : ℂ => aP P/(Real.sqrt (Ideal.absNorm P:ℝ):ℂ)*
    (frozenBranchScale F jF e:ℂ)*extractedFrozenColumn F jF e A n b*z) hh
  convert he using 1 <;> simp only [extractedFrozenColumn,div_eq_mul_inv] <;> ring

lemma quotientSupport_norm_div (D : Ideal Eis) (hD : D ≠ 0) (S : Finset (Ideal Eis)) (Y : ℝ)
    (hS : ∀ I ∈ S, (Ideal.absNorm I:ℝ) ≤ Y) (J : Ideal Eis) (hJ : J ∈ quotientSupport D S) :
    (Ideal.absNorm J:ℝ) ≤ Y/(Ideal.absNorm D:ℝ) := by
  have hpos : (0:ℝ) < Ideal.absNorm D := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD)
  have hh := hS (D*J) ((mem_quotientSupport D J hD S).mp hJ)
  rw [map_mul,Nat.cast_mul] at hh
  exact (le_div_iff₀ hpos).mpr (by simpa only [mul_comm] using hh)

end
end SevenEighths.InverseReflectedPhase

end OAI
