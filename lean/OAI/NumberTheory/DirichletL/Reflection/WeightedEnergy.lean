import OAI.NumberTheory.DirichletL.Reflection.ActualExtractedEnergy

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ ι : Type*} [Fintype φ] [Fintype ι] {N a c : Eis} {mode : Bool}

theorem bounded_column_hybrid_energy_extracted (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ X Y B L : ℝ, 1 ≤ X → 1 ≤ L →
    ∀ (F : PrimeFamily φ), Pairwise (Function.onFun IsCoprime F.ideal) →
    ∀ (jF : φ → ℕ) (e : φ → Fin 3) (A : Ideal Eis → Ideal Eis → ℂ),
      (∀ n b, ‖A n b‖ ≤ 1) →
    ∀ (rows nset bset Pset : Finset (Ideal Eis)) (aP : Ideal Eis → ℂ),
      (∀ K ∈ rows, Admissible K ∧ (Ideal.absNorm K:ℝ) ≤ X) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ) ≤ Y) →
      (∀ b ∈ bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b:ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ) ≤ 2*L) →
      (∀ P ∈ Pset, ‖aP P‖ ≤ 1) →
      let Yq := extractedDualScale (frozenExtracted F jF e 1) Y
      let Bq := extractedDualScale (frozenExtracted F jF e 2) B
      (∑ K ∈ rows, ‖hybridRow Pset nset bset aP
        (frozenBranchColumn F jF e A) K‖^2) ≤
      (frozenBranchScale F jF e)^2*
        (C*(X*Yq*Bq*L)^ε*(X+Yq*Bq)*Bq*(Yq+L+(Yq*L)^(2/3:ℝ))) := by
  obtain ⟨C,hC,he⟩ := hybridRow_energy ε hε
  refine ⟨C,hC,?_⟩
  intro X Y B L hX hL F hF jF e A hA rows nset bset Pset aP hrows hn hb hP ha
  let D1 := frozenExtracted F jF e 1
  let D2 := frozenExtracted F jF e 2
  let Yq := extractedDualScale D1 Y
  let Bq := extractedDualScale D2 B
  have hD1 : D1 ≠ 0 := frozenExtracted_ne_zero F jF e 1
  have hD2 : D2 ≠ 0 := frozenExtracted_ne_zero F jF e 2
  have hnq : ∀ n ∈ quotientSupport D1 nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ) ≤ Yq := by
    intro n hn'
    exact ⟨quotientSupport_cubic_admissible D1 hD1 nset (fun n h => (hn n h).1) n hn',
      (quotientSupport_norm_div D1 hD1 nset Y (fun n h => (hn n h).2) n hn').trans (le_max_right _ _)⟩
  have hbq : ∀ b ∈ quotientSupport D2 bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b:ℝ) ≤ Bq := by
    intro b hb'
    have hsource := hb (D2*b) ((mem_quotientSupport D2 b hD2 bset).mp hb')
    rw [primaryGenerator_mul] at hsource
    exact ⟨(mul_ne_zero_iff.mp hsource.1).2,
      (quotientSupport_norm_div D2 hD2 bset B (fun b h => (hb b h).2) b hb').trans (le_max_right _ _)⟩
  have hacoeff : ∀ P ∈ Pset, ‖aP P*extractedSlotFactor D1 D2 P‖ ≤ 1 := by
    intro P hP'
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (ha P hP')).trans (extractedSlotFactor_norm_le_one D1 D2 P)
  have hcolumn : ∀ n b, ‖extractedFrozenColumn F jF e A n b‖ ≤ 1 :=
    extractedFrozenColumn_norm_le_one F jF e A hA
  have hh := he X Yq Bq L hX (le_max_left _ _) (le_max_left _ _) hL rows
    (quotientSupport D1 nset) (quotientSupport D2 bset) Pset
    (fun P => aP P*extractedSlotFactor D1 D2 P)
    (extractedFrozenColumn F jF e A)
    hrows hnq hbq hP hacoeff (fun n _ b _ => hcolumn n b)
  apply le_trans (Finset.sum_le_sum (fun K hK => ?_))
    ((by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hh (sq_nonneg _)) :
      (∑ K ∈ rows, (frozenBranchScale F jF e)^2*
        ‖hybridRow Pset (quotientSupport D1 nset) (quotientSupport D2 bset)
          (fun P => aP P*extractedSlotFactor D1 D2 P)
          (extractedFrozenColumn F jF e A) K‖^2) ≤ _)
  rw [hybridRow_frozen_extraction F hF jF e _ nset bset Pset
    (fun n h => (hn n h).1.2) (fun b h => (hb b h).1) aP K (hrows K hK).1
    (fun P h => (hP P h).1.2)]
  have hp := frozenBranchScale_pos F jF e
  have hs := extractedRowFactor_norm_le_one D1 D2 K
  have hs2 : ‖extractedRowFactor D1 D2 K‖^2 ≤ 1 := by
    have h0 := norm_nonneg (extractedRowFactor D1 D2 K)
    nlinarith
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp,mul_pow]
  change (frozenBranchScale F jF e)^2*‖extractedRowFactor D1 D2 K‖^2* _ ≤ _
  calc
    _ ≤ ((frozenBranchScale F jF e)^2*1)*_ := by gcongr
    _ = _ := by rw [mul_one]

lemma actualCuspWeightedColumn_norm_le_one {ι : Type*} [Fintype ι]
    (G0 : PrimeFamily ι) (D0 : ControlledStratumArithmetic G0.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (u : Eisˣ) (m : ℕ) (w : Ideal Eis → Ideal Eis → ℂ)
    (hw : ∀ n b, ‖w n b‖ ≤ 1) (n b : Ideal Eis) :
    ‖actualCuspColumn D0 s hc u m n b*w n b‖ ≤ 1 := by
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (actualCuspColumn_norm_le_one D0 s hc u m n b)).trans (hw n b)

end
end SevenEighths.InverseReflectedPhase

end OAI
