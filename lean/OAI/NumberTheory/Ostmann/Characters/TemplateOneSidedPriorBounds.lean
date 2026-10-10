import OAI.NumberTheory.Ostmann.Characters.OneSidedScaleGapAsymptotics
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPriorSource

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedPrior
open Construction Preliminaries PrimeDyadicCover Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem sourceRowMass_zero_of_empty {A : ℕ} (Q U : ℕ) (E : Finset (PrimeUpTo A))
    (i : Index U) (hi : block Q U (sourceNaturals E) i=∅)
    (x : Fin Q × Fin (2*lower Q U i+1)) : sourceRowMass Q U E i x=0 := by
  simp only [sourceRowMass,rowMass,hi,Finset.notMem_empty,ite_false]

theorem sourceRow_sum_zero_of_empty {A : ℕ} (Q U : ℕ) (E : Finset (PrimeUpTo A))
    (i : Index U) (hi : block Q U (sourceNaturals E) i=∅)
    (f : Fin Q × Fin (2*lower Q U i+1) → ℂ) :
    (∑x,(sourceRowMass Q U E i x:ℂ)*f x)=0 := by
  simp only [sourceRowMass_zero_of_empty Q U E i hi,Complex.ofReal_zero,zero_mul,Finset.sum_const_zero]

theorem occupied_lower_log {A : ℕ} (Q U : ℕ) (hQ : 0<Q)
    (E : Finset (PrimeUpTo A)) (hmin : ∀p∈E,Q≤p.val)
    {B : ℝ} (hlong : ∀p∈E,B≤Real.log p.val) (i : Index U)
    (hi : (block Q U (sourceNaturals E) i).Nonempty) :
    B-Real.log 2≤Real.log (lower Q U i) := by
  obtain ⟨p,hp⟩ := hi
  have hps := block_subset Q U (sourceNaturals E) i hp
  have hh := block_bounds hQ _ (sourceNaturals_property E _ hmin) i hp
  have hpos : (0:ℝ)<p := by exact_mod_cast (block_lower_pos hQ i).trans_le hh.1
  have hlog := Real.log_le_log hpos (by exact_mod_cast hh.2 : (p:ℝ)≤2*(lower Q U i:ℝ))
  have hl := sourceNaturals_property E (fun n=>B≤Real.log (n:ℝ)) hlong p hps
  have hb : (0:ℝ)<lower Q U i := by exact_mod_cast block_lower_pos hQ i
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hb.ne'] at hlog
  linarith

theorem eventually_occupied_lower_scale {γ γLong : ℝ} (hγ : 0≤γ) (hgap : γ<γLong) :
    ∀ᶠ L : ℝ in atTop,∀ {A : ℕ} (Q U : ℕ),0<Q →
      ∀ (E : Finset (PrimeUpTo A)),(∀p∈E,Q≤p.val) →
      (∀p∈E,Real.exp (γLong*L)≤Real.log p.val) →
      ∀ i : Index U,(block Q U (sourceNaturals E) i).Nonempty →
        Real.exp (γ*L)≤Real.log (lower Q U i) := by
  filter_upwards [eventually_exp_scale_gap hgap (1+Real.log 2),
    eventually_ge_atTop (0:ℝ)] with L hlarge hL
  intro A Q U hQ E hmin hlong i hi
  have hlo := occupied_lower_log Q U hQ E hmin hlong i hi
  have he : 1≤Real.exp (γ*L) := Real.one_le_exp (mul_nonneg hγ hL)
  have hl2 : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have hh := mul_nonneg hl2 (sub_nonneg.mpr he)
  nlinarith

theorem source_row_parameters {A : ℕ} (Q U : ℕ) (hQ : 0<Q)
    (E : Finset (PrimeUpTo A)) (hE : 0<primeShellMass E)
    (hmin : ∀p∈E,Q≤p.val) (i : Index U) :
    Fintype.card (Fin Q)≤Q ∧ 0<(lower Q U i:ℝ) ∧
    ((2*lower Q U i+1:ℕ):ℝ)≤3*(lower Q U i:ℝ) ∧
    (∀x,0 ≤ sourceRowMass Q U E i x) ∧ (∑x,sourceRowMass Q U E i x)≤1 ∧
    ∀x:Fin Q × Fin (2*lower Q U i+1),sourceRowMass Q U E i x≤
      longProgressionMajorant (1/primeShellMass E) (lower Q U i) Q x.1.val x.2.val := by
  refine ⟨by simp,by exact_mod_cast block_lower_pos hQ i,rowLength_le (block_lower_pos hQ i),
    sourceRowMass_nonneg Q U E hE i,sourceRowMass_total_le_one Q U hQ E hE hmin i,
    sourceRowMass_majorant Q U hQ E hE hmin i⟩

theorem source_cmean_norm_le_blocks {A : ℕ} (Q U : ℕ) (hQ : 0<Q)
    (E : Finset (PrimeUpTo A)) (hE : 0<primeShellMass E)
    (hmin : ∀p∈E,Q≤p.val) (hmax : ∀p∈E,p.val≤U)
    (f : PrimeUpTo A→ℂ) {B : ℝ} (hB : 0≤B)
    (hrows : ∀i:Index U,(block Q U (sourceNaturals E) i).Nonempty →
      ‖∑x:Fin Q × Fin (2*lower Q U i+1),(sourceRowMass Q U E i x:ℂ)*
        sourceTest f (rowValue Q (2*lower Q U i+1) x)‖≤B) :
    ‖(primeShellPrior E hE).cmean f‖≤(Fintype.card (Index U):ℝ)*B := by
  rw [source_cmean_eq_rows_actual Q U hQ E hE hmin hmax]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑_i:Index U,B := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases h : (block Q U (sourceNaturals E) i).Nonempty
      · exact hrows i h
      · rw [sourceRow_sum_zero_of_empty Q U E i (Finset.not_nonempty_iff_eq_empty.mp h),norm_zero]
        exact hB
    _ = _ := by simp

end Ostmann.Characters.TemplateOneSidedPrior

end

end OAI
