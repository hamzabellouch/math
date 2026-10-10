import OAI.Analysis.AncientFlat.Evolution.ConstantEvolution
import OAI.Analysis.AncientFlat.Evolution.HeatDilation
import OAI.Analysis.AncientFlat.Evolution.CompactDifferenceCore
import OAI.Analysis.AncientFlat.Kernel.SymbolSemigroup
import OAI.Analysis.AncientFlat.Evolution.MovingNorm

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian
namespace BiharmonicKernel
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
lemma evolution_real_smul (t : ℝ) (ht : 0<t) (a : ℝ) (f : C₀(V,ℂ)) :
    evolution t (a • f)=a • evolution t f := by
  rw [evolution_eq_convolve t ht,evolution_eq_convolve t ht]
  exact ((C0Convolution.convolveCLM _ (heatKernel (V := V) t ht).integrable).restrictScalars ℝ).map_smul a f
end BiharmonicKernel
namespace FlatSimilarity
open BiharmonicKernel ParametrixDilation
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
def constantS (c t : ℝ) (d : C₀(V,ℂ)) : C₀(V,ℂ) :=
  Real.exp (-t/2) • dil t (evolution (constantTheta c t) d)
lemma constantTheta_add (c s t : ℝ) :
    constantTheta c (s+t)=Real.exp (-t)*constantTheta c s+constantTheta c t := by
  simp only [constantTheta,neg_add,Real.exp_add]
  ring
lemma constantS_zero (c : ℝ) (d : C₀(V,ℂ)) : constantS c 0 d=d := by
  simp [constantS,constantTheta_zero,evolution_zero]
lemma constantS_add (c : ℝ) (hc : 0<c) (s t : ℝ) (hs : 0<s) (ht : 0<t) (d : C₀(V,ℂ)) :
    constantS c (s+t) d=constantS c s (constantS c t d) := by
  have hθs := constantTheta_pos hc hs
  have hθt := constantTheta_pos hc ht
  have hθst : 0<Real.exp (-t)*constantTheta c s := mul_pos (Real.exp_pos _) hθs
  unfold constantS
  rw [evolution_real_smul _ hθs,ContinuousLinearMap.map_smul_of_tower,
    evolution_dil,←evolution_semigroup _ _ hθst hθt,constantTheta_add,
    smul_smul]
  rw [dil_add]
  congr 1
  rw [←Real.exp_add]
  congr 1
  ring
lemma TimeOneMap.constant_apply {c : ℝ} (hc : 0<c)
    {Pc : C₀(V,ℂ) →L[ℂ] C₀(V,ℂ)}
    (hPc : TimeOneMap (fun _ => c^2) (fun _ => 0) Pc) (d : C₀(V,ℂ)) :
    Pc d=constantS c 1 d := by
  obtain ⟨u,hu,hue⟩ := hPc d
  have hh := hu.unique (SymbolBounds.constant hc) (constantMoving_classical c hc d) 1
    ⟨zero_le_one,le_rfl⟩
  ext x
  rw [hue,hh]
  rfl
lemma TimeOneMap.constant_powers {c : ℝ} (hc : 0<c)
    {Pc : C₀(V,ℂ) →L[ℂ] C₀(V,ℂ)}
    (hPc : TimeOneMap (fun _ => c^2) (fun _ => 0) Pc) (n : ℕ) (d : C₀(V,ℂ)) :
    (Pc^n) d=constantS c n d := by
  induction n generalizing d with
  | zero => simp [constantS_zero]
  | succ n ih =>
    by_cases hn : n=0
    · subst n
      simpa using hPc.constant_apply hc d
    · rw [pow_succ,mul_apply_eq_comp,ih,hPc.constant_apply hc]
      symm
      exact_mod_cast constantS_add c hc (n:ℝ) 1 (by exact_mod_cast Nat.pos_of_ne_zero hn) zero_lt_one d
lemma TimeOneMap.constant_power_bound {c : ℝ} (hc : 0<c)
    {Pc : C₀(V,ℂ) →L[ℂ] C₀(V,ℂ)}
    (hPc : TimeOneMap (fun _ => c^2) (fun _ => 0) Pc) :
    ∃ C : ℝ, ∀ n : ℕ, ‖Pc^n‖≤C*(Real.exp (-(1:ℝ)/2))^n := by
  let C : ℝ := max 1 (∫ x : V, ‖heatKernel 1 zero_lt_one x‖)
  have hC : 0≤C := zero_le_one.trans (le_max_left _ _)
  refine ⟨C,fun n => ?_⟩
  by_cases hn : n=0
  · subst n
    simp only [pow_zero,mul_one]
    exact ContinuousLinearMap.norm_id_le.trans (le_max_left _ _)
  · have hnpos : 0<(n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hpow : (Real.exp (-(1:ℝ)/2))^n=Real.exp (-(n:ℝ)/2) := by
      rw [←Real.exp_nat_mul]
      congr 1
      ring
    rw [hpow]
    apply (Pc^n).opNorm_le_bound (mul_nonneg hC (Real.exp_pos _).le)
    intro d
    rw [hPc.constant_powers hc,constantS,norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le,norm_dil]
    calc
      _ ≤ Real.exp (-(n:ℝ)/2)*((∫ x : V, ‖heatKernel 1 zero_lt_one x‖)*‖d‖) :=
        mul_le_mul_of_nonneg_left (evolution_norm_le _ (constantTheta_pos hc hnpos) d) (Real.exp_pos _).le
      _ ≤ Real.exp (-(n:ℝ)/2)*(C*‖d‖) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg d)) (Real.exp_pos _).le
      _ = _ := by ring
lemma exists_constant_time_one (c : ℝ) (hc : 0<c) :
    ∃ Pc : C₀(V,ℂ) →L[ℂ] C₀(V,ℂ), TimeOneMap (fun _ => c^2) (fun _ => 0) Pc := by
  obtain ⟨K,hK,S,h0,hb,hcont,hadd,hm⟩ := exists_symbol_semigroup (V := V) c _ _ (SymbolBounds.constant hc)
  refine ⟨S 1,fun d => ?_⟩
  obtain ⟨u,hu,hue⟩ := hm d
  exact ⟨u,hu,hue 1 ⟨zero_le_one,le_rfl⟩⟩
end FlatSimilarity

end

end OAI
