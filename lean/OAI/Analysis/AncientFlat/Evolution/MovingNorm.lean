import OAI.Analysis.AncientFlat.Evolution.TimeOneLipschitz

namespace OAI
noncomputable section
open Set Filter
open scoped Topology ContDiff ZeroAtInfty BoundedContinuousFunction
namespace FlatSimilarity
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma SymbolBounds.constant {c : ℝ} (hc : 0<c) :
    SymbolBounds c (fun _ : V => c^2) (fun _ : V => 0) := by
  refine ⟨hc,⟨c^2,by positivity,fun _ => le_rfl⟩,contDiff_const,contDiff_const,fun n => ⟨0,le_rfl,?_⟩⟩
  intro x
  simp
lemma SymbolBounds.uniform_moving_bound {c : ℝ} {Af Bf : V → ℝ} (h : SymbolBounds c Af Bf) :
    ∃ K : ℝ, 0≤K ∧ ∀ (d : C₀(V,ℂ)) (u : ℝ → C₀(V,ℂ)), MovesClassically Af Bf d u →
      ∀ t ∈ Icc (0:ℝ) 1, ∀ x, ‖u t x‖≤K*‖d‖ := by
  obtain ⟨K,hK,S,_,hSb,_,_,hSm⟩ := exists_symbol_semigroup c Af Bf h
  refine ⟨K,hK,fun d u hu t ht x => ?_⟩
  obtain ⟨w,hw,hwS⟩ := hSm d
  have he : u t x=S t d (Real.exp (t/4) • x) := by
    rw [hwS t ht,smul_smul,←Real.exp_add]
    have hx : -t/4+t/4=0 := by ring
    simp only [hx,Real.exp_zero,one_smul]
    exact congrArg (fun f : C₀(V,ℂ) => f x) (hu.unique h hw t ht)
  rw [he]
  exact ((S t d).toBCF.norm_coe_le_norm _).trans (by
    rw [ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    exact ((S t).le_opNorm d).trans (mul_le_mul_of_nonneg_right (hSb t ht) (norm_nonneg _)))
end FlatSimilarity

end

end OAI
