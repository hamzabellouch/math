import OAI.Analysis.AncientFlat.Evolution.ConstantRepresentation
import OAI.Analysis.AncientFlat.Regularity.HolderAlgebra

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian
namespace ParabolicSchauder
open ParametrixEvolution ParabolicInterior
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem constant_fourth_estimate (α : ℝ) (hα : 0<α) (hα1 : α<1) :
    ∃ C : ℝ, 0<C ∧ ∀ (T : ℝ), 0<T → T≤1 →
      ∀ (f : ℝ →ᵇ C₀(V,ℂ)) (F : ℝ), 0≤F →
      (∀ t∈Icc 0 T, ∀ x y, ‖f t x-f t y‖≤F*‖x-y‖^α) →
      ∀ (u : ℝ → C₀(V,ℂ)), SourceEvolves unitLine 0 f 0 T 0 u →
      HolderBound α {p : V × ℝ | p.2∈Icc 0 T}
        (fun p => iteratedFDeriv ℝ 4 (fun x => u p.2 x) p.1) (C*F) := by
  obtain ⟨C,hC,hest⟩ := fourth_derivative_holder (V := V) α hα hα1
  refine ⟨2*C+1,by linarith,?_⟩
  intro T hT hT1 f F hF hf u hu
  have hfc : Continuous (fun t => (f t).toBCF) :=
    ZeroAtInftyContinuousMap.isometry_toBCF.continuous.comp f.continuous
  obtain ⟨_,hbound,hspace,htime⟩ := hest T hT hT1 (fun t => (f t).toBCF) F hF hfc hf
  have he (t : ℝ) (ht : t∈Icc 0 T) :
      (fun x => u t x)=potential (fun r => (f r).toBCF) t :=
    funext (constant_representation hT.le hT1 hα hα1.le f ⟨F,hF,hf⟩ u hu t ht)
  refine ⟨?_,?_⟩
  · intro p hp
    change ‖iteratedFDeriv ℝ 4 (fun x => u p.2 x) p.1‖≤_
    rw [he p.2 hp]
    have ht1 : p.2^(α/4)≤1 := Real.rpow_le_one hp.1 (hp.2.trans hT1) (by positivity)
    exact (hbound p.2 hp p.1).trans ((mul_le_mul_of_nonneg_left ht1 (mul_nonneg hC hF)).trans (by nlinarith))
  · intro p hp q hq
    change ‖iteratedFDeriv ℝ 4 (fun x => u p.2 x) p.1-iteratedFDeriv ℝ 4 (fun x => u q.2 x) q.1‖≤_
    rw [he p.2 hp,he q.2 hq]
    apply (norm_sub_le_norm_sub_add_norm_sub _
      (iteratedFDeriv ℝ 4 (potential (fun r => (f r).toBCF) p.2) q.1) _).trans
    have hs := hspace p.2 hp p.1 q.1
    have ht := htime q.2 hq p.2 hp q.1
    have hd : 0≤pdist p q := pdist_nonneg p q
    have hs' : ‖p.1-q.1‖^α≤pdist p q^α :=
      Real.rpow_le_rpow (norm_nonneg _) (le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg _) _)) hα.le
    have ht' : |p.2-q.2|^(α/4)≤pdist p q^α := by
      rw [show α/4=(1/4:ℝ)*α by ring,Real.rpow_mul (abs_nonneg _)]
      apply Real.rpow_le_rpow (Real.rpow_nonneg (abs_nonneg _) _) _ hα.le
      exact le_add_of_nonneg_left (norm_nonneg _)
    have ihs := mul_le_mul_of_nonneg_left hs' (mul_nonneg hC hF)
    have iht := mul_le_mul_of_nonneg_left ht' (mul_nonneg hC hF)
    nlinarith [mul_nonneg hF (Real.rpow_nonneg hd α)]
end ParabolicSchauder

end

end OAI
