import OAI.Analysis.AncientFlat.Evolution.Commutator

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ZeroAtInfty BoundedContinuousFunction SchwartzMap
namespace FrozenParametrix
open BiharmonicKernel
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
lemma exists_frozen_lipschitz_bound_sharp (α β : ℝ) (hα : 0 < α) (B L : ℝ)
    (hB : 0 ≤ B) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : C(V,Icc α β)) (b : V →ᵇ ℂ)
      (_hb : ‖b‖ ≤ B) (_hLip : ∀ x y, ‖b x-b y‖ ≤ L*‖x-y‖)
      (r : ℝ) (_hr : 0 < r) (_hr1 : r ≤ 1) (f : C₀(V,ℂ)) (x y : V),
      ‖b x*frozenOp hα a r f x-b y*frozenOp hα a r f y‖ ≤
        ((r⁻¹)^4*‖f‖*C)*‖x-y‖ := by
  obtain ⟨C,D,hC,hD,hbound⟩ := SourceFrozenOrder.exists_bounds (heatOne : SchwartzMap V ℂ) 0 α β hα
  refine ⟨B*D+L*C,by positivity,?_⟩
  intro a b hb hLip r hr hr1 f x y
  obtain ⟨hu,hul⟩ := hbound (fun z => (a z).val) (continuous_subtype_val.comp a.continuous)
    (fun z => (a z).property) r hr f.toBCF
  have hh := ProductLipschitz.bound b
    (SourceFrozenOrder.value heatOne (fun z => (a z).val) r f.toBCF 0)
    B L ((r⁻¹)^0*(‖f.toBCF‖*C)) ((r⁻¹)^1*(‖f.toBCF‖*D)) hB hL
    (fun z => (b.norm_coe_le_norm z).trans hb) hu hLip hul x y
  simp_rw [frozen_eq_ordered hα a r hr]
  apply hh.trans
  calc
    _ ≤ (B*((r⁻¹)^4*(‖f‖*D))+L*((r⁻¹)^4*(‖f‖*C)))*‖x-y‖ := by
      simp only [ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
      gcongr <;> first | exact (one_le_inv₀ hr).mpr hr1 | norm_num
    _ = _ := by ring

lemma exists_principal_lipschitz_bound_sharp (α β : ℝ) (hα : 0<α) (L : ℝ) (hL : 0≤L) :
    ∃ C : ℝ, 0≤C ∧ ∀ (a₀ a₁ : C(V,Icc α β)) (r q : ℝ), 0<r → 0≤q → q≤r →
      (∀ x y, |(a₁ x).val-(a₀ y).val|≤L*(‖x-y‖+q)) →
      (∀ x y, |(a₁ x).val-(a₁ y).val|≤L*‖x-y‖) → ∀ (f : C₀(V,ℂ)) (x y : V),
      ‖principalResidual hα a₀ a₁ r f x-principalResidual hα a₀ a₁ r f y‖≤
        (r⁻¹)^4*‖f‖*C*‖x-y‖ := by
  obtain ⟨C,hC,hb⟩ := SourceFrozenOrder.exists_commutator_lipschitz (bilapOne : SchwartzMap V ℂ) 4 α β hα
  refine ⟨L*C,by positivity,fun a₀ a₁ r q hr hq hqr hc hl f x y => ?_⟩
  have hh := hb (fun z => (a₀ z).val) (continuous_subtype_val.comp a₀.continuous)
    (fun z => (a₀ z).property) r q L hr hq hqr hL (coefficient a₀) (coefficient a₁) f.toBCF
    (fun z w => by simpa only [coefficient_apply,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hc z w)
    (fun z w => by simpa only [coefficient_apply,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hl z w) x y
  simp_rw [principal_eq_ordered hα a₀ a₁ r hr]
  simpa only [ZeroAtInftyContinuousMap.norm_toBCF_eq_norm,mul_assoc] using hh
end FrozenParametrix

end

end OAI
