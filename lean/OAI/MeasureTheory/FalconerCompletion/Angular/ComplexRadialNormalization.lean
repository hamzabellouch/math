import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Estimates.FarRetainedEqOriginalLabels

namespace OAI

/-! Angular cutoffs and derivative estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer
open Set MeasureTheory _root_.OAI.GraphLiteralSupport.Attempt4FullFar
open scoped ComplexConjugate

lemma complex_radial_normalizationND {Ω : ℝ} (hΩ : 0<Ω) (Ψ : ℝ → ℝ) (f : ℝ → ℂ) :
    Ω⁻¹ • (∫ r, (Ψ (r/Ω):ℂ)*f r) = ∫ u, (Ψ u:ℂ)*f (Ω*u) := by
  have hh := Measure.integral_comp_mul_left (fun r => (Ψ (r/Ω):ℂ)*f r) Ω
  simp only [abs_of_pos (inv_pos.mpr hΩ)] at hh
  rw [← hh]
  apply integral_congr_ae
  filter_upwards with u
  rw [mul_div_cancel_left₀ u hΩ.ne']

lemma farAngularEnergyND_normalized {V : Type*} [MeasurableSpace V] (d : ℕ)
    (μ : Measure V) [IsFiniteMeasure μ] (a : ℝ) (h : ℕ) (v lam₁ lam₂ : ℝ)
    (A D : Finset (Fin d → ℤ)) (U W : (Fin d → ℤ) → ℝ×V → ℂ)
    (hU : ∀ i∈A, Measurable (U i)) (hW : ∀ j∈D, Measurable (W j))
    (C E : (Fin d → ℤ) → ℝ)
    (hbU : ∀ i∈A, ∀ r, ∀ᵐ w ∂μ, ‖U i (r,w)‖≤C i)
    (hbW : ∀ j∈D, ∀ r, ∀ᵐ w ∂μ, ‖W j (r,w)‖≤E j)
    {Ψ : ℝ → ℝ} (hmΨ : Measurable Ψ) (hΨ : Integrable Ψ) :
    Attempt4Near.farAngularEnergyND d μ a h v lam₁ lam₂ Ψ A D U W =
    (lam₁^2*lam₂^2*(2:ℝ)^((d:ℝ)*(v-a)))*
      ‖∫ p : ℝ×(V×V), (Ψ p.1:ℂ)*Attempt4Near.farRetainedND h A D
        (fun i q => U i ((2:ℝ)^v*q.1,q.2)) (fun j q => W j ((2:ℝ)^v*q.1,q.2)) p.1 p.2
        ∂volume.prod (μ.prod μ)‖ := by
  let Us := fun i (q : ℝ×V) => U i ((2:ℝ)^v*q.1,q.2)
  let Ws := fun j (q : ℝ×V) => W j ((2:ℝ)^v*q.1,q.2)
  have hUs : ∀ i∈A, Measurable (Us i) := fun i hi =>
    (hU i hi).comp ((measurable_const.mul measurable_fst).prodMk measurable_snd)
  have hWs : ∀ j∈D, Measurable (Ws j) := fun j hj =>
    (hW j hj).comp ((measurable_const.mul measurable_fst).prodMk measurable_snd)
  have hUb : ∀ i∈A, ∀ r, ∀ᵐ w ∂μ, ‖Us i (r,w)‖≤C i := fun i hi r => hbU i hi ((2:ℝ)^v*r)
  have hWb : ∀ j∈D, ∀ r, ∀ᵐ w ∂μ, ‖Ws j (r,w)‖≤E j := fun j hj r => hbW j hj ((2:ℝ)^v*r)
  have hi := Attempt4Near.farRetainedND_joint_integrable h μ A D U W hU hW C E hbU hbW
    (hmΨ.comp (measurable_id.div_const _)) (hΨ.comp_div (by positivity : (2:ℝ)^v≠0))
  have hj := Attempt4Near.farRetainedND_joint_integrable h μ A D Us Ws hUs hWs C E hUb hWb hmΨ hΨ
  rw [Attempt4Near.farAngularEnergyND,
    integral_prod (fun p : ℝ×(V×V) => (Ψ (p.1/(2:ℝ)^v):ℂ)*Attempt4Near.farRetainedND h A D U W p.1 p.2) hi,
    integral_prod (fun p : ℝ×(V×V) => (Ψ p.1:ℂ)*Attempt4Near.farRetainedND h A D Us Ws p.1 p.2) hj]
  simp only [integral_const_mul]
  have hn := congrArg norm (complex_radial_normalizationND (by positivity : (0:ℝ)<(2:ℝ)^v) Ψ
    (fun r => ∫ z, Attempt4Near.farRetainedND h A D U W r z ∂μ.prod μ))
  simp only [norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : (0:ℝ)<((2:ℝ)^v)⁻¹)] at hn
  calc
    _ = (lam₁^2*lam₂^2*(2:ℝ)^((d:ℝ)*(v-a)))*
      (((2:ℝ)^v)⁻¹ * ‖∫ r, (Ψ (r/(2:ℝ)^v):ℂ)*(∫ z, Attempt4Near.farRetainedND h A D U W r z ∂μ.prod μ)‖) := by ring
    _ = _ := by rw [hn]; rfl

variable {n : ℕ}

theorem physical_farAngularEnergyND_original {Ψ : ℝ → ℝ} (hmΨ : Measurable Ψ) (hΨ : Integrable Ψ)
    (a v lam₁ lam₂ : ℝ)
    (ρ κ : Measure (EuclideanSpace ℝ (Fin (n+1)))) [IsFiniteMeasure ρ] [IsFiniteMeasure κ]
    (h : ℕ) (A D : Finset (Fin (n+1) → ℤ)) (M N : ℝ)
    (b c : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    {B C : ℝ} (hB : 0≤B) (hC : 0≤C)
    (hbd : ∀ x w, ‖w‖=1 → ‖b x w‖≤B) (hcd : ∀ x w, ‖w‖=1 → ‖c x w‖≤C) :
    Attempt4Near.farAngularEnergyND (n+1) (canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1))))
      a h v lam₁ lam₂ Ψ A D (originalCellTransformND ρ h M b) (originalCellTransformND κ h N c) =
    (lam₁^2*lam₂^2*(2:ℝ)^((n+1:ℕ)*(v-a))/((M*M)*(N*N)))*
      ‖∫ z in originalFarRegionND h A D, euclideanFarKernelND Ψ v (scalarPairSymbolND b) (scalarPairSymbolND c) z
        ∂(ρ.prod ρ).prod (κ.prod κ)‖ := by
  let Bs := fun i => |M⁻¹| *(ρ (ambientGridCell h i)).toReal*B
  let Cs := fun j => |N⁻¹| *(κ (ambientGridCell h j)).toReal*C
  have hUb : ∀ i∈A, ∀ r, ∀ᵐ w ∂canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1))),
      ‖originalCellTransformND ρ h M b i (r,w)‖≤Bs i := by
    intro i _ r
    filter_upwards [canonicalSphereMeasureND_ae_norm] with w hw
    exact sourceAngularTransformND_norm_le ρ _ _ b _ w (fun x => hbd x w hw)
  have hWb : ∀ j∈D, ∀ r, ∀ᵐ w ∂canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1))),
      ‖originalCellTransformND κ h N c j (r,w)‖≤Cs j := by
    intro j _ r
    filter_upwards [canonicalSphereMeasureND_ae_norm] with w hw
    exact sourceAngularTransformND_norm_le κ _ _ c _ w (fun x => hcd x w hw)
  rw [farAngularEnergyND_normalized (n+1) _ a h v lam₁ lam₂ A D (originalCellTransformND ρ h M b) (originalCellTransformND κ h N c)
    (fun i _ => sourceAngularTransformND_measurable ρ _ _ hb)
    (fun j _ => sourceAngularTransformND_measurable κ _ _ hc) Bs Cs hUb hWb hmΨ hΨ]
  rw [← original_far_energy_identityND hmΨ hΨ v ρ κ h A D M N b c hb hc hB hC hbd hcd]
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr
    (mul_nonneg (mul_self_nonneg M) (mul_self_nonneg N)))]
  ring

lemma physical_far_profile_coefficientND (R : ℝ) (hR : 0<R) (ma mb K : ℝ) :
    (R^(-(mb-ma)))^2*(R^(-(mb-ma)))^2*K/((R^(-mb)*R^(-mb))*(R^(-mb)*R^(-mb))) =
      K/(R^(-ma))^4 := by
  have hm : R^(-ma)≠0 := ne_of_gt (Real.rpow_pos_of_pos hR _)
  have hn : R^(-mb)≠0 := ne_of_gt (Real.rpow_pos_of_pos hR _)
  have he : R^(-(mb-ma))=(R^(-ma))⁻¹*R^(-mb) := by
    rw [← Real.rpow_neg hR.le,← Real.rpow_add hR]
    congr 1
    ring
  rw [he]
  field_simp

end CurrentFalconer
end GraphLiteralSupport
end
end

end OAI
