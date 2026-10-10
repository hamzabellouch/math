import OAI.Analysis.AncientFlat.Kernel.SchwartzIBP

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped BoundedContinuousFunction Topology
namespace FlatDuality

lemma hasDerivAt_integral_centerLip {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : ℝ → X → ℂ} {g : X → ℂ} {t : ℝ} {s : Set ℝ} {b : X → ℝ}
    (hs : s ∈ 𝓝 t) (hm : ∀ r ∈ s, AEStronglyMeasurable (f r) μ)
    (hi : Integrable (f t) μ) (hgm : AEStronglyMeasurable g μ)
    (hl : ∀ x, ∀ r ∈ s, ‖f r x-f t x‖≤b x*‖r-t‖) (hb : Integrable b μ)
    (hd : ∀ x, HasDerivAt (fun r => f r x) (g x) t) :
    HasDerivAt (fun r => ∫ x, f r x ∂μ) (∫ x, g x ∂μ) t := by
  let L : ℂ →L[ℝ] ℝ →L[ℝ] ℂ := ContinuousLinearMap.smulRightL ℝ ℝ ℂ 1
  have hgd : ∀ᵐ x ∂μ, HasFDerivAt (fun r => f r x) (L (g x)) t :=
    Eventually.of_forall (fun x => (hd x).hasFDerivAt)
  obtain ⟨hg,he⟩ := hasFDerivAt_integral_of_dominated_loc_of_lip' hs hm hi
    (L.continuous.comp_aestronglyMeasurable hgm) (Eventually.of_forall hl) hb hgd
  have hgi : Integrable g μ := by
    rw [←integrable_norm_iff (L.continuous.comp_aestronglyMeasurable hgm)] at hg
    simpa [L,Function.comp_def,integrable_norm_iff hgm] using hg
  rw [hasDerivAt_iff_hasFDerivAt]
  simpa only [Function.comp_def, ContinuousLinearMap.integral_comp_comm L hgi] using! he

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
lemma hasDerivAt_changing_pair {u : ℝ → V →ᵇ ℂ} {p : V →ᵇ ℂ} {t : ℝ}
    (hu : HasDerivAt u p t) (φ : ℝ → V → ℂ) (ψ : V → ℂ)
    (s : Set ℝ) (hs : s ∈ 𝓝 t)
    (hφ : ∀ r ∈ s, AEStronglyMeasurable (φ r)) (hψ : AEStronglyMeasurable ψ)
    (hd : ∀ x, HasDerivAt (fun r => φ r x) (ψ x) t)
    (A B : V → ℝ)
    (hA : Integrable A) (hB : Integrable B)
    (hAn : ∀ x, 0≤A x) (hBn : ∀ x, 0≤B x)
    (hbound : ∀ r ∈ s, ∀ x, ‖φ r x‖≤A x)
    (hlip : ∀ r ∈ s, ∀ x, ‖φ r x-φ t x‖≤B x*‖r-t‖) :
    HasDerivAt (fun r => ∫ x, φ r x*u r x)
      (∫ x, ψ x*u t x+φ t x*p x) t := by
  obtain ⟨C,hC,hbig⟩ := hu.isBigO_sub.exists_nonneg
  let q : Set ℝ := {r | ‖u r-u t‖≤C*‖r-t‖} ∩ s
  have hq : q ∈ 𝓝 t := inter_mem hbig.bound hs
  have ht : t ∈ s := mem_of_mem_nhds hs
  have hi : Integrable (φ t) := hA.mono' (hφ t ht) (Eventually.of_forall (hbound t ht))
  apply hasDerivAt_integral_centerLip hq
  · intro r hr
    exact (hφ r hr.2).mul (u r).continuous.aestronglyMeasurable
  · exact integrable_mul_bounded hi (u t).continuous ⟨‖u t‖,norm_nonneg _,(u t).norm_coe_le_norm⟩
  · exact (hψ.mul (u t).continuous.aestronglyMeasurable).add ((hφ t ht).mul p.continuous.aestronglyMeasurable)
  · intro x r hr
    have he : φ r x*u r x-φ t x*u t x=
        φ r x*(u r x-u t x)+(φ r x-φ t x)*u t x := by ring
    rw [he]
    calc
      _ ≤ ‖φ r x‖*‖u r x-u t x‖+‖φ r x-φ t x‖*‖u t x‖ := by
        simpa only [norm_mul] using norm_add_le (φ r x*(u r x-u t x)) ((φ r x-φ t x)*u t x)
      _ ≤ A x*(C*‖r-t‖)+(B x*‖r-t‖)*‖u t‖ := add_le_add
        (mul_le_mul (hbound r hr.2 x) (((u r-u t).norm_coe_le_norm x).trans hr.1)
          (norm_nonneg _) (hAn x))
        (mul_le_mul (hlip r hr.2 x) ((u t).norm_coe_le_norm x) (norm_nonneg _)
          (mul_nonneg (hBn x) (norm_nonneg _)))
      _ = (A x*C+B x*‖u t‖)*‖r-t‖ := by ring
  · exact (hA.mul_const C).add (hB.mul_const ‖u t‖)
  · intro x
    have he := (BoundedContinuousFunction.evalCLM ℝ x).hasFDerivAt.comp_hasDerivAt t hu
    exact (hd x).mul he
end FlatDuality

end

end OAI
