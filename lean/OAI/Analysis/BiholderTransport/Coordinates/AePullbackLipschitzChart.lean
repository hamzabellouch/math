import Mathlib
import OAI.Analysis.BiholderTransport.Volume.LocalCharts

namespace OAI

section
section
noncomputable section
open Set Filter MeasureTheory Manifold Metric
open scoped ENNReal NNReal Topology

namespace WeakMTWTransport

lemma ae_pullback_of_lipschitz_chart_inverse {n : ℕ} {M : Type*}
    [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
    (d : PartialEquiv M (Model n)) {G : Set M} (hGm : MeasurableSet G)
    (hGs : G⊆d.source) (hIm : MeasurableSet (d '' G))
    {D : ℝ≥0} (hdi : LipschitzOnWith D d.symm (d '' G))
    {P : Model n → Prop} (hP : ∀ᵐ z ∂volume.restrict (d '' G), P z) :
    ∀ᵐ x ∂(metricVolume n).restrict G, P (d x) := by
  let N := {z | z∈d '' G ∧ ¬P z}
  have hN : volume N=0 := by
    have H := ae_iff.mp ((ae_restrict_iff' hIm).mp hP)
    apply measure_mono_null _ H
    exact fun z hz h => hz.2 (h hz.1)
  have hNsub : N⊆d '' G := fun z hz => hz.1
  have hNi : metricVolume n (d.symm '' N)=0 := by
    apply le_antisymm _ (show (0:ℝ≥0∞)≤_ from zero_le)
    have H := metricVolume_lipschitz_image_le_nat (n := n) (hdi.mono hNsub)
    rw [metricVolume_model,hN,mul_zero] at H
    exact H
  rw [ae_restrict_iff' hGm]
  apply ae_iff.mpr
  apply measure_mono_null _ hNi
  intro x hx
  have hxG : x∈G := by by_contra h; exact hx (fun hh => False.elim (h hh))
  have hn : ¬P (d x) := fun h => hx (fun _ => h)
  exact ⟨d x,⟨⟨x,hxG,rfl⟩,hn⟩,d.left_inv (hGs hxG)⟩

lemma ae_chart_jacobian_bounds {n : ℕ} {M : Type*}
    [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
    (d e : PartialEquiv M (Model n)) {G : Set M} {T : M → M}
    (hGm : MeasurableSet G) (hIm : MeasurableSet (d '' G))
    (hGs : G⊆d.source) (hTs : T '' G⊆e.source) (hTi : InjOn T G)
    {C D H K : ℝ≥0} (hC : 0<C) (hK : 0<K)
    (hd : LipschitzOnWith C d G) (hdi : LipschitzOnWith D d.symm (d '' G))
    (he : LipschitzOnWith H e (T '' G)) (hei : LipschitzOnWith K e.symm (e '' (T '' G)))
    {a b : ℝ≥0∞}
    (hmass : ∀ B : Set M, MeasurableSet B → B⊆G →
      a*metricVolume n B≤ metricVolume n (T '' B) ∧
      metricVolume n (T '' B)≤b*metricVolume n B)
    {f' : Model n → Model n →L[ℝ] Model n}
    (hf' : ∀ z∈d '' G, HasFDerivWithinAt (e ∘ T ∘ d.symm) (f' z) (d '' G) z) :
    ∀ᵐ x ∂(metricVolume n).restrict G,
      a/((C:ℝ≥0∞)^n*(K:ℝ≥0∞)^n)≤ENNReal.ofReal |(f' (d x)).det| ∧
      ENNReal.ofReal |(f' (d x)).det|≤(H:ℝ≥0∞)^n*b*(D:ℝ≥0∞)^n := by
  apply ae_pullback_of_lipschitz_chart_inverse d hGm hGs hIm hdi
    (P := fun z => a/((C:ℝ≥0∞)^n*(K:ℝ≥0∞)^n)≤ENNReal.ofReal |(f' z).det| ∧
      ENNReal.ofReal |(f' z).det|≤(H:ℝ≥0∞)^n*b*(D:ℝ≥0∞)^n)
  apply ae_jacobian_bounds_of_image_mass volume hIm hf'
  · rintro z ⟨x,hx,rfl⟩ w ⟨y,hy,rfl⟩ heq
    simp only [Function.comp_apply,d.left_inv (hGs hx),d.left_inv (hGs hy)] at heq
    have hTxs : T x∈e.source := hTs ⟨x,hx,rfl⟩
    have hTys : T y∈e.source := hTs ⟨y,hy,rfl⟩
    exact congrArg d (hTi hx hy (e.injOn hTxs hTys heq))
  · exact fun A hA hAs => image_mass_in_bilipschitz_coordinates d e hGs hTs
      hC hK hd hdi he hei hmass hA hAs

end WeakMTWTransport

end

end

end

end OAI
