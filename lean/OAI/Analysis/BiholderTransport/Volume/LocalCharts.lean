import Mathlib
import OAI.Analysis.BiholderTransport.LocalFlow.ForwardChart

namespace OAI

section

section

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakMTWTransport
section Area
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

lemma ae_jacobian_bounds_of_image_mass {s : Set E} (hs : MeasurableSet s)
    {f : E → E} {f' : E → E →L[ℝ] E}
    (hf' : ∀ x∈s, HasFDerivWithinAt f (f' x) s x) (hi : InjOn f s)
    {a b : ℝ≥0∞}
    (hmass : ∀ A : Set E, MeasurableSet A → A⊆s →
      a*μ A≤μ (f '' A) ∧ μ (f '' A)≤b*μ A) :
    ∀ᵐ x ∂μ.restrict s, a≤ENNReal.ofReal |(f' x).det| ∧
      ENNReal.ofReal |(f' x).det|≤b := by
  have hJ := aemeasurable_ofReal_abs_det_fderivWithin μ hs hf'
  have harea (A : Set E) (hA : MeasurableSet A) :
      (∫⁻ x in A, ENNReal.ofReal |(f' x).det| ∂μ.restrict s)=μ (f '' (A∩s)) := by
    rw [Measure.restrict_restrict hA]
    exact lintegral_abs_det_fderiv_eq_addHaar_image μ (hA.inter hs)
      (fun x hx => (hf' x hx.2).mono inter_subset_right) (hi.mono inter_subset_right)
  have hlo : ∀ᵐ x ∂μ.restrict s, a≤ENNReal.ofReal |(f' x).det| := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀ aemeasurable_const
    intro A hA _
    rw [harea A hA,lintegral_const,Measure.restrict_apply MeasurableSet.univ,
      univ_inter,Measure.restrict_apply hA]
    exact (hmass (A∩s) (hA.inter hs) inter_subset_right).1
  have hup : ∀ᵐ x ∂μ.restrict s, ENNReal.ofReal |(f' x).det|≤b := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀ hJ
    intro A hA _
    rw [harea A hA,lintegral_const,Measure.restrict_apply MeasurableSet.univ,
      univ_inter,Measure.restrict_apply hA]
    exact (hmass (A∩s) (hA.inter hs) inter_subset_right).2
  exact hlo.and hup

end Area
end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter MeasureTheory Manifold Metric
open scoped ENNReal NNReal Topology

namespace WeakMTWTransport

lemma metricVolume_lipschitz_image_le_nat {n : ℕ} {X Y : Type*}
    [MetricSpace X] [MetricSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
    [BorelSpace X] [BorelSpace Y] {f : X → Y} {s : Set X} {C : ℝ≥0}
    (hf : LipschitzOnWith C f s) :
    metricVolume n (f '' s)≤(C:ℝ≥0∞)^n*metricVolume n s := by
  simpa only [ENNReal.rpow_natCast] using metricVolume_lipschitz_image_le (n := n) hf

lemma image_mass_in_bilipschitz_coordinates {n : ℕ} {M : Type*}
    [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
    (d e : PartialEquiv M (Model n)) {G : Set M} {T : M → M}
    (hGs : G⊆d.source) (hTs : T '' G⊆e.source)
    {C D H K : ℝ≥0} (hC : 0<C) (hK : 0<K)
    (hd : LipschitzOnWith C d G) (hdi : LipschitzOnWith D d.symm (d '' G))
    (he : LipschitzOnWith H e (T '' G)) (hei : LipschitzOnWith K e.symm (e '' (T '' G)))
    {a b : ℝ≥0∞}
    (hmass : ∀ B : Set M, MeasurableSet B → B⊆G →
      a*metricVolume n B≤ metricVolume n (T '' B) ∧
      metricVolume n (T '' B)≤b*metricVolume n B)
    {A : Set (Model n)} (hA : MeasurableSet A) (hAs : A⊆d '' G) :
    (a/((C:ℝ≥0∞)^n*(K:ℝ≥0∞)^n))*volume A ≤
        volume ((e ∘ T ∘ d.symm) '' A) ∧
      volume ((e ∘ T ∘ d.symm) '' A) ≤
        ((H:ℝ≥0∞)^n*b*(D:ℝ≥0∞)^n)*volume A := by
  let B := d.symm '' A
  have hAt : A⊆d.target := by
    rintro z hz
    obtain ⟨x,hx,rfl⟩ := hAs hz
    exact d.map_source (hGs hx)
  have hBG : B⊆G := by
    rintro _ ⟨z,hz,rfl⟩
    obtain ⟨x,hx,rfl⟩ := hAs hz
    simpa only [d.left_inv (hGs hx)] using hx
  have hBm : MeasurableSet B := hA.image_of_continuousOn_injOn
    (hdi.mono hAs).continuousOn (d.symm.injOn.mono hAt)
  have hdB : d '' B=A := by
    ext z
    constructor
    · rintro ⟨x,⟨w,hw,rfl⟩,rfl⟩
      simpa only [d.right_inv (hAt hw)] using hw
    · intro hz
      exact ⟨d.symm z,⟨z,hz,rfl⟩,d.right_inv (hAt hz)⟩
  have heB : e '' (T '' B)=(e ∘ T ∘ d.symm) '' A := by
    rw [image_image,image_image]
    rfl
  have hTsB : T '' B⊆T '' G := image_mono hBG
  have H1 := metricVolume_lipschitz_image_le_nat (n := n) (hd.mono hBG)
  rw [hdB,metricVolume_model] at H1
  have H2 := metricVolume_lipschitz_image_le_nat (n := n) (hdi.mono hAs)
  rw [metricVolume_model] at H2
  have H3 := metricVolume_lipschitz_image_le_nat (n := n) (he.mono hTsB)
  rw [heB,metricVolume_model] at H3
  have H4 := metricVolume_lipschitz_image_le_nat (n := n) (hei.mono (image_mono hTsB))
  have hiB : e.symm '' (e '' (T '' B))=T '' B := by
    ext x
    constructor
    · rintro ⟨z,⟨y,hy,rfl⟩,rfl⟩
      simpa only [e.left_inv (hTs (hTsB hy))] using hy
    · intro hx
      exact ⟨e x,⟨x,hx,rfl⟩,e.left_inv (hTs (hTsB hx))⟩
  rw [hiB,heB,metricVolume_model] at H4
  obtain ⟨hlo,hup⟩ := hmass B hBm hBG
  constructor
  · rw [show a/((C:ℝ≥0∞)^n*(K:ℝ≥0∞)^n)*volume A=
        (a*volume A)/((C:ℝ≥0∞)^n*(K:ℝ≥0∞)^n) by
      simp only [div_eq_mul_inv,mul_right_comm]]
    rw [ENNReal.div_le_iff' (mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hC.ne'))
      (pow_ne_zero _ (by exact_mod_cast hK.ne')))
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
        (ENNReal.pow_ne_top ENNReal.coe_ne_top))]
    calc
      _ ≤ a*((C:ℝ≥0∞)^n*metricVolume n B) := mul_le_mul_right H1 _
      _ = (C:ℝ≥0∞)^n*(a*metricVolume n B) := by ac_rfl
      _ ≤ (C:ℝ≥0∞)^n*metricVolume n (T '' B) := mul_le_mul_right hlo _
      _ ≤ (C:ℝ≥0∞)^n*((K:ℝ≥0∞)^n*volume ((e ∘ T ∘ d.symm) '' A)) := mul_le_mul_right H4 _
      _ = _ := by ac_rfl
  · calc
      _ ≤ (H:ℝ≥0∞)^n*metricVolume n (T '' B) := H3
      _ ≤ (H:ℝ≥0∞)^n*(b*metricVolume n B) := mul_le_mul_right hup _
      _ ≤ (H:ℝ≥0∞)^n*(b*((D:ℝ≥0∞)^n*volume A)) :=
        mul_le_mul_right (mul_le_mul_right H2 _) _
      _ = _ := by ac_rfl

end WeakMTWTransport

end

end

end

end OAI
