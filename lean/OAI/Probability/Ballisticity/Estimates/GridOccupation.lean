import Mathlib
import OAI.Probability.Ballisticity.Estimates.FinitePastDecorrelation

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def layerGridPoint (a : ℝ) (j : ℕ) : unitInterval :=
  Set.projIcc 0 1 (by norm_num) ((j:ℝ)/a)

lemma layerGridPoint_coe {a : ℝ} (ha : 0 < a) {j : ℕ} (hj : (j:ℝ) ≤ a) :
    (layerGridPoint a j : ℝ) = (j:ℝ)/a := by
  exact congrArg Subtype.val (Set.projIcc_of_mem (by norm_num : (0:ℝ) ≤ 1)
    ⟨div_nonneg (Nat.cast_nonneg _) ha.le,(div_le_one ha).mpr hj⟩)

lemma layerGridPoint_floor_dist {a : ℝ} (ha : 0 < a) (t : unitInterval) :
    dist t (layerGridPoint a ⌊a*(t:ℝ)⌋₊) ≤ 1/a := by
  have h0 : 0 ≤ a*(t:ℝ) := mul_nonneg ha.le t.2.1
  have hlo := Nat.floor_le h0
  have hhi := Nat.lt_floor_add_one (a*(t:ℝ))
  have hja : (⌊a*(t:ℝ)⌋₊:ℝ) ≤ a := hlo.trans (mul_le_of_le_one_right ha.le t.2.2)
  rw [Subtype.dist_eq,Real.dist_eq,layerGridPoint_coe ha hja,
    abs_of_nonneg (sub_nonneg.mpr ((div_le_iff₀ ha).mpr (by nlinarith))) ]
  apply (le_div_iff₀ ha).mpr
  have he : ((t:ℝ)-(⌊a*(t:ℝ)⌋₊:ℝ)/a)*a = (t:ℝ)*a-(⌊a*(t:ℝ)⌋₊:ℝ) := by field_simp
  rw [he]
  linarith

lemma volume_layer_cell_le {a : ℝ} (ha : 0 < a) (j : ℕ) :
    volume {t : unitInterval | ⌊a*(t:ℝ)⌋₊ = j} ≤ ENNReal.ofReal (1/a) := by
  rw [unitInterval.volume_apply]
  calc
    volume (Subtype.val '' {t : unitInterval | ⌊a*(t:ℝ)⌋₊ = j}) ≤
        volume (Set.Icc ((j:ℝ)/a) (((j:ℝ)+1)/a)) := by
      apply measure_mono
      rintro _ ⟨t,ht,rfl⟩
      have hlo := Nat.floor_le (mul_nonneg ha.le t.2.1)
      have hhi := Nat.lt_floor_add_one (a*(t:ℝ))
      rw [ht] at hlo hhi
      exact ⟨(div_le_iff₀ ha).mpr (by nlinarith),
        (le_div_iff₀ ha).mpr (by nlinarith)⟩
    _ = ENNReal.ofReal (1/a) := by rw [Real.volume_Icc]; congr 1; ring

noncomputable def layerGap (P : RealPathPair) (t : unitInterval) : ℝ := P.2 t-P.1 t

lemma continuous_layerGap : Continuous (fun z : RealPathPair × unitInterval => layerGap z.1 z.2) :=
  (continuous_eval.comp (continuous_fst.snd.prodMk continuous_snd)).sub
    (continuous_eval.comp (continuous_fst.fst.prodMk continuous_snd))

lemma gap_grid_close {a ε δ : ℝ} (ha : 0 < a) (hδ : 1/a ≤ δ)
    (P : RealPathPair) (t : unitInterval)
    (h1 : P.1 ∉ ContinuousOscillation ε δ) (h2 : P.2 ∉ ContinuousOscillation ε δ) :
    |layerGap P t-layerGap P (layerGridPoint a ⌊a*(t:ℝ)⌋₊)| ≤ 2*ε := by
  have hd := (layerGridPoint_floor_dist ha t).trans hδ
  have hm1 : |P.1 t-P.1 (layerGridPoint a ⌊a*(t:ℝ)⌋₊)| ≤ ε :=
    le_of_not_gt (fun h => h1 ⟨t,_,hd,h⟩)
  have hm2 : |P.2 t-P.2 (layerGridPoint a ⌊a*(t:ℝ)⌋₊)| ≤ ε :=
    le_of_not_gt (fun h => h2 ⟨t,_,hd,h⟩)
  calc
    |layerGap P t-layerGap P (layerGridPoint a ⌊a*(t:ℝ)⌋₊)| =
        |(P.2 t-P.2 (layerGridPoint a ⌊a*(t:ℝ)⌋₊))-
          (P.1 t-P.1 (layerGridPoint a ⌊a*(t:ℝ)⌋₊))| := by congr 1; dsimp [layerGap]; ring
    _ ≤ |P.2 t-P.2 (layerGridPoint a ⌊a*(t:ℝ)⌋₊)|+
          |P.1 t-P.1 (layerGridPoint a ⌊a*(t:ℝ)⌋₊)| := by
      simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le
        (P.2 t-P.2 (layerGridPoint a ⌊a*(t:ℝ)⌋₊)) 0
        (P.1 t-P.1 (layerGridPoint a ⌊a*(t:ℝ)⌋₊))
    _ ≤ 2*ε := by linarith

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma IsGaussianSequence.comp {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {S : Ω → ℝ} {r : ℕ → ℝ} (hr : IsGaussianSequence μ S r)
    {v : ℕ → ℕ} (hv : Tendsto v atTop atTop) : IsGaussianSequence μ S (r ∘ v) :=
  ⟨hr.1.comp hv,fun a ha => (hr.2 a ha).comp hv⟩

lemma layerGridPoint_tendsto (a : ℕ → ℝ) (j : ℕ → ℕ) (v : unitInterval)
    (h : Tendsto (fun i => (j i:ℝ)/a i) atTop (𝓝 (v:ℝ))) :
    Tendsto (fun i => layerGridPoint (a i) (j i)) atTop (𝓝 v) := by
  have hh := (continuous_projIcc (a := (0:ℝ)) (b := 1) (h := by norm_num)).continuousAt.tendsto.comp h
  simpa only [layerGridPoint,Function.comp_def,Set.projIcc_of_mem (by norm_num : (0:ℝ)≤1) v.2,Subtype.eta] using hh

noncomputable def interiorPastGrid {q : ℕ} (a : ℝ) (v : Fin q → unitInterval)
    (s t : unitInterval) : JointPastTimes q :=
  ((fun z => layerGridPoint a ⌊(v z:ℝ)*a⌋₊),
    layerGridPoint a (⌊(s:ℝ)*a⌋₊+1),
    layerGridPoint a ((⌊(s:ℝ)*a⌋₊+1)+⌊((t:ℝ)-s)*a⌋₊))

lemma interiorPastGrid_tendsto {q : ℕ} (a : ℕ → ℝ) (ha : Tendsto a atTop atTop)
    (v : Fin q → unitInterval) (s t : unitInterval) (hst : s ≤ t) :
    Tendsto (fun i => interiorPastGrid (a i) v s t) atTop (𝓝 (v,s,t)) := by
  have hH : Tendsto (fun i => ((⌊(s:ℝ)*a i⌋₊+1:ℕ):ℝ)/a i) atTop (𝓝 (s:ℝ)) := by
    have hh := ((tendsto_nat_floor_mul_div_atTop s.2.1).comp ha).add
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)).div_atTop ha)
    simpa [Nat.cast_add,add_div] using hh
  apply Tendsto.prodMk_nhds
  · apply tendsto_pi_nhds.mpr
    intro z
    exact layerGridPoint_tendsto a _ (v z) ((tendsto_nat_floor_mul_div_atTop (v z).2.1).comp ha)
  · apply Tendsto.prodMk_nhds
    · exact layerGridPoint_tendsto a _ s hH
    · apply layerGridPoint_tendsto a _ t
      have hh := hH.add ((tendsto_nat_floor_mul_div_atTop (sub_nonneg.mpr (show (s:ℝ)≤t from hst))).comp ha)
      simpa [Nat.cast_add,add_div] using hh

lemma interiorPastGrid_eventually {q : ℕ} (a : ℕ → ℝ) (ha : Tendsto a atTop atTop)
    (v : Fin q → unitInterval) (s t : unitInterval) (hv : ∀ z, v z ≤ s)
    (hst : s ≤ t) (ht : (t:ℝ)<1) :
    ∀ᶠ i in atTop, 0<a i ∧
      (∀ z, ⌊(v z:ℝ)*a i⌋₊≤⌊(s:ℝ)*a i⌋₊+1) ∧
      (((⌊(s:ℝ)*a i⌋₊+1)+⌊((t:ℝ)-s)*a i⌋₊:ℕ):ℝ)≤a i ∧
      (∀ z, a i*(interiorPastGrid (a i) v s t |>.1 z:ℝ)=⌊(v z:ℝ)*a i⌋₊) ∧
      a i*(interiorPastGrid (a i) v s t |>.2.1:ℝ)=(⌊(s:ℝ)*a i⌋₊+1:ℕ) ∧
      a i*(interiorPastGrid (a i) v s t |>.2.2:ℝ)=
        ((⌊(s:ℝ)*a i⌋₊+1:ℕ):ℝ)+⌊((t:ℝ)-s)*a i⌋₊ := by
  filter_upwards [ha.eventually_gt_atTop 0,ha.eventually_ge_atTop (1/(1-(t:ℝ)))] with i hi hi'
  have he : 1≤(1-(t:ℝ))*a i := (div_le_iff₀ (sub_pos.mpr ht)).mp hi' |>.trans_eq (mul_comm _ _)
  have hf := Nat.floor_le (mul_nonneg s.2.1 hi.le)
  have hg := Nat.floor_le (mul_nonneg (sub_nonneg.mpr (show (s:ℝ)≤t from hst)) hi.le)
  have htot : (((⌊(s:ℝ)*a i⌋₊+1)+⌊((t:ℝ)-s)*a i⌋₊:ℕ):ℝ)≤a i := by
    push_cast
    nlinarith
  have hH : ((⌊(s:ℝ)*a i⌋₊+1:ℕ):ℝ)≤a i := by
    have := Nat.cast_nonneg (α := ℝ) ⌊((t:ℝ)-s)*a i⌋₊
    push_cast at htot ⊢
    linarith
  have hj (z : Fin q) : (⌊(v z:ℝ)*a i⌋₊:ℝ)≤a i :=
    (Nat.floor_le (mul_nonneg (v z).2.1 hi.le)).trans
      (mul_le_of_le_one_left hi.le (v z).2.2)
  have hid (j : ℕ) (hh : (j:ℝ)≤a i) : a i*(layerGridPoint (a i) j:ℝ)=j := by
    rw [layerGridPoint_coe hi hh,mul_div_cancel₀ _ hi.ne']
  have hvs (z : Fin q) : (v z : ℝ) ≤ (s : ℝ) := hv z
  refine ⟨hi,fun z => (Nat.floor_mono (mul_le_mul_of_nonneg_right (hvs z) hi.le)).trans (Nat.le_succ _),htot,?_,hid _ hH,?_⟩
  · exact fun z => hid _ (hj z)
  · simpa only [Nat.cast_add,interiorPastGrid] using hid _ htot

end DirectionalTransience

end

end

end OAI
