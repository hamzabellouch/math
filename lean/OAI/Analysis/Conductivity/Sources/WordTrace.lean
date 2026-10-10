import Mathlib
import OAI.Analysis.Conductivity.Sources.NestedWeightedLimit
import OAI.Analysis.Conductivity.Branching.ChildJetScaling
import OAI.Analysis.Conductivity.Sources.WordGeometry
import OAI.Analysis.Conductivity.Sources.PhysicalMaximum
import OAI.Analysis.Conductivity.Sources.CopiedEnergyAlgebra
import OAI.Analysis.Conductivity.Branching.PhysicalTraceTransport
import OAI.Analysis.Conductivity.Sobolev.OriginalMultiplierOperator

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def sourceWordPull : SourceWord → H1 →L[ℝ] H1
  | [] => ContinuousLinearMap.id ℝ H1
  | k::ν => (sourceWordPull ν).comp (childH1Pullback k)

lemma sourceWordMap_contDiff (ν : SourceWord) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (sourceWordMap ν : R3 → R3) := by
  induction ν with
  | nil => exact contDiff_id
  | cons k ν ih => exact (sourceChildEuclidean_contDiff _).comp ih

lemma sourceWordPull_smooth (ν : SourceWord) {f : R3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) :
    sourceWordPull ν (smoothH1 f hf)=smoothH1 (f ∘ sourceWordMap ν) (hf.comp (sourceWordMap_contDiff ν)) := by
  induction ν generalizing f with
  | nil => rfl
  | cons k ν ih =>
    change sourceWordPull ν (childH1Pullback k (smoothH1 f hf))=_
    rw [childH1Pullback_smooth,ih]
    rfl

lemma childH1Pullback_bound (k : Fin 2) (u : H1) {M : ℝ}
    (hb : ∀ᵐ x∂ballMeasure,abs (weakValue u x) ≤ M) :
    ∀ᵐ x∂ballMeasure,abs (weakValue (childH1Pullback k u) x) ≤ M := by
  filter_upwards [childH1Pullback_value k u,(sourceChildEuclidean_ball_quasi k).ae hb] with x hx hy
  rw [hx]; exact hy

lemma sourceWordPull_bound (ν : SourceWord) (u : H1) {M : ℝ}
    (hb : ∀ᵐ x∂ballMeasure,abs (weakValue u x) ≤ M) :
    ∀ᵐ x∂ballMeasure,abs (weakValue (sourceWordPull ν u) x) ≤ M := by
  induction ν generalizing u with
  | nil => exact hb
  | cons k ν ih => exact ih _ (childH1Pullback_bound k u hb)

def sourceWordTraceCLM (ν : SourceWord) : H1 →L[ℝ] Lp ℝ 2 (volume : Measure (UnitAddTorus (Fin 2))) :=
  (physicalRealTraceCLM 0).comp (sourceWordPull ν)

def sourceWordBoundary (ν : SourceWord) (θ : UnitAddTorus (Fin 2)) : R3 :=
  sourceWordMap ν (WithLp.toLp 2 (physicalOuterBoundary 0 θ))

lemma sourceWordBoundary_continuous (ν : SourceWord) : Continuous (sourceWordBoundary ν) :=
  (sourceWordMap ν).continuous.comp ((PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
    (physicalOuterBoundary_continuous 0))

lemma sourceWordTrace_smooth (ν : SourceWord) {f : R3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) :
    sourceWordTraceCLM ν (smoothH1 f hf)=ᵐ[volume] (fun θ => f (sourceWordBoundary ν θ)) := by
  change physicalRealTraceCLM 0 (sourceWordPull ν (smoothH1 f hf))=ᵐ[volume] _
  rw [sourceWordPull_smooth]
  exact physicalRealTrace_smooth_ae 0 (hf.comp (sourceWordMap_contDiff ν))

lemma sourceWordTrace_mul (ν : SourceWord) {f : R3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) (hc : HasCompactSupport f) (u : H1) :
    sourceWordTraceCLM ν (originalMulH1CLM hf hc u)=ᵐ[volume]
      (fun θ => f (sourceWordBoundary ν θ)*sourceWordTraceCLM ν u θ) := by
  let χ : UnitAddTorus (Fin 2) → ℝ := f ∘ sourceWordBoundary ν
  have hχ : Continuous χ := hf.continuous.comp (sourceWordBoundary_continuous ν)
  have hχc : HasCompactSupport χ := HasCompactSupport.of_compactSpace _
  have he : sourceWordTraceCLM ν (originalMulH1CLM hf hc u)=
      compactMultiplierCLM hχ hχc (sourceWordTraceCLM ν u) := by
    have hclosed : IsClosed {u : H1 | sourceWordTraceCLM ν (originalMulH1CLM hf hc u)=
        compactMultiplierCLM hχ hχc (sourceWordTraceCLM ν u)} :=
      isClosed_eq ((sourceWordTraceCLM ν).continuous.comp (originalMulH1CLM hf hc).continuous)
        ((compactMultiplierCLM hχ hχc).continuous.comp (sourceWordTraceCLM ν).continuous)
    apply (closure_minimal (s:={u : H1 | u.val∈smoothJets}) ?_ hclosed) (smoothH1_dense u)
    rintro v ⟨g,hg,_,hv⟩
    have he : v=smoothH1 g hg := Subtype.ext hv
    change sourceWordTraceCLM ν (originalMulH1CLM hf hc v)=_
    rw [he,originalMulH1_smooth]
    apply Lp.ext
    filter_upwards [sourceWordTrace_smooth ν (hf.mul hg),sourceWordTrace_smooth ν hg,
      compactMultiplierCLM_ae hχ hχc (sourceWordTraceCLM ν (smoothH1 g hg))] with θ h0 h1 h2
    exact h0.trans (by rw [h2,h1]; rfl)
  rw [he]
  exact compactMultiplierCLM_ae hχ hχc (sourceWordTraceCLM ν u)

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma constantH1_eq_smooth (c : ℝ) : constantH1 c=smoothH1 (fun _ => c) contDiff_const := by
  apply H1_eq_of_value_ae
  exact (constantH1_value c).trans (smoothH1_value _ contDiff_const).symm

lemma sourceWordTrace_constant (ν : SourceWord) (c : ℝ) :
    sourceWordTraceCLM ν (constantH1 c)=ᵐ[volume] (fun _ => c) := by
  rw [constantH1_eq_smooth]
  exact sourceWordTrace_smooth ν contDiff_const

lemma sourceWordMean_constant (ν : SourceWord) (c : ℝ) :
    sourceMeanCLM 0 (sourceWordPull ν (constantH1 c))=c := by
  rw [sourceMean_eq_integral]
  change (∫ θ,sourceWordTraceCLM ν (constantH1 c) θ)=c
  rw [integral_congr_ae (sourceWordTrace_constant ν c)]
  simp

namespace BoundedRootSources
variable (r : BoundedRootSources)
lemma sourceHarmonic_word {u : H1} (hu : r.sourceHarmonic u) (ν : SourceWord) :
    r.sourceHarmonic (sourceWordPull ν u) := by
  induction ν generalizing u with
  | nil => exact hu
  | cons k ν ih => exact ih (r.sourceHarmonic_child hu k)

lemma sourceHarmonic_word_mean {u : H1} (hu : r.sourceHarmonic u) (ν : SourceWord) :
    sourceMeanCLM 0 (sourceWordPull ν u)=sourceMeanCLM 0 u := by
  induction ν generalizing u with
  | nil => rfl
  | cons k ν ih =>
    change sourceMeanCLM 0 (sourceWordPull ν (childH1Pullback k u))=_
    rw [ih (r.sourceHarmonic_child hu k),r.sourceHarmonic_mean hu k]

lemma sourceHarmonic_trace_centered_mean {u : H1} (hu : r.sourceHarmonic u) (ν : SourceWord) :
    (∫ θ,sourceWordTraceCLM ν (u-constantH1 (sourceMeanCLM 0 u)) θ)=0 := by
  change (∫ θ,physicalRealTraceCLM 0 (sourceWordPull ν (u-constantH1 (sourceMeanCLM 0 u))) θ)=0
  rw [←sourceMean_eq_integral,map_sub,map_sub,r.sourceHarmonic_word_mean hu ν,sourceWordMean_constant,sub_self]
end BoundedRootSources

lemma sourceWordBoundary_radius : ∃ D : ℝ,0 ≤ D ∧ ∀ ν θ,
    dist (sourceWordBoundary ν θ) (sourceWordMap ν 0) ≤ D*sourceScale^ν.length := by
  let f : UnitAddTorus (Fin 2) → ℝ := fun θ => dist (sourceWordBoundary [] θ) 0
  have hf : Continuous f := (sourceWordBoundary_continuous []).dist continuous_const
  obtain ⟨D,hD⟩ := (HasCompactSupport.of_compactSpace f).exists_bound_of_continuous hf
  have hD0 : 0 ≤ D := (norm_nonneg (f 0)).trans (hD 0)
  refine ⟨D,hD0,?_⟩
  intro ν θ
  change dist (sourceWordMap ν (WithLp.toLp 2 (physicalOuterBoundary 0 θ))) (sourceWordMap ν 0) ≤ _
  rw [sourceWordMap_dist]
  have hh : dist (WithLp.toLp 2 (physicalOuterBoundary 0 θ)) 0 ≤ D := by
    simpa only [f,sourceWordBoundary,sourceWordMap_nil,Real.norm_eq_abs,abs_of_nonneg dist_nonneg] using hD θ
  nlinarith [pow_nonneg (show 0 ≤ sourceScale by norm_num [sourceScale]) ν.length]

lemma sourceWord_weighted_mean_bound (r : BoundedRootSources) {u : H1}
    (hu : r.sourceHarmonic u) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ᵐ x∂ballMeasure,abs (weakValue u x) ≤ M)
    {f : R3 → ℝ} (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) (hc : HasCompactSupport f)
    {L D : ℝ} (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hlip : ∀ x y,abs (f x-f y) ≤ L*dist x y)
    (hdiam : ∀ ν θ,dist (sourceWordBoundary ν θ) (sourceWordMap ν 0) ≤ D*sourceScale^ν.length)
    (ν : SourceWord) :
    abs (sourceMeanCLM 0 (sourceWordPull ν
      (originalMulH1CLM hf hc (u-constantH1 (sourceMeanCLM 0 u))))) ≤
        (2*M*L*D)*sourceScale^ν.length := by
  let v := u-constantH1 (sourceMeanCLM 0 u)
  have hv : ∀ᵐ x∂ballMeasure,abs (weakValue v x) ≤ 2*M := by
    filter_upwards [hb,(H1_sub_constant_spec u (sourceMeanCLM 0 u)).1] with x hx he
    change abs (weakValue (u-constantH1 (sourceMeanCLM 0 u)) x) ≤ _
    rw [he]
    have hm := sourceMean_bound 0 u hM hb
    exact (abs_sub _ _).trans (by linarith)
  let t := sourceWordTraceCLM ν v
  have ht : Integrable t := (Lp.memLp t).integrable (by norm_num)
  have htb : ∀ᵐ θ,abs (t θ) ≤ 2*M := physicalRealTrace_bound 0 (sourceWordPull ν v)
    (by positivity) (sourceWordPull_bound ν v hv)
  have hz : (∫ θ,t θ)=0 := r.sourceHarmonic_trace_centered_mean hu ν
  obtain ⟨A,hA⟩ := hc.exists_bound_of_continuous hf.continuous
  have htf : Integrable (fun θ => t θ*f (sourceWordBoundary ν θ)) :=
    ht.mul_bdd (hf.continuous.comp (sourceWordBoundary_continuous ν)).aestronglyMeasurable
      (Eventually.of_forall (fun θ => hA (sourceWordBoundary ν θ)))
  have ho : ∀ᵐ θ,abs (f (sourceWordBoundary ν θ)-f (sourceWordMap ν 0)) ≤ L*(D*sourceScale^ν.length) :=
    Eventually.of_forall (fun θ => (hlip _ _).trans (mul_le_mul_of_nonneg_left (hdiam ν θ) hL))
  have hh := surface_cancellation_bound volume t (f ∘ sourceWordBoundary ν)
    (f (sourceWordMap ν 0)) (2*M) (L*(D*sourceScale^ν.length)) (by positivity)
    (mul_nonneg hL (mul_nonneg hD (pow_nonneg (by norm_num [sourceScale]) _))) ht htf hz htb ho
  rw [sourceMean_eq_integral]
  change abs (∫ θ,sourceWordTraceCLM ν (originalMulH1CLM hf hc v) θ) ≤ _
  rw [integral_congr_ae (sourceWordTrace_mul ν hf hc v)]
  have he : (∫ θ,f (sourceWordBoundary ν θ)*t θ)=(∫ θ,t θ*f (sourceWordBoundary ν θ)) := by
    congr 1; funext θ; ring
  rw [he]
  exact hh.trans_eq (by ring)

end ScalarConductivity

end
end

end OAI
