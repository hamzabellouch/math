import Mathlib
import OAI.Analysis.Conductivity.Sobolev.SobolevMaximum
import OAI.Analysis.Conductivity.Variational.VoltageBoundaryTrace

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal NNReal
local instance physicalRealTraceMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance physicalRealTraceIsProbabilityMeasure : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma H1_eq_of_value_ae {u v : H1} (h : weakValue u=ᵐ[ballMeasure] weakValue v) : u=v := by
  apply weakValueL_injective
  apply Lp.ext
  exact (weakValueL_apply_ae u).trans (h.trans (weakValueL_apply_ae v).symm)

lemma SmoothLipZero.lipschitz (F : SmoothLipZero) : LipschitzWith (⟨F.bound,F.bound_nonneg⟩ : ℝ≥0) F :=
  lipschitzWith_of_nnnorm_deriv_le (F.smooth.differentiable (by simp)) (fun x => F.deriv_bound x)

lemma SmoothLipZero.onH1_smooth (F : SmoothLipZero) {f : R3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) : F.onH1 (smoothH1 f hf)=smoothH1 (F ∘ f) (F.smooth.comp hf) := by
  apply H1_eq_of_value_ae
  filter_upwards [F.onH1_value (smoothH1 f hf),smoothH1_value f hf,
    smoothH1_value (F ∘ f) (F.smooth.comp hf)] with x hF hf hh
  change weakValue (F.onH1 (smoothH1 f _)) x=F (weakValue (smoothH1 f _) x) at hF
  rw [hF,hf,hh]
  rfl

def physicalComplexTraceCLM (i : Fin 3) : H1 →L[ℝ] TorusL2 :=
  (((mFourierBasis (d:=Fin 2)).repr.symm.toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ).comp
    (physicalOuterTraceCLM i)

def physicalRealTraceCLM (i : Fin 3) : H1 →L[ℝ] Lp ℝ 2 (volume : Measure (UnitAddTorus (Fin 2))) :=
  (Complex.reCLM.compLpL 2 volume).comp (physicalComplexTraceCLM i)

lemma physicalRealTrace_smooth_ae (i : Fin 3) {f : R3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) :
    physicalRealTraceCLM i (smoothH1 f hf)=ᵐ[volume]
      fun θ => f (WithLp.toLp 2 (physicalOuterBoundary i θ)) := by
  have he : physicalComplexTraceCLM i (smoothH1 f hf)=
      ContinuousMap.toLp 2 volume ℂ (continuousOuterMap i hf.continuous) := by
    change (mFourierBasis (d:=Fin 2)).repr.symm (physicalOuterTraceCLM i (smoothH1 f hf))=_
    rw [smoothOuterFourier_original]
    exact (mFourierBasis (d:=Fin 2)).repr.symm_apply_apply _
  have hh := Complex.reCLM.coeFn_compLpL (p:=2) (μ:=volume) (physicalComplexTraceCLM i (smoothH1 f hf))
  change physicalRealTraceCLM i (smoothH1 f hf)=ᵐ[volume] _ at hh
  rw [he] at hh
  filter_upwards [hh,ContinuousMap.coeFn_toLp (continuousOuterMap i hf.continuous) (p:=2) (μ:=volume) (𝕜:=ℂ)]
    with θ hθ hv
  rw [hθ,hv]
  rfl

theorem physicalRealTrace_chain (F : SmoothLipZero) (i : Fin 3) (u : H1) :
    physicalRealTraceCLM i (F.onH1 u)=F.lipschitz.compLp F.at_zero (physicalRealTraceCLM i u) := by
  have hc : IsClosed {u : H1 | physicalRealTraceCLM i (F.onH1 u)=
      F.lipschitz.compLp F.at_zero (physicalRealTraceCLM i u)} :=
    isClosed_eq ((physicalRealTraceCLM i).continuous.comp F.onH1_continuous)
      ((F.lipschitz.continuous_compLp F.at_zero).comp (physicalRealTraceCLM i).continuous)
  apply (closure_minimal (s:={u : H1 | u.val∈smoothJets}) ?_ hc) (smoothH1_dense u)
  rintro v ⟨f,hf,hm,he⟩
  have hv : v=smoothH1 f hf := Subtype.ext he
  change physicalRealTraceCLM i (F.onH1 v)=_
  rw [hv,F.onH1_smooth]
  apply Lp.ext
  filter_upwards [physicalRealTrace_smooth_ae i (F.smooth.comp hf),
    F.lipschitz.coeFn_compLp F.at_zero (physicalRealTraceCLM i (smoothH1 f hf)),
    physicalRealTrace_smooth_ae i hf] with θ hF hc hhf
  rw [hF,hc]
  change F (f (WithLp.toLp 2 (physicalOuterBoundary i θ)))=F (physicalRealTraceCLM i (smoothH1 f hf) θ)
  rw [hhf]

theorem physicalRealTrace_upper_bound (i : Fin 3) (u : H1) {M : ℝ} (hM : 0≤M)
    (hb : ∀ᵐ x∂ballMeasure,weakValue u x≤M) :
    ∀ᵐ θ : UnitAddTorus (Fin 2),physicalRealTraceCLM i u θ≤M := by
  let F := upperTransition M hM
  have hz : F.onH1 u=0 := by
    apply h1_eq_zero_of_value_zero
    filter_upwards [F.onH1_value u,hb] with x hx hb
    change weakValue (F.onH1 u) x=F (weakValue u x) at hx
    rw [hx]
    exact (upperTransition_zero_iff M hM _).mpr hb
  have ht := physicalRealTrace_chain F i u
  rw [hz,map_zero] at ht
  have he := (Lp.ext_iff.mp ht).symm.trans (Lp.coeFn_zero ℝ 2 (volume : Measure (UnitAddTorus (Fin 2))))
  filter_upwards [he,F.lipschitz.coeFn_compLp F.at_zero (physicalRealTraceCLM i u)] with θ hz hc
  exact (upperTransition_zero_iff M hM _).mp (hc.symm.trans hz)

end ScalarConductivity

end
end

end OAI
