import Mathlib
import OAI.Analysis.Conductivity.Variational.CentralSmoothTrace

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory
open scoped ENNReal

instance spectralTraceGraph_realInner {ι : Type*} (w : ι → ℝ) :
    InnerProductSpace ℝ (spectralTraceGraph w) := InnerProductSpace.complexToReal

abbrev CentralTraceFields (s : Fin 3 → ℝ) := PiLp 2 (fun _ : Fin 3 => spectralTraceGraph (torusRate s))
abbrev CentralAmbient (s : Fin 3 → ℝ) := WithLp 2 (CentralJets × CentralTraceFields s)

instance centralAmbientNormedSpace (s : Fin 3 → ℝ) : NormedSpace ℝ (CentralAmbient s) := inferInstance
instance centralAmbientInnerProductSpace (s : Fin 3 → ℝ) : InnerProductSpace ℝ (CentralAmbient s) := inferInstance

def centralEmbedL (s : Fin 3 → ℝ) : centralSmoothFunctions →ₗ[ℝ] CentralAmbient s :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ CentralJets (CentralTraceFields s)).symm.toLinearMap.comp
    (centralSmoothJetL.prod
      (((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => spectralTraceGraph (torusRate s))).symm.toLinearMap).comp
        (LinearMap.pi (centralSmoothTraceL s))))

def centralAmbientD (s : Fin 3 → ℝ) : CentralAmbient s →L[ℝ] CentralGradients :=
  centralJetD.comp (WithLp.fstL 2 ℝ CentralJets (CentralTraceFields s))

def centralAmbientT (s : Fin 3 → ℝ) (i : Fin 3) :
    CentralAmbient s →L[ℝ] spectralTraceGraph (torusRate s) :=
  (PiLp.proj 2 (fun _ : Fin 3 => spectralTraceGraph (torusRate s)) i).comp
    (WithLp.sndL 2 ℝ CentralJets (CentralTraceFields s))

def centralAmbientM (s : Fin 3 → ℝ) : CentralAmbient s →L[ℝ] ℝ :=
  (spectralGraphMean (torusRate s)).comp (centralAmbientT s 0)

def centralAmbientOne (s : Fin 3 → ℝ) : CentralAmbient s := centralEmbedL s centralSmoothOne

def centralAmbientQ (s : Fin 3 → ℝ) : CentralAmbient s →L[ℝ] CentralAmbient s :=
  ContinuousLinearMap.id ℝ _-(centralAmbientM s).smulRight (centralAmbientOne s)

lemma centralAmbientD_embed (s : Fin 3 → ℝ) (f : centralSmoothFunctions) :
    centralAmbientD s (centralEmbedL s f)=centralJetD (centralSmoothJet f) := rfl

lemma centralAmbientT_embed (s : Fin 3 → ℝ) (f : centralSmoothFunctions) (i : Fin 3) :
    centralAmbientT s i (centralEmbedL s f)=centralSmoothTrace s f i := rfl

@[simp] lemma centralAmbientM_one (s : Fin 3 → ℝ) : centralAmbientM s (centralAmbientOne s)=1 :=
  centralOne_mean s 0

@[simp] lemma centralAmbientD_one (s : Fin 3 → ℝ) : centralAmbientD s (centralAmbientOne s)=0 :=
  centralOne_gradient

@[simp] lemma centralAmbientWeight_one (s : Fin 3 → ℝ) (i : Fin 3) :
    spectralGraphWeight (torusRate s) (centralAmbientT s i (centralAmbientOne s))=0 :=
  centralOne_weight s i

@[simp] lemma centralAmbientQ_one (s : Fin 3 → ℝ) : centralAmbientQ s (centralAmbientOne s)=0 := by
  simp [centralAmbientQ]

lemma centralAmbientQ_apply (s : Fin 3 → ℝ) (u : CentralAmbient s) :
    centralAmbientQ s u=u-centralAmbientM s u • centralAmbientOne s := rfl

lemma centralEmbed_norm (s : Fin 3 → ℝ) (f : centralSmoothFunctions) :
    ‖centralEmbedL s f‖^2=(∫ z in centralClosed,(f z)^2)+‖centralJetD (centralSmoothJet f)‖^2+
      ∑ i : Fin 3,(‖centralTraceFourier f i‖^2+
        ‖spectralGraphWeight (torusRate s) (centralSmoothTrace s f i)‖^2) := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖centralSmoothJet f‖^2+‖(WithLp.toLp 2 (fun i => centralSmoothTrace s f i) : CentralTraceFields s)‖^2=_
  rw [centralSmoothJet_norm,PiLp.norm_sq_eq_of_L2 _ (WithLp.toLp 2 (fun i => centralSmoothTrace s f i) : CentralTraceFields s)]
  simp only [centralSmoothTrace_norm]

def centralEnergySpace (s : Fin 3 → ℝ) : Submodule ℝ (CentralAmbient s) :=
  (LinearMap.range (centralEmbedL s)).topologicalClosure

instance centralEnergySpace_complete (s : Fin 3 → ℝ) : CompleteSpace (centralEnergySpace s) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

def centralD (s : Fin 3 → ℝ) : centralEnergySpace s →L[ℝ] CentralGradients :=
  (centralAmbientD s).comp (centralEnergySpace s).subtypeL

def centralT (s : Fin 3 → ℝ) (i : Fin 3) :
    centralEnergySpace s →L[ℝ] spectralTraceGraph (torusRate s) :=
  (centralAmbientT s i).comp (centralEnergySpace s).subtypeL

def centralM (s : Fin 3 → ℝ) : centralEnergySpace s →L[ℝ] ℝ :=
  (centralAmbientM s).comp (centralEnergySpace s).subtypeL

def centralOne (s : Fin 3 → ℝ) : centralEnergySpace s :=
  ⟨centralAmbientOne s,(LinearMap.range (centralEmbedL s)).le_topologicalClosure ⟨centralSmoothOne,rfl⟩⟩

end

open Set MeasureTheory

def centralAmbientJ (s : Fin 3 → ℝ) : CentralAmbient s →L[ℝ] CentralJets :=
  WithLp.fstL 2 ℝ CentralJets (CentralTraceFields s)

def centralAmbientTraceL2 (s : Fin 3 → ℝ) (i : Fin 3) :
    CentralAmbient s →L[ℝ] SpectralL2 TorusModes :=
  (((PiLp.proj 2 (fun _ : Fin 2 => SpectralL2 TorusModes) 0).comp
    (spectralTraceGraph (torusRate s)).subtypeL).restrictScalars ℝ).comp (centralAmbientT s i)

lemma centralAmbientTraceL2_embed (s : Fin 3 → ℝ) (f : centralSmoothFunctions) (i : Fin 3) :
    centralAmbientTraceL2 s i (centralEmbedL s f)=centralTraceFourier f i :=
  centralSmoothTrace_fst s f i

lemma central_smooth_trace_jet_bound (f : centralSmoothFunctions) (i : Fin 3) :
    ‖centralTraceFourier f i‖^2≤192*centralTraceConstant*‖centralSmoothJet f‖^2 := by
  have hh := centralTrace_anchor_bound f i
  have he := centralSmoothJet_norm f
  have hn : 0≤∫ z in centralClosed,(f z)^2 := integral_nonneg (fun _ => sq_nonneg _)
  have hm := mul_nonneg centralTraceConstant_pos.le hn
  rw [he]
  nlinarith only [hh,hm]

lemma central_graph_trace_jet_bound (s : Fin 3 → ℝ) (u : centralEnergySpace s) (i : Fin 3) :
    ‖centralAmbientTraceL2 s i u.val‖^2≤192*centralTraceConstant*‖centralAmbientJ s u.val‖^2 := by
  have hc : IsClosed {v : CentralAmbient s | ‖centralAmbientTraceL2 s i v‖^2≤
      192*centralTraceConstant*‖centralAmbientJ s v‖^2} :=
    isClosed_le ((centralAmbientTraceL2 s i).continuous.norm.pow 2)
      (continuous_const.mul ((centralAmbientJ s).continuous.norm.pow 2))
  apply closure_minimal (t:= {v : CentralAmbient s | ‖centralAmbientTraceL2 s i v‖^2≤
      192*centralTraceConstant*‖centralAmbientJ s v‖^2}) _ hc u.property
  rintro v ⟨f,rfl⟩
  change ‖centralAmbientTraceL2 s i (centralEmbedL s f)‖^2≤_
  rw [centralAmbientTraceL2_embed]
  exact central_smooth_trace_jet_bound f i

lemma central_graph_jet_injective (s : Fin 3 → ℝ) :
    Function.Injective (fun u : centralEnergySpace s => centralAmbientJ s u.val) := by
  intro u v huv
  have hz : centralAmbientJ s (u-v).val=0 := by
    change centralAmbientJ s (u.val-v.val)=0
    exact (map_sub (centralAmbientJ s) u.val v.val).trans (sub_eq_zero.mpr huv)
  have ht (i : Fin 3) : centralAmbientT s i (u-v).val=0 := by
    apply spectralTraceGraph_fst_injective (torusRate s)
    change centralAmbientTraceL2 s i (u-v).val=0
    have hb := central_graph_trace_jet_bound s (u-v) i
    rw [hz,norm_zero,zero_pow (by decide : (2:ℕ)≠0),mul_zero] at hb
    exact norm_eq_zero.mp (by nlinarith only [hb,norm_nonneg (centralAmbientTraceL2 s i (u-v).val)])
  have hval : (u-v).val=0 := by
    apply (WithLp.equiv 2 (CentralJets × CentralTraceFields s)).injective
    apply Prod.ext
    · exact hz
    · apply PiLp.ext
      exact ht
  exact sub_eq_zero.mp (Subtype.ext hval)

end ScalarConductivity

end

end OAI
