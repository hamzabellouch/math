import Mathlib
import OAI.Analysis.Conductivity.Variational.CentralUnnormalizedVariational

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def centralDirection (i : Fin 3) : Box3 := ![((1,0),0),((0,1),0),((0,0),1)] i

lemma centralJetField_succ (f : Box3 → ℝ) (i : Fin 3) :
    centralJetField f i.succ=cubePartial f (centralDirection i) := by
  fin_cases i <;> rfl

lemma central_smooth_integration_by_parts {f ψ : Box3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ⊆centralClosed) (v : Box3) :
    (∫ x,ψ x*fderiv ℝ f x v ∂centralMeasure)=
      -(∫ x,fderiv ℝ ψ x v*f x ∂centralMeasure) := by
  have hdf : Continuous (fun x => fderiv ℝ f x v) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdψ : Continuous (fun x => fderiv ℝ ψ x v) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  let : (volume : Measure Box3).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure (volume : Measure (ℝ×ℝ)) (volume : Measure ℝ)
  have he := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := ψ) (g := f) (v := v)
    ((hdψ.mul hf.continuous).integrable_of_hasCompactSupport (hc.fderiv_apply ℝ v).mul_right)
    ((hψ.continuous.mul hdf).integrable_of_hasCompactSupport hc.mul_right)
    ((hψ.continuous.mul hf.continuous).integrable_of_hasCompactSupport hc.mul_right)
    (fun x _ => hψ.differentiable (by simp) x)
    (fun x _ => hf.differentiable (by simp) x)
  have hl : (∫ x,ψ x*fderiv ℝ f x v ∂centralMeasure)=∫ x,ψ x*fderiv ℝ f x v := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun hh => hx (hs hh)),zero_mul]
  have hr : (∫ x,fderiv ℝ ψ x v*f x ∂centralMeasure)=∫ x,fderiv ℝ ψ x v*f x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [fderiv_of_notMem_tsupport ℝ (fun hh => hx (hs hh))]
    simp
  rw [hl,hr]
  exact he

def centralAmbientComponent (s : Fin 3 → ℝ) (i : Fin 4) :
    CentralAmbient s →L[ℝ] CentralL2 :=
  (PiLp.proj 2 (fun _ : Fin 4 => CentralL2) i).comp (centralAmbientJ s)

theorem central_distributional_derivative (s : Fin 3 → ℝ)
    (u : centralEnergySpace s) (ψ : centralSmoothFunctions)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ⊆centralClosed) (i : Fin 3) :
    inner ℝ (centralSmoothJet ψ 0) (centralAmbientComponent s i.succ u.val)=
      -inner ℝ (centralSmoothJet ψ i.succ) (centralAmbientComponent s 0 u.val) := by
  have hclosed : IsClosed {z : CentralAmbient s |
      inner ℝ (centralSmoothJet ψ 0) (centralAmbientComponent s i.succ z)=
        -inner ℝ (centralSmoothJet ψ i.succ) (centralAmbientComponent s 0 z)} :=
    isClosed_eq (continuous_const.inner (centralAmbientComponent s i.succ).continuous)
      ((continuous_const.inner (centralAmbientComponent s 0).continuous).neg)
  apply closure_minimal _ hclosed u.property
  rintro z ⟨f,rfl⟩
  change inner ℝ (centralSmoothJet ψ 0) (centralSmoothJet f i.succ)=
    -inner ℝ (centralSmoothJet ψ i.succ) (centralSmoothJet f 0)
  rw [L2.inner_def,L2.inner_def]
  have hl : (∫ x,inner ℝ (centralSmoothJet ψ 0 x) (centralSmoothJet f i.succ x) ∂centralMeasure)=
      ∫ x,ψ x*fderiv ℝ f x (centralDirection i) ∂centralMeasure := by
    apply integral_congr_ae
    filter_upwards [centralSmoothJet_ae ψ 0,centralSmoothJet_ae f i.succ] with x hx hy
    rw [hx,hy,centralJetField_succ]
    simp only [centralJetField,Matrix.cons_val_zero,Real.inner_apply,cubePartial]
  have hr : (∫ x,inner ℝ (centralSmoothJet ψ i.succ x) (centralSmoothJet f 0 x) ∂centralMeasure)=
      ∫ x,fderiv ℝ ψ x (centralDirection i)*f x ∂centralMeasure := by
    apply integral_congr_ae
    filter_upwards [centralSmoothJet_ae ψ i.succ,centralSmoothJet_ae f 0] with x hx hy
    rw [hx,hy,centralJetField_succ]
    simp only [centralJetField,Matrix.cons_val_zero,Real.inner_apply,cubePartial,mul_comm]
  rw [hl,hr]
  exact central_smooth_integration_by_parts (central_smooth f) (central_smooth ψ) hc hs _

def centralSmoothElement (s : Fin 3 → ℝ) (f : centralSmoothFunctions) : centralEnergySpace s :=
  ⟨centralEmbedL s f,(LinearMap.range (centralEmbedL s)).le_topologicalClosure ⟨f,rfl⟩⟩

lemma central_trace_zero (s : Fin 3 → ℝ) (ψ : centralSmoothFunctions) (i : Fin 3)
    (hz : ∀ x,ψ (centralBoundary i x)=0) : centralT s i (centralSmoothElement s ψ)=0 := by
  apply spectralTraceGraph_fst_injective (torusRate s)
  change (centralSmoothTrace s ψ i).val 0=0
  rw [centralSmoothTrace_fst]
  apply norm_eq_zero.mp
  have hn := centralTraceFourier_norm ψ i
  simp only [hz,zero_pow (by decide : 2≠0),integral_zero] at hn
  nlinarith only [hn,norm_nonneg (centralTraceFourier ψ i)]

def CentralVariationalEquation (s slopes : Fin 3 → ℝ) (p : centralEnergySpace s) : Prop :=
  ∀ v : centralEnergySpace s,
    inner ℝ (centralD s p) (centralD s v)+
      angularArea*(∑ i : Fin 3,inner ℝ (spectralGraphWeight (torusRate s) (centralT s i p))
        (spectralGraphWeight (torusRate s) (centralT s i v)))=
      angularArea*(∑ i : Fin 3,slopes i*spectralGraphMean (torusRate s) (centralT s i v))

theorem central_variational_weak_interior (s slopes : Fin 3 → ℝ)
    (hs : ∑ i,slopes i=0) :
    ∃ p : centralEnergySpace s,centralM s p=0 ∧ CentralVariationalEquation s slopes p ∧
      ∀ ψ : centralSmoothFunctions,(∀ (i : Fin 3) x,ψ (centralBoundary i x)=0) →
        inner ℝ (centralD s p) (centralJetD (centralSmoothJet ψ))=0 := by
  obtain ⟨p,hp,hvar,_⟩ := central_unnormalized_variational_exists s slopes hs
  refine ⟨p,hp,hvar,?_⟩
  intro ψ hψ
  have he := hvar (centralSmoothElement s ψ)
  have ht (i : Fin 3) := central_trace_zero s ψ i (hψ i)
  have hd : centralD s (centralSmoothElement s ψ)=centralJetD (centralSmoothJet ψ) := rfl
  rw [hd] at he
  simpa only [ht,map_zero,inner_zero_right,mul_zero,Finset.sum_const_zero,add_zero] using he

end ScalarConductivity

end

end OAI
