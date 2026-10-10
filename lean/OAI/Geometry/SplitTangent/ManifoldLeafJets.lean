import Mathlib
import OAI.Geometry.SplitTangent.TensorVanishing
import OAI.Geometry.SplitTangent.Basic

namespace OAI

/-! Manifold Leaf Jets. -/

noncomputable section
open Set Filter Topology Bundle
open scoped Manifold ContDiff
universe u
namespace SplitTangent.AlignedProductChart
variable {X : ComplexManifold.{u}} {S : TangentSplitting X}
  {A B C D : Type*}
  [NormedAddCommGroup A] [NormedSpace ℂ A]
  [NormedAddCommGroup B] [NormedSpace ℂ B]
  [NormedAddCommGroup C] [NormedSpace ℂ C]
  [NormedAddCommGroup D] [NormedSpace ℂ D]

 
def jet (P : AlignedProductChart S A B) (f : X.Carrier → ℂ)
    (y : X.Carrier) (m : ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin m => Tangent X y) ℂ :=
  (HorizontalJet.value (f ∘ P.chart.symm) (P.chart y) m).compContinuousLinearMap
    (fun _ => mfderiv (ModelWithCorners X) 𝓘(ℂ,A × B) P.chart y)

lemma jet_eq_zero_iff [CompleteSpace A] [CompleteSpace B]
    (P : AlignedProductChart S A B) (f : X.Carrier → ℂ)
    {y : X.Carrier} (hy : y∈P.chart.source) (m : ℕ) :
    P.jet f y m=0 ↔ HorizontalJet.value (f ∘ P.chart.symm) (P.chart y) m=0 := by
  constructor
  · intro h
    ext w
    choose v hv using fun i => P.mdifferentiable.mfderiv_surjective hy (w i)
    have he := congrArg (fun K => K v) h
    change HorizontalJet.value (f ∘ P.chart.symm) (P.chart y) m
      (fun i => mfderiv (ModelWithCorners X) 𝓘(ℂ,A × B) P.chart y (v i))=0 at he
    have hw : (fun i => mfderiv (ModelWithCorners X) 𝓘(ℂ,A × B) P.chart y (v i))=w := funext hv
    rwa [hw] at he
  · intro h
    ext v
    simp only [jet,h]
    rfl

lemma coordinate_function_analytic [CompleteSpace A] [CompleteSpace B]
    (P : AlignedProductChart S A B)
    {f : X.Carrier → ℂ} {y : X.Carrier} (hy : y∈P.chart.source)
    (hf : ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,ℂ) ω f y) :
    AnalyticAt ℂ (f ∘ P.chart.symm) (P.chart y) := by
  have hf' : ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,ℂ) ω f
      (P.chart.symm (P.chart y)) := by simpa only [P.chart.left_inv hy] using hf
  exact (hf'.comp _ (P.inverse_holomorphicAt (P.chart.map_source hy))).contDiffAt.analyticAt

lemma transition_derivative [CompleteSpace A] [CompleteSpace B]
    [CompleteSpace C] [CompleteSpace D] (P : AlignedProductChart S A B)
    (Q : AlignedProductChart S C D) {y : X.Carrier}
    (hy : y∈P.chart.source) (hq : y∈Q.chart.source) :
    (fderiv ℂ (Q.chart ∘ P.chart.symm) (P.chart y)).comp
      (mfderiv (ModelWithCorners X) 𝓘(ℂ,A × B) P.chart y) =
        mfderiv (ModelWithCorners X) 𝓘(ℂ,C × D) Q.chart y := by
  have hq' : P.chart.symm (P.chart y)∈Q.chart.source := by simpa only [P.chart.left_inv hy] using hq
  have ht := (Q.holomorphicAt hq').comp _ (P.inverse_holomorphicAt (P.chart.map_source hy))
  have hc := mfderiv_comp y (ht.mdifferentiableAt (by simp))
    ((P.holomorphicAt hy).mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at hc
  have he : ((Q.chart ∘ P.chart.symm) ∘ P.chart) =ᶠ[𝓝 y] Q.chart := by
    filter_upwards [P.chart.open_source.mem_nhds hy] with z hz
    exact congrArg Q.chart (P.chart.left_inv hz)
  exact hc.symm.trans he.mfderiv_eq

 

theorem jet_independent [CompleteSpace A] [CompleteSpace B]
    [CompleteSpace C] [CompleteSpace D] (P : AlignedProductChart S A B)
    (Q : AlignedProductChart S C D) {f : X.Carrier → ℂ} {y : X.Carrier}
    (hy : y∈P.chart.source) (hq : y∈Q.chart.source)
    (hf : ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,ℂ) ω f y)
    (m : ℕ) (hz : ∀n,n < m → Q.jet f y n=0) :
    P.jet f y m=Q.jet f y m := by
  let T : A × B → C × D := Q.chart ∘ P.chart.symm
  have hq' : P.chart.symm (P.chart y)∈Q.chart.source := by simpa only [P.chart.left_inv hy] using hq
  have hT : AnalyticAt ℂ T (P.chart y) :=
    ((Q.holomorphicAt hq').comp _ (P.inverse_holomorphicAt (P.chart.map_source hy))).contDiffAt.analyticAt
  have hx : T (P.chart y)=Q.chart y := congrArg Q.chart (P.chart.left_inv hy)
  have hfc : AnalyticAt ℂ (f ∘ Q.chart.symm) (T (P.chart y)) :=
    hx.symm ▸ Q.coordinate_function_analytic hq hf
  have hzero (n : ℕ) (hn : n < m) :
      HorizontalJet.value (f ∘ Q.chart.symm) (T (P.chart y)) n=0 :=
    hx.symm ▸ (Q.jet_eq_zero_iff f hq n).mp (hz n hn)
  have hcomp := HorizontalJet.value_comp hfc hT
    (P.transition_axes Q (P.chart.map_source hy) hq') m hzero
  have he : (f ∘ P.chart.symm) =ᶠ[𝓝 (P.chart y)] ((f ∘ Q.chart.symm) ∘ T) := by
    filter_upwards [(P.inverse_holomorphicAt (P.chart.map_source hy)).continuousAt.preimage_mem_nhds
      (Q.chart.open_source.mem_nhds hq')] with z hz
    exact congrArg f (Q.chart.left_inv hz).symm
  have hval := (HorizontalJet.value_congr he m).trans hcomp
  have hd := P.transition_derivative Q hy hq
  ext v
  change HorizontalJet.value (f ∘ P.chart.symm) (P.chart y) m
    (fun i => mfderiv (ModelWithCorners X) 𝓘(ℂ,A × B) P.chart y (v i)) = _
  rw [hval]
  change HorizontalJet.value (f ∘ Q.chart.symm) (T (P.chart y)) m
    (fun i => ((fderiv ℂ T (P.chart y)).comp
      (mfderiv (ModelWithCorners X) 𝓘(ℂ,A × B) P.chart y)) (v i)) = _
  rw [hx,hd]
  rfl

 

theorem jet_smul [CompleteSpace A] [CompleteSpace B] (P : AlignedProductChart S A B)
    {f v : X.Carrier → ℂ} {y : X.Carrier} (hy : y∈P.chart.source)
    (hf : ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,ℂ) ω f y)
    (hv : ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,ℂ) ω v y)
    (m : ℕ) (hz : ∀n,n < m → P.jet f y n=0) :
    P.jet (fun z => v z*f z) y m=v y • P.jet f y m := by
  have he := HorizontalJet.value_smul (P.coordinate_function_analytic hy hf)
    (P.coordinate_function_analytic hy hv) m
    (fun n hn => (P.jet_eq_zero_iff f hy n).mp (hz n hn))
  ext w
  change HorizontalJet.value (fun z => (v ∘ P.chart.symm) z • (f ∘ P.chart.symm) z)
    (P.chart y) m _ = _
  rw [he]
  simp only [smul_apply,Function.comp_apply,P.chart.left_inv hy]
  rfl

 

lemma jet_supported [CompleteSpace A] [CompleteSpace B]
    (P : AlignedProductChart S A B) (f : X.Carrier → ℂ)
    {y : X.Carrier} (hy : y∈P.chart.source) (m : ℕ)
    (v : Fin m → Tangent X y) :
    P.jet f y m (fun i => S.projector y (v i))=P.jet f y m v := by
  have he (w : Tangent X y) :
      (mfderiv (ModelWithCorners X) 𝓘(ℂ,A × B) P.chart y (S.projector y w)).1=
        (mfderiv (ModelWithCorners X) 𝓘(ℂ,A × B) P.chart y w).1 := by
    have hk : w-S.projector y w∈S.second y := by
      change S.projector y (w-S.projector y w)=0
      rw [map_sub,S.idempotent,sub_self]
    have hm := Submodule.mem_map_of_mem (f :=
      (mfderiv (ModelWithCorners X) 𝓘(ℂ,A × B) P.chart y).toLinearMap) hk
    rw [P.second y hy] at hm
    change (mfderiv (ModelWithCorners X) 𝓘(ℂ,A × B) P.chart y (w-S.projector y w)).1=0 at hm
    erw [map_sub,Prod.fst_sub,sub_eq_zero] at hm
    exact hm.symm
  change iteratedFDeriv ℂ m (fun a => (f ∘ P.chart.symm) (a,(P.chart y).2)) (P.chart y).1
    (fun i => (mfderiv (ModelWithCorners X) 𝓘(ℂ,A × B) P.chart y (S.projector y (v i))).1)=_
  simp only [he]
  rfl

lemma jet_symmetric [CompleteSpace A] [CompleteSpace B] (P : AlignedProductChart S A B)
    {f : X.Carrier → ℂ} {y : X.Carrier} (hy : y∈P.chart.source)
    (hf : ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,ℂ) ω f y)
    (m : ℕ) (v : Fin m → Tangent X y) (σ : Equiv.Perm (Fin m)) :
    P.jet f y m (v ∘ σ)=P.jet f y m v := by
  exact (HorizontalJet.slice_analytic (P.coordinate_function_analytic hy hf)).contDiffAt.iteratedFDeriv_comp_perm
    (fun i => (mfderiv (ModelWithCorners X) 𝓘(ℂ,A × B) P.chart y (v i)).1) σ

lemma jet_congr [CompleteSpace A] [CompleteSpace B]
    (P : AlignedProductChart S A B) {f h : X.Carrier → ℂ}
    {y : X.Carrier} (hy : y∈P.chart.source) (he : f=ᶠ[𝓝 y] h) (m : ℕ) :
    P.jet f y m=P.jet h y m := by
  have hi : Tendsto P.chart.symm (𝓝 (P.chart y)) (𝓝 y) := by
    simpa only [P.chart.left_inv hy] using
      (P.inverse_holomorphicAt (P.chart.map_source hy)).continuousAt.tendsto
  have hc' := he.comp_tendsto hi
  unfold jet
  rw [HorizontalJet.value_congr hc' m]

lemma jet_add [CompleteSpace A] [CompleteSpace B]
    (P : AlignedProductChart S A B) {f h : X.Carrier → ℂ}
    {y : X.Carrier} (hy : y∈P.chart.source)
    (hf : ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,ℂ) ω f y)
    (hh : ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,ℂ) ω h y) (m : ℕ) :
    P.jet (f+h) y m=P.jet f y m+P.jet h y m := by
  have hf' := (HorizontalJet.slice_analytic (P.coordinate_function_analytic hy hf)).contDiffAt (n := m)
  have hh' := (HorizontalJet.slice_analytic (P.coordinate_function_analytic hy hh)).contDiffAt (n := m)
  ext v
  exact congrArg (fun K => K (fun i =>
    (mfderiv (ModelWithCorners X) 𝓘(ℂ,A × B) P.chart y (v i)).1))
      (iteratedFDeriv_add_apply hf' hh')

lemma jet_csmul [CompleteSpace A] [CompleteSpace B]
    (P : AlignedProductChart S A B) {f : X.Carrier → ℂ}
    {y : X.Carrier} (hy : y∈P.chart.source)
    (hf : ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,ℂ) ω f y) (m : ℕ) (c : ℂ) :
    P.jet (c • f) y m=c • P.jet f y m := by
  ext v
  have hf' := (HorizontalJet.slice_analytic (P.coordinate_function_analytic hy hf)).contDiffAt (n := m)
  exact congrArg (fun K => K (fun i =>
    (mfderiv (ModelWithCorners X) 𝓘(ℂ,A × B) P.chart y (v i)).1))
      (iteratedFDeriv_const_smul_apply (a := c) hf')

@[simp] lemma jet_zero [CompleteSpace A] [CompleteSpace B]
    (P : AlignedProductChart S A B) (y : X.Carrier) (m : ℕ) :
    P.jet 0 y m=0 := by
  ext v
  simp [jet,HorizontalJet.value]
  rfl

end SplitTangent.AlignedProductChart

end

end OAI
