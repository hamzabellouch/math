import Mathlib
import OAI.Analysis.Conductivity.Sources.PhysicalC1Pullback
import OAI.Analysis.Conductivity.Geometry.ParametricPotentialCoordinates

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology

variable {P E F : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def spatialFDeriv (f : P×E → F) (q : P×E) : E →L[ℝ] F :=
  fderiv ℝ (fun x => f (q.1,x)) q.2

lemma spatialFDeriv_eq {f : P×E → F} {q : P×E} (hf : DifferentiableAt ℝ f q) :
    spatialFDeriv f q=(fderiv ℝ f q).comp (ContinuousLinearMap.inr ℝ P E) := by
  rcases q with ⟨p,x⟩
  have h := hf.hasFDerivAt.comp x ((hasFDerivAt_const p x).prodMk (hasFDerivAt_id x))
  exact h.fderiv

lemma spatialFDeriv_smoothOn {f : P×E → F} {U : Set (P×E)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ (↑(⊤:ℕ∞)) f U) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (spatialFDeriv f) U := by
  apply hU.contDiffOn_iff.mpr
  intro q hq
  have hd : ContDiffAt ℝ (↑(⊤:ℕ∞)) (fderiv ℝ f) q :=
    (hf.contDiffAt (hU.mem_nhds hq)).fderiv_right (by simp)
  have hc : ContDiffAt ℝ (↑(⊤:ℕ∞))
      (fun z => (fderiv ℝ f z).comp (ContinuousLinearMap.inr ℝ P E)) q :=
    hd.clm_comp contDiffAt_const
  apply hc.congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hq] with z hz
  exact spatialFDeriv_eq ((hf.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))

lemma spatialFDeriv_smooth {f : P×E → F} (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (spatialFDeriv f) := by
  rw [←contDiffOn_univ]
  exact spatialFDeriv_smoothOn isOpen_univ hf.contDiffOn

end ScalarConductivity



namespace ScalarConductivity
open Set Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

lemma inverseSourceWeight_eq_det
    (X : OpenPartialHomeomorph Coord3 Coord3)
    (hX : DifferentiableOn ℝ X X.source) (hXi : DifferentiableOn ℝ X.symm X.target)
    {x : Coord3} (hx : x∈X.source) : inverseSourceWeight X x=|(fderiv ℝ X x).det| := by
  have he := congrArg (fun L : Coord3 →L[ℝ] Coord3 => L.det)
    (local_fderiv_symm_comp X hX hXi hx)
  simp only [ContinuousLinearMap.det,ContinuousLinearMap.toLinearMap_comp,
    ContinuousLinearMap.coe_id,LinearMap.det_comp,LinearMap.det_id] at he
  apply inv_eq_of_mul_eq_one_right
  rw [←abs_mul]
  simpa only [abs_one,ContinuousLinearMap.det] using congrArg abs he

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

omit [FiniteDimensional ℝ P] in
theorem parametric_inverseSourceWeight_smooth
    (Y : OpenPartialHomeomorph (P×Coord3) (P×Coord3))
    (hY : ∀ p x,(Y (p,x)).1=p)
    (hsm : ContDiff ℝ (↑(⊤:ℕ∞)) Y)
    (hinv : ContDiffOn ℝ (↑(⊤:ℕ∞)) Y.symm Y.target) :
    ContDiffOn ℝ (↑(⊤:ℕ∞))
      (fun q : P×Coord3 => inverseSourceWeight (fiberSlice Y hY q.1).symm q.2) Y.target := by
  let f : P×Coord3 → Coord3 := fun q => (Y.symm q).2
  have hf : ContDiffOn ℝ (↑(⊤:ℕ∞)) f Y.target :=
    contDiff_snd.contDiffOn.comp hinv (fun _ _ => mem_univ _)
  have hd := spatialFDeriv_smoothOn Y.open_target hf
  have heq (q : P×Coord3) (hq : q∈Y.target) :
      inverseSourceWeight (fiberSlice Y hY q.1).symm q.2=|(spatialFDeriv f q).det| := by
    obtain ⟨hs,hi⟩ := fiberSlice_smooth Y hY hsm hinv q.1
    exact inverseSourceWeight_eq_det _ (hi.differentiableOn (by simp))
      (hs.differentiable (by simp)).differentiableOn hq
  apply Y.open_target.contDiffOn_iff.mpr
  intro q hq
  have hne : (spatialFDeriv f q).det≠0 := by
    obtain ⟨hs,hi⟩ := fiberSlice_smooth Y hY hsm hinv q.1
    exact local_fderiv_det_ne_zero (fiberSlice Y hY q.1).symm
      (hi.differentiableOn (by simp)) (hs.differentiable (by simp)).differentiableOn hq
  have hc := ((contDiff_clm_det (E := Coord3) (↑(⊤:ℕ∞))).contDiffAt.comp q
    (hd.contDiffAt (Y.open_target.mem_nhds hq))).abs hne
  apply hc.congr_of_eventuallyEq
  filter_upwards [Y.open_target.mem_nhds hq] with z hz
  exact heq z hz

omit [FiniteDimensional ℝ P] in
theorem parametric_chart_compact_bounds
    (Y : OpenPartialHomeomorph (P×Coord3) (P×Coord3))
    (hY : ∀ p x,(Y (p,x)).1=p)
    (hsm : ContDiff ℝ (↑(⊤:ℕ∞)) Y)
    (hinv : ContDiffOn ℝ (↑(⊤:ℕ∞)) Y.symm Y.target)
    {K : Set (P×Coord3)} (hK : IsCompact K) (hKs : K⊆Y.target) :
    ∃ B : ℝ,0<B ∧ ∀ q∈K,
      let X := (fiberSlice Y hY q.1).symm
      |inverseSourceWeight X q.2|≤B ∧
      ‖fderiv ℝ (inverseSourceWeight X) q.2‖≤B ∧
      ‖fderiv ℝ X q.2‖≤B ∧
      9*|(fderiv ℝ X q.2).det|⁻¹*‖operatorMatrix (fderiv ℝ X q.2)‖*
        ‖operatorMatrix (fderiv ℝ X q.2)‖≤B := by
  let f : P×Coord3 → Coord3 := fun q => (Y.symm q).2
  let w : P×Coord3 → ℝ := fun q => inverseSourceWeight (fiberSlice Y hY q.1).symm q.2
  let D := spatialFDeriv f
  let g : P×Coord3 → ℝ := fun q =>
    9*|(D q).det|⁻¹*‖operatorMatrix (D q)‖*‖operatorMatrix (D q)‖
  have hf : ContDiffOn ℝ (↑(⊤:ℕ∞)) f Y.target :=
    contDiff_snd.contDiffOn.comp hinv (fun _ _ => mem_univ _)
  have hD := spatialFDeriv_smoothOn Y.open_target hf
  have hw := parametric_inverseSourceWeight_smooth Y hY hsm hinv
  have hdw := spatialFDeriv_smoothOn Y.open_target hw
  have hg : ContinuousOn g Y.target := by
    intro q hq
    have hd := hD.contDiffAt (Y.open_target.mem_nhds hq)
    have hm := (operatorMatrix_contDiff (m := Fin 3) (n := Fin 3)).contDiffAt.comp q hd
    have hne : (D q).det≠0 := by
      obtain ⟨hs,hi⟩ := fiberSlice_smooth Y hY hsm hinv q.1
      exact local_fderiv_det_ne_zero (fiberSlice Y hY q.1).symm
        (hi.differentiableOn (by simp)) (hs.differentiable (by simp)).differentiableOn hq
    have ht := ((contDiff_clm_det (E := Coord3) (↑(⊤:ℕ∞))).contDiffAt.comp q hd).abs hne
    exact (((continuousAt_const.mul ((ht.inv (abs_ne_zero.mpr hne)).continuousAt)).mul
      hm.continuousAt.norm).mul hm.continuousAt.norm).continuousWithinAt
  obtain ⟨A,hA⟩ := (hK.image_of_continuousOn (hw.continuousOn.mono hKs)).isBounded.exists_norm_le
  obtain ⟨B,hB⟩ := (hK.image_of_continuousOn (hdw.continuousOn.mono hKs)).isBounded.exists_norm_le
  obtain ⟨C,hC⟩ := (hK.image_of_continuousOn (hD.continuousOn.mono hKs)).isBounded.exists_norm_le
  obtain ⟨T,hT⟩ := (hK.image_of_continuousOn (hg.mono hKs)).isBounded.exists_norm_le
  refine ⟨|A|+|B|+|C|+|T|+1,by positivity,fun q hq => ⟨?_,?_,?_,?_⟩⟩
  · exact (hA _ (mem_image_of_mem _ hq)).trans (by linarith [le_abs_self A,abs_nonneg B,abs_nonneg C,abs_nonneg T])
  · exact (hB _ (mem_image_of_mem _ hq)).trans (by linarith [le_abs_self B,abs_nonneg A,abs_nonneg C,abs_nonneg T])
  · exact (hC _ (mem_image_of_mem _ hq)).trans (by linarith [le_abs_self C,abs_nonneg A,abs_nonneg B,abs_nonneg T])
  · exact (le_abs_self _).trans ((hT _ (mem_image_of_mem _ hq)).trans
      (by linarith [le_abs_self T,abs_nonneg A,abs_nonneg B,abs_nonneg C]))

end ScalarConductivity

end

end OAI
