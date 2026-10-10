import Mathlib
import OAI.Probability.SKGap.Gaussian.GaussianRecipeEvent
import OAI.Probability.SKGap.Matrix.StartedWordClosure

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
namespace SKGapCutoff.Recipe
open Primary Matrix SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary MeasureTheory ProbabilityTheory Real Set Filter
variable {n : ℕ}

def StartedMatrixEvent (j R A₀ A c B W C : ℝ) (M Nmax : ℕ) (J : Interaction n) : Prop :=
  SKGap.opNorm J≤R ∧ (∀h x l,l<M→ShapeBound (Primary.formalField j J h x l) B) ∧
  ∀a:Fin n→ℝ,(∀i,a i∈Icc 0 A₀)→
    c≤ComplexSpectral.lowerRayleigh (RealComplex.liftMatrix (stabilityMatrix a 1 ((j/n)*∑i,a i) J))→
    ClosedWordTestBound j a J A W (2*Nmax+5) ∧
    ClosedWordDiagramBound j a J A C (2*M+2*Nmax+4)

lemma ClosedWordTestBound.mono {j A W : ℝ} {a : Fin n→ℝ} {J : Interaction n} {L K : ℕ}
    (h : ClosedWordTestBound j a J A W L) (hK : K≤L) : ClosedWordTestBound j a J A W K :=
  fun w hw hi hb=>h w (hw.trans hK) hi hb
lemma ClosedWordDiagramBound.mono {j A C : ℝ} {a : Fin n→ℝ} {J : Interaction n} {L K : ℕ}
    (h : ClosedWordDiagramBound j a J A C L) (hK : K≤L) : ClosedWordDiagramBound j a J A C K :=
  fun w hw hi hb=>h w (hw.trans hK) hi hb

theorem gaussian_started_matrix_event {j A₀ A c : ℝ} (hj : 0<j) (hj1 : j<1)
    (hA₀ : 0<A₀) (hs : sqrt j*A₀<1) (hAA : A₀≤A) (hA : 1≤A) (hc : 0<c)
    (M Nmax : ℕ) : ∃R B W C : ℝ,1≤R ∧ 0≤B ∧ 0≤W ∧ 0<C ∧
      Tendsto (fun n=>(Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1))
        {g | ¬StartedMatrixEvent j R A₀ A c B W C M Nmax
          (removeDiagonal (goeMatrix (j/n) g))}) atTop (𝓝 0) := by
  let R:=max A (2*sqrt j+1+1)
  have hAR : A≤R:=le_max_left _ _
  have hR : 1≤R:=hA.trans hAR
  obtain ⟨C,N,hC,hN,hclosed⟩:=closed_word_event hj hA₀ hs hA hAA hc (2*M+2*Nmax+5)
  obtain ⟨B,N',hB,hN',hordinary⟩:=ordinary_word_event hj hj1 hA (2*M+2*Nmax+5)
  obtain ⟨W,hW,htest⟩:=closed_word_test_budget hj.le hA₀.le
    (by linarith : 0≤A) hc (by linarith : 0≤R) (2*M+2*Nmax+5)
  refine ⟨R,primaryEventBudget j R B M,W+C,C,hR,
    primaryEventBudget_nonneg (by linarith) hB.le _,by positivity,hC,?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (show Tendsto (fun n=>recipeNormTail j n+ordinaryWordTail j (2*M+2*Nmax+5) n+
      ordinaryWordTail j (2*M+2*Nmax+5) n) atTop (𝓝 0) from by
      simpa using ((recipeNormTail_limit hj).add (ordinaryWordTail_limit hj _)).add (ordinaryWordTail_limit hj _))
    (Filter.Eventually.of_forall (fun _=>bot_le))
  filter_upwards [eventually_ge_atTop (max N N')] with n hn
  have hnN : N≤n:=(le_max_left ..).trans hn
  have hnN' : N'≤n:=(le_max_right ..).trans hn
  have hn0 : 0<n:=hN.trans_le hnN
  let μ:=Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1)
  let V : Set (MatrixCoordinates (Fin n)→ℝ):={g | 2*sqrt j+1+1<SKGap.opNorm (removeDiagonal (goeMatrix (j/n) g))}
  let U : Set (MatrixCoordinates (Fin n)→ℝ):={g | ¬WordSeminormBound (removeDiagonal (goeMatrix (j/n) g)) j A B (2*M+2*Nmax+5)}
  let F : Set (MatrixCoordinates (Fin n)→ℝ):={g | ¬ClosedWordEvent j A₀ A c C (2*M+2*Nmax+5) (removeDiagonal (goeMatrix (j/n) g))}
  have hV : μ V≤recipeNormTail j n:=zeroDiagGOE_norm_tail hj hn0
  have hU : μ U≤ordinaryWordTail j (2*M+2*Nmax+5) n:=hordinary n hnN'
  have hF : μ F≤ordinaryWordTail j (2*M+2*Nmax+5) n:=hclosed n hnN
  apply (measure_mono (t:=(V∪U)∪F) ?_).trans ((measure_union_le _ _).trans
    (add_le_add ((measure_union_le _ _).trans (add_le_add hV hU)) hF))
  intro g hg
  by_contra hh
  have hJ : SKGap.opNorm (removeDiagonal (goeMatrix (j/n) g))≤R:=
    (le_of_not_gt (fun hbad=>hh (.inl (.inl hbad)))).trans (le_max_right _ _)
  have hu : WordSeminormBound (removeDiagonal (goeMatrix (j/n) g)) j A B (2*M+2*Nmax+5):=by
    by_contra hbad; exact hh (.inl (.inr hbad))
  have hf : ClosedWordEvent j A₀ A c C (2*M+2*Nmax+5) (removeDiagonal (goeMatrix (j/n) g)):=by
    by_contra hbad; exact hh (.inr hbad)
  apply hg
  refine ⟨hJ,fun h x l hl=>wordEvent_formal _ hn0 (by linarith) hB.le hA hJ M _ (by omega) hu h x l hl,?_⟩
  intro a ha hstable
  have hb:=hf a ha hstable
  have hsym : (removeDiagonal (goeMatrix (j/n) g))ᵀ=removeDiagonal (goeMatrix (j/n) g) := by
    simp only [removeDiagonal,transpose_sub,diagonal_transpose,goeMatrix_transpose]
  exact ⟨(htest n hn0 a _ C ha hsym hJ hstable hb).mono (by omega),hb.diagram.mono (by omega)⟩

end SKGapCutoff.Recipe

end
end

end OAI
