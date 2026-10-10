import Mathlib
import OAI.Probability.SKGap.Matrix.StartedMatrixEvent
import OAI.Probability.SKGap.Localization.DisorderRecipeEvent

namespace OAI

section

noncomputable section
open scoped BigOperators Topology Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary Matrix MeasureTheory ProbabilityTheory Real Set Filter
variable {n : ℕ}

def inverseDenominator (j : ℝ) (a : Fin n→ℝ) (J : Interaction n) : Interaction n :=
  1-Matrix.diagonal a*(J-((j/n)*∑i,a i) • 1)

lemma continuous_inverseDenominator (j : ℝ) (a : Fin n→ℝ) :
    Continuous (inverseDenominator j a) := by
  unfold inverseDenominator
  exact continuous_const.sub (continuous_const.matrix_mul (continuous_id.sub continuous_const))

lemma continuousAt_exactWord (j : ℝ) (a : Fin n→ℝ) (w : List (WordLetter (Fin n)))
    (J : Interaction n) (hJ : (inverseDenominator j a J).det≠0) :
    ContinuousAt (fun M=>exactWord j a w M) J := by
  have hletter (l : WordLetter (Fin n)) : ContinuousAt (l.exactEval j a) J := by
    cases l with
    | diag d=>exact continuousAt_const
    | noise=>exact continuousAt_id
    | inverse=>
      have h : ContinuousAt Inv.inv (inverseDenominator j a J) := by
        apply continuousAt_matrix_inv
        simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hJ
      have he : WordLetter.exactEval j a WordLetter.inverse=(fun M=>(inverseDenominator j a M)⁻¹) := by
        funext M
        simp only [WordLetter.exactEval,inverseDenominator,Fintype.card_fin]
      rw [he]
      exact h.comp (continuous_inverseDenominator j a).continuousAt
  induction w with
  | nil=>exact continuousAt_const
  | cons l w ih=>
    change ContinuousAt (fun M=>l.exactEval j a M*exactWord j a w M) J
    exact (continuous_fst.matrix_mul continuous_snd).continuousAt.comp ((hletter l).prodMk ih)

lemma continuous_stability_lower (j : ℝ) (a : Fin n→ℝ) :
    Continuous (fun J : Interaction n=>ComplexSpectral.lowerRayleigh
      (RealComplex.liftMatrix (stabilityMatrix a 1 ((j/n)*∑i,a i) J))) := by
  apply ComplexSpectral.continuous_lowerRayleigh.comp
  unfold RealComplex.liftMatrix stabilityMatrix Matrix.map
  fun_prop

def BufferedClosedWordEvent (j A D c C : ℝ) (L : ℕ) (J : Interaction n) : Prop :=
  ∀a:Fin n→ℝ,(∀i,a i∈Icc 0 A)→
    c<ComplexSpectral.lowerRayleigh (RealComplex.liftMatrix (stabilityMatrix a 1 ((j/n)*∑i,a i) J))→
    (inverseDenominator j a J).det≠0→ClosedWordSeminormBound j a J D C L

lemma isClosed_bufferedClosedWordEvent (j A D c C : ℝ) (L : ℕ) :
    IsClosed {J : Interaction n | BufferedClosedWordEvent j A D c C L J} := by
  rw [←isOpen_compl_iff]
  apply isOpen_iff_mem_nhds.mpr
  intro J hJ
  change ¬BufferedClosedWordEvent j A D c C L J at hJ
  simp only [BufferedClosedWordEvent,ClosedWordSeminormBound,not_forall,not_le] at hJ
  obtain ⟨a,ha,hmargin,hdet,p,w,hw,hi,hb,hfail⟩:=hJ
  have hm := (continuous_stability_lower j a).continuousAt.eventually (lt_mem_nhds hmargin)
  have hd := ((continuous_inverseDenominator j a).matrix_det).continuousAt.eventually
    (isOpen_ne.mem_nhds hdet)
  have hf := ((matrixWordSeminorm_lipschitz p).continuous.continuousAt.comp
    ((continuousAt_exactWord j a w J hdet).sub continuousAt_const)).eventually (lt_mem_nhds hfail)
  filter_upwards [hm,hd,hf] with M hm hd hf
  change ¬BufferedClosedWordEvent j A D c C L M
  intro H
  exact (not_le_of_gt hf) (H a ha hm hd p w hw hi hb)

lemma ClosedWordEvent.buffered {j A D c C : ℝ} {L : ℕ} {J : Interaction n}
    (h : ClosedWordEvent j A D c C L J) : BufferedClosedWordEvent j A D c C L J := by
  intro a ha hm _
  exact h a ha hm.le

theorem disorder_buffered_closed_word_event {β A D c : ℝ} (hβ : 0<β) (hA : 0<A)
    (hs : sqrt (β^2)*A<1) (hD : 1≤D) (hAD : A≤D) (hc : 0<c) (L : ℕ) :
    ∃C:ℝ,∃N:ℕ,0<C ∧ 0<N ∧ ∀n,N≤n→
      SKGap.disorderLaw β n {g | ¬BufferedClosedWordEvent (β^2) A D c C L (coupling g)}≤
        ordinaryWordTail (β^2) L n := by
  obtain ⟨C,N,hC,hN,h⟩:=closed_word_event (sq_pos_of_pos hβ) hA hs hD hAD hc L
  refine ⟨C,N,hC,hN,fun n hn=>?_⟩
  rw [disorder_closed_matrix_event β _ (isClosed_bufferedClosedWordEvent _ _ _ _ _ _)]
  apply (measure_mono ?_).trans (h n hn)
  intro g hg H
  exact hg H.buffered

lemma inverseDenominator_det_ne (hn : 0<n) (j : ℝ) (a : Fin n→ℝ)
    (ha : ∀i,0≤a i) (J : Interaction n) (hJ : Jᵀ=J) {c : ℝ} (hc : 0<c)
    (hm : c≤ComplexSpectral.lowerRayleigh (RealComplex.liftMatrix
      (stabilityMatrix a 1 ((j/n)*∑i,a i) J))) :
    (inverseDenominator j a J).det≠0 := by
  have : Nonempty (Fin n):=Fin.pos_iff_nonempty.mp hn
  let D:=pathDiagonal a 1
  let q:=(j/n)*∑i,a i
  have hrep : stabilityMatrix a 1 q J=1-D*(J-q • 1)*D := by
    rw [stabilityMatrix_path_rep a ha (by norm_num),pathShift_one]
  have hsym : (1-D*(J-q • 1)*D)ᵀ=1-D*(J-q • 1)*D := by
    simp only [transpose_sub,transpose_one,transpose_mul,hJ,D,pathDiagonal,
      diagonal_transpose,transpose_smul,mul_assoc]
  have hu : IsUnit (1-D*(J-q • 1)*D) := by
    apply symmetric_isUnit_of_lower _ hsym hc
    rw [←hrep]
    exact hm
  have hu' := ResolventIdentity.inverse_one_sub_square_mul_unit D (J-q • 1) hu
  have he : D*D=Matrix.diagonal a:=pathDiagonal_square ha
  rw [he] at hu'
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hu')

lemma BufferedClosedWordEvent.unbuffer {j A D c C : ℝ} {L : ℕ} {J : Interaction n}
    (hn : 0<n) (hJ : Jᵀ=J) (hc : 0<c)
    (h : BufferedClosedWordEvent j A D (c/2) C L J) : ClosedWordEvent j A D c C L J := by
  intro a ha hm
  exact h a ha (by linarith)
    (inverseDenominator_det_ne hn j a (fun i=>(ha i).1) J hJ hc hm)

theorem disorder_closed_word_event {β A D c : ℝ} (hβ : 0<β) (hA : 0<A)
    (hs : sqrt (β^2)*A<1) (hD : 1≤D) (hAD : A≤D) (hc : 0<c) (L : ℕ) :
    ∃C:ℝ,∃N:ℕ,0<C ∧ 0<N ∧ ∀n,N≤n→
      SKGap.disorderLaw β n {g | ¬ClosedWordEvent (β^2) A D c C L (coupling g)}≤
        ordinaryWordTail (β^2) L n := by
  obtain ⟨C,N,hC,hN,h⟩:=disorder_buffered_closed_word_event hβ hA hs hD hAD (half_pos hc) L
  refine ⟨C,N,hC,hN,fun n hn=>?_⟩
  apply (measure_mono ?_).trans (h n hn)
  intro g hg H
  exact hg (H.unbuffer (hN.trans_le hn) (by ext i k; exact coupling_symm g k i) hc)

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators Topology
namespace SKGapCutoff.Recipe
open Primary Matrix SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary MeasureTheory ProbabilityTheory Real Set Filter

theorem disorder_started_matrix_event {β A₀ A c : ℝ} (hβ : 0<β) (hβ1 : β<1)
    (hA₀ : 0<A₀) (hs : sqrt (β^2)*A₀<1) (hAA : A₀≤A) (hA : 1≤A) (hc : 0<c)
    (M Nmax : ℕ) : ∃B W C : ℝ,0≤B ∧ 0≤W ∧ 0<C ∧
      Tendsto (fun n=>SKGap.disorderLaw β n
        {g | ¬StartedMatrixEvent (β^2) (physicalNormBound (β^2)) A₀ A c B W C M Nmax
          (coupling g)}) atTop (𝓝 0) := by
  let j:=β^2
  have hj : 0<j:=sq_pos_of_pos hβ
  let R:=max A (physicalNormBound j)
  have hAR : A≤R:=le_max_left _ _
  have hR : 1≤R:=hA.trans hAR
  obtain ⟨C,N,hC,hN,hclosed⟩:=disorder_closed_word_event hβ hA₀ hs hA hAA hc (2*M+2*Nmax+5)
  obtain ⟨B,N',hB,hN',hordinary⟩:=disorder_word_event hβ hβ1 hA (2*M+2*Nmax+5)
  obtain ⟨W,hW,htest⟩:=closed_word_test_budget hj.le hA₀.le
    (by linarith : 0≤A) hc (by unfold physicalNormBound; positivity : 0≤physicalNormBound j) (2*M+2*Nmax+5)
  refine ⟨primaryEventBudget j R B M,W+C,C,
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
  let μ:=SKGap.disorderLaw β n
  let V : Set (Disorder n):={g | physicalNormBound j<SKGap.opNorm (coupling g)}
  let U : Set (Disorder n):={g | ¬WordSeminormBound (coupling g) j A B (2*M+2*Nmax+5)}
  let F : Set (Disorder n):={g | ¬ClosedWordEvent j A₀ A c C (2*M+2*Nmax+5) (coupling g)}
  have hV : μ V≤recipeNormTail j n:=disorder_norm_event hβ hn0
  have hU : μ U≤ordinaryWordTail j (2*M+2*Nmax+5) n:=hordinary n hnN'
  have hF : μ F≤ordinaryWordTail j (2*M+2*Nmax+5) n:=hclosed n hnN
  apply (measure_mono (t:=(V∪U)∪F) ?_).trans ((measure_union_le _ _).trans
    (add_le_add ((measure_union_le _ _).trans (add_le_add hV hU)) hF))
  intro g hg
  by_contra hh
  have hJ : SKGap.opNorm (coupling g)≤physicalNormBound j:=
    le_of_not_gt (fun hbad=>hh (.inl (.inl hbad)))
  have hu : WordSeminormBound (coupling g) j A B (2*M+2*Nmax+5):=by
    by_contra hbad; exact hh (.inl (.inr hbad))
  have hf : ClosedWordEvent j A₀ A c C (2*M+2*Nmax+5) (coupling g):=by
    by_contra hbad; exact hh (.inr hbad)
  apply hg
  refine ⟨hJ,fun h x l hl=>wordEvent_formal _ hn0 (by linarith) hB.le hA (hJ.trans (le_max_right _ _)) M _ (by omega) hu h x l hl,?_⟩
  intro a ha hstable
  have hb:=hf a ha hstable
  have hsym : (coupling g)ᵀ=coupling g := by
    ext i k;exact coupling_symm g k i
  exact ⟨(htest n hn0 a _ C ha hsym hJ hstable hb).mono (by omega),hb.diagram.mono (by omega)⟩

end SKGapCutoff.Recipe

end
end

end OAI
