import Mathlib
import OAI.Probability.SKGap.Localization.OperatorQuenched
import OAI.Probability.SKGap.Matrix.FixedNormRecipeEvent

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary MeasureTheory ProbabilityTheory Real Set
variable {n : ℕ}

lemma continuous_matrixLetter (a : Letter (Fin n→ℝ)) :
    Continuous (fun J : Interaction n=>matrixLetter J a) := by
  cases a <;> first | exact continuous_const | exact continuous_id

lemma continuous_matrixWord (w : OrdinaryWord n) :
    Continuous (fun J : Interaction n=>matrixWord J w) := by
  induction w with
  | nil=>simpa only [matrixWord,List.map_nil,List.prod_nil] using
      (continuous_const : Continuous (fun _ : Interaction n=>(1 : Interaction n)))
  | cons a w ih=>
    simpa only [matrixWord,List.map_cons,List.prod_cons] using
      (continuous_matrixLetter a).matrix_mul ih

lemma isClosed_wordSeminormBound (j A C : ℝ) (L : ℕ) :
    IsClosed {J : Interaction n | WordSeminormBound J j A C L} := by
  simp only [WordSeminormBound,ofPred_forall]
  apply isClosed_iInter;intro p
  apply isClosed_iInter;intro w
  apply isClosed_iInter;intro hw
  apply isClosed_iInter;intro hb
  exact isClosed_le ((matrixWordSeminorm_lipschitz p).continuous.comp
    ((continuous_matrixWord w).sub continuous_const)) continuous_const

end SKGapCutoff.Recipe

noncomputable section
open scoped BigOperators Topology
namespace SKGapCutoff.Recipe
open SKGap SKGap.ObservationBridge SKGap.Noncrossing SKGap.Noncrossing.Primary
open MeasureTheory ProbabilityTheory Real Set Filter
local instance (n : ℕ) : MeasurableSpace (Interaction n) := borel _
local instance (n : ℕ) : BorelSpace (Interaction n) := ⟨rfl⟩

lemma disorder_closed_matrix_event (β : ℝ) {n : ℕ} (P : Interaction n→Prop)
    (hP : IsClosed {J | P J}) :
    SKGap.disorderLaw β n {g | ¬P (coupling g)}=
      (Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1))
        {g | ¬P (removeDiagonal (goeMatrix (β^2/n) g))} := by
  have hE : MeasurableSet {g : Disorder n | ¬P (coupling g)} :=
    (hP.preimage SKGap.ObservationBridge.continuous_coupling).measurableSet.compl
  have H:=(measurePreserving_goeEdges (n:=n) (r:=β^2/(n:ℝ)) (by positivity)).measure_preimage hE.nullMeasurableSet
  simpa only [SKGap.gaussianCoordinates,SKGap.disorderLaw,Set.preimage_ofPred_eq,coupling_goeEdges,
    eraseDiagonal,removeDiagonal] using H.symm

lemma disorder_word_event {β A : ℝ} (hβ : 0<β) (hβ1 : β<1) (hA : 1≤A) (L : ℕ) :
    ∃C:ℝ,∃N:ℕ,0<C ∧ 0<N ∧ ∀n,N≤n→
      SKGap.disorderLaw β n {g | ¬WordSeminormBound (coupling g) (β^2) A C L}≤
        ordinaryWordTail (β^2) L n := by
  have hj1 : β^2<1 := by nlinarith
  obtain ⟨C,N,hC,hN,hb⟩:=ordinary_word_event (sq_pos_of_pos hβ) hj1 hA L
  refine ⟨C,N,hC,hN,?_⟩
  intro n hn
  rw [disorder_closed_matrix_event β _ (isClosed_wordSeminormBound _ _ _ _)]
  exact hb n hn

lemma disorder_norm_event {β : ℝ} (hβ : 0<β) {n : ℕ} (hn : 0<n) :
    SKGap.disorderLaw β n {g | physicalNormBound (β^2)<SKGap.opNorm (coupling g)}≤
      recipeNormTail (β^2) n := by
  have hP : IsClosed {J : Interaction n | SKGap.opNorm J≤physicalNormBound (β^2)} :=
    isClosed_le SKGap.RealComplex.continuous_realOpNorm continuous_const
  have H:=disorder_closed_matrix_event β (fun J : Interaction n=>SKGap.opNorm J≤physicalNormBound (β^2)) hP
  simp only [not_le] at H
  rw [H]
  exact zeroDiagGOE_norm_tail (sq_pos_of_pos hβ) hn

theorem disorder_fixed_norm_recipe_probability {β A : ℝ} (hβ : 0<β) (hβ1 : β<1)
    (hA : 1≤A) (M Nmax : ℕ) : ∃B W C : ℝ,0≤B ∧ 0≤W ∧ 0<C ∧
      Tendsto (fun n=>SKGap.disorderLaw β n
        {g | ¬RecipeMatrixEvent (β^2) (physicalNormBound (β^2)) A B W C M Nmax
          (coupling g)}) atTop (𝓝 0) := by
  let j:=β^2
  have hj : 0<j:=sq_pos_of_pos hβ
  let R:=max A (physicalNormBound j)
  have hAR : A≤R:=le_max_left _ _
  have hR : 1≤R:=hA.trans hAR
  obtain ⟨C,N,hC,hN,hword⟩:=disorder_word_event hβ hβ1 hA (2*M+2*Nmax+3)
  refine ⟨primaryEventBudget j R C M,R^(2*Nmax+3)+C,C,
    primaryEventBudget_nonneg (by linarith) hC.le M,
    add_nonneg (pow_nonneg (by linarith) _) hC.le,hC,?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (show Tendsto (fun n=>recipeNormTail j n+ordinaryWordTail j (2*M+2*Nmax+3) n) atTop (𝓝 0) from
      by simpa using (recipeNormTail_limit hj).add (ordinaryWordTail_limit hj _))
    (Filter.Eventually.of_forall (fun _=>bot_le))
  filter_upwards [eventually_ge_atTop N] with n hn
  have hn0 : 0<n:=hN.trans_le hn
  let E:Set (Disorder n):={g | physicalNormBound j<SKGap.opNorm (coupling g)}
  let F:Set (Disorder n):={g | ¬WordSeminormBound (coupling g) j A C (2*M+2*Nmax+3)}
  have hE : SKGap.disorderLaw β n E≤recipeNormTail j n:=disorder_norm_event hβ hn0
  have hF : SKGap.disorderLaw β n F≤ordinaryWordTail j (2*M+2*Nmax+3) n:=hword n hn
  apply (measure_mono (t:=E∪F) ?_).trans ((measure_union_le _ _).trans (add_le_add hE hF))
  intro g hg
  by_contra hh
  have hp : SKGap.opNorm (coupling g)≤physicalNormBound j:=le_of_not_gt (fun hbad=>hh (.inl hbad))
  have hw : WordSeminormBound (coupling g) j A C (2*M+2*Nmax+3):=by
    by_contra hbad;exact hh (.inr hbad)
  have hev:=wordEvent_recipeEvent (coupling g) hn0 hR hA hAR hC.le
    (hp.trans (le_max_right _ _)) M Nmax hw
  exact hg ⟨hp,hev.2⟩

end SKGapCutoff.Recipe

end
end
end

end OAI
