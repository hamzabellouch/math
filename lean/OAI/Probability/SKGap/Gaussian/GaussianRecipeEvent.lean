import Mathlib
import OAI.Probability.SKGap.Matrix.PrimaryWordEventBinding

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary MeasureTheory ProbabilityTheory Real Set

def ordinaryWordTail (j : ℝ) (L n : ℕ) : ENNReal :=
  2*((wordPatternSet L L).card*ENNReal.ofReal (3*exp (-(n:ℝ)))+
    ENNReal.ofReal (exp (-2*(n:ℝ)/(π^2*(sqrt (2*j))^2)))+
      (ENNReal.ofReal (2*exp (-(n:ℝ)/(π^2*j)))+
        ENNReal.ofReal (2*(n:ℝ)*exp (-1/(8*(j/n))))))
def recipeNormTail (j : ℝ) (n : ℕ) : ENNReal :=
  ENNReal.ofReal (2*exp (-(n:ℝ)/(π^2*j)))+
    ENNReal.ofReal (2*(n:ℝ)*exp (-1/(8*(j/n))))

theorem gaussian_recipe_event {j A : ℝ} (hj : 0<j) (hj1 : j<1) (hA : 1≤A)
    (M Nmax : ℕ) : ∃R B W C : ℝ, ∃N : ℕ,
      1≤R ∧ 0≤B ∧ 0≤W ∧ 0<C ∧ 0<N ∧ ∀n,N≤n→
      (Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1))
        {g | ¬RecipeMatrixEvent j R A B W C M Nmax
          (removeDiagonal (goeMatrix (j/n) g))}≤
      recipeNormTail j n+ordinaryWordTail j (2*M+2*Nmax+3) n := by
  let R:=max A (2*sqrt j+1+1)
  have hAR : A≤R:=le_max_left _ _
  have hR : 1≤R:=hA.trans hAR
  obtain ⟨C,N,hC,hN,hword⟩:=ordinary_word_event hj hj1 hA (2*M+2*Nmax+3)
  refine ⟨R,primaryEventBudget j R C M,R^(2*Nmax+3)+C,C,N,hR,
    primaryEventBudget_nonneg (by linarith) hC.le M,
    add_nonneg (pow_nonneg (by linarith) _) hC.le,hC,hN,?_⟩
  intro n hn
  have hn0 : 0<n:=lt_of_lt_of_le hN hn
  let μ:=Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1)
  let E : Set (MatrixCoordinates (Fin n)→ℝ):=
    {g | 2*sqrt j+1+1<SKGap.opNorm (removeDiagonal (goeMatrix (j/n) g))}
  let F : Set (MatrixCoordinates (Fin n)→ℝ):=
    {g | ¬WordSeminormBound (removeDiagonal (goeMatrix (j/n) g)) j A C (2*M+2*Nmax+3)}
  have hE : μ E≤recipeNormTail j n:=zeroDiagGOE_norm_tail hj hn0
  have hF : μ F≤ordinaryWordTail j (2*M+2*Nmax+3) n:=hword n hn
  apply (measure_mono (t:=E∪F) ?_).trans ((measure_union_le _ _).trans (add_le_add hE hF))
  intro g hg
  by_contra hh
  have hJ : SKGap.opNorm (removeDiagonal (goeMatrix (j/n) g))≤R := by
    apply le_trans (le_of_not_gt (fun hbad=>hh (.inl hbad))) (le_max_right _ _)
  have hw : WordSeminormBound (removeDiagonal (goeMatrix (j/n) g)) j A C (2*M+2*Nmax+3):=by
    by_contra hbad; exact hh (.inr hbad)
  exact hg (wordEvent_recipeEvent _ hn0 hR hA hAR hC.le hJ M Nmax hw)

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory Real
namespace SKGapCutoff.Recipe
open SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary

lemma exp_rate_limit {c : ℝ} (hc : 0<c) :
    Tendsto (fun n : ℕ=>exp (-c*(n:ℝ))) atTop (𝓝 0) := by
  simpa using (summable_pow_mul_exp_neg_nat_mul 0 hc).tendsto_atTop_zero
lemma n_exp_rate_limit {c : ℝ} (hc : 0<c) :
    Tendsto (fun n : ℕ=>(n:ℝ)*exp (-c*(n:ℝ))) atTop (𝓝 0) := by
  simpa using (summable_pow_mul_exp_neg_nat_mul 1 hc).tendsto_atTop_zero

lemma recipeNormTail_limit {j : ℝ} (hj : 0<j) :
    Tendsto (recipeNormTail j) atTop (𝓝 0) := by
  have h₁ : Tendsto (fun n : ℕ=>ENNReal.ofReal (2*exp (-(n:ℝ)/(π^2*j)))) atTop (𝓝 0) := by
    have H:=ENNReal.tendsto_ofReal ((exp_rate_limit (c:=1/(π^2*j)) (by positivity)).const_mul 2)
    simpa only [mul_zero,ENNReal.ofReal_zero,show ∀(n : ℕ),-(1/(π^2*j))*(n:ℝ)=-(n:ℝ)/(π^2*j) by intro n;ring] using H
  have h₂ : Tendsto (fun n : ℕ=>ENNReal.ofReal (2*(n:ℝ)*exp (-1/(8*(j/n))))) atTop (𝓝 0) := by
    have H:=ENNReal.tendsto_ofReal ((n_exp_rate_limit (c:=1/(8*j)) (by positivity)).const_mul 2)
    have HH : Tendsto (fun n : ℕ=>ENNReal.ofReal (2*((n:ℝ)*exp (-(1/(8*j))*(n:ℝ))))) atTop (𝓝 0):=by simpa using H
    apply HH.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n:ℝ)≠0:=by exact_mod_cast (by omega : n≠0)
    congr 1
    rw [mul_assoc]
    congr 2
    field_simp
  convert h₁.add h₂ using 1 <;> first | rfl | simp

lemma ordinaryWordTail_limit {j : ℝ} (hj : 0<j) (L : ℕ) :
    Tendsto (ordinaryWordTail j L) atTop (𝓝 0) := by
  have h₁ : Tendsto (fun n : ℕ=>ENNReal.ofReal (3*exp (-(n:ℝ)))) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal ((exp_rate_limit (c:=1) (by norm_num)).const_mul 3)
  have h₂ : Tendsto (fun n : ℕ=>ENNReal.ofReal (exp (-2*(n:ℝ)/(π^2*(sqrt (2*j))^2)))) atTop (𝓝 0) := by
    have hsq : 0<(sqrt (2*j))^2:=by rw [sq_sqrt (by positivity)]; positivity
    have H:=ENNReal.tendsto_ofReal (exp_rate_limit (c:=2/(π^2*(sqrt (2*j))^2)) (by positivity))
    simpa only [ENNReal.ofReal_zero,show ∀(n : ℕ),-(2/(π^2*(sqrt (2*j))^2))*(n:ℝ)= -2*(n:ℝ)/(π^2*(sqrt (2*j))^2) by intro n;ring] using H
  have h₃:=(ENNReal.Tendsto.const_mul h₁ (a:=((wordPatternSet L L).card:ENNReal)) (Or.inr (by simp))).add h₂ |>.add (recipeNormTail_limit hj)
  convert ENNReal.Tendsto.const_mul h₃ (a:=2) (Or.inr (by simp)) using 1 <;> first | rfl | simp

theorem gaussian_recipe_event_probability {j A : ℝ} (hj : 0<j) (hj1 : j<1) (hA : 1≤A)
    (M Nmax : ℕ) : ∃R B W C : ℝ, 1≤R ∧ 0≤B ∧ 0≤W ∧ 0<C ∧
      Tendsto (fun n=>(Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1))
        {g | ¬RecipeMatrixEvent j R A B W C M Nmax
          (removeDiagonal (goeMatrix (j/n) g))}) atTop (𝓝 0) := by
  obtain ⟨R,B,W,C,N,hR,hB,hW,hC,hN,hb⟩:=gaussian_recipe_event hj hj1 hA M Nmax
  refine ⟨R,B,W,C,hR,hB,hW,hC,?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (show Tendsto (fun n=>recipeNormTail j n+ordinaryWordTail j (2*M+2*Nmax+3) n) atTop (𝓝 0) from
      by simpa using (recipeNormTail_limit hj).add (ordinaryWordTail_limit hj _))
    (Filter.Eventually.of_forall (fun _=>bot_le))
  filter_upwards [eventually_ge_atTop N] with n hn
  exact hb n hn

end SKGapCutoff.Recipe

end
end

end OAI
