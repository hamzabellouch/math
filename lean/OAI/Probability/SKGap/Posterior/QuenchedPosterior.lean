import Mathlib
import OAI.Probability.SKGap.Matrix.BufferedClosedWord
import OAI.Probability.SKGap.Posterior.BufferedPosteriorCovariance
import OAI.Probability.SKGap.Localization.QuenchedHelpers

namespace OAI

namespace SKGap.FullMain
open MeasureTheory ProbabilityTheory Filter Set Real
open scoped Topology BigOperators
open SKGapCutoff SKGapCutoff.Recipe SKGapCutoff.Primary SKGapCutoff.Static
noncomputable section

lemma recipe_increase_diagnostics {n M N : ℕ} {j K A B W C W' C' : ℝ}
    {J : Interaction n} (H : RecipeMatrixEvent j K A B W C M N J)
    (hW : W≤W') (hC : C≤C') : RecipeMatrixEvent j K A B W' C' M N J := by
  exact ⟨H.1,H.2.1,fun w hl hw=>(H.2.2.1 w hl hw).trans hW,
    fun w hl hw=>(H.2.2.2 w hl hw).trans hC⟩

lemma started_replace_shapes {n M N : ℕ} {j K A₀ A c B B' W C W' C' : ℝ}
    {J : Interaction n} (H : StartedMatrixEvent j K A₀ A c B W C M N J)
    (hf : ∀h x l,l<M→ShapeBound (formalField j J h x l) B')
    (hW : W≤W') (hC : C≤C') : StartedMatrixEvent j K A₀ A c B' W' C' M N J := by
  refine ⟨H.1,hf,?_⟩
  intro a ha hc
  have ht:=H.2.2 a ha hc
  exact ⟨fun w hl hi hw=>(ht.1 w hl hi hw).trans hW,fun w hl hi hw=>(ht.2 w hl hi hw).trans hC⟩

def PosteriorCovarianceProperty {n : ℕ} (j Aroot ε c r₀ D : ℝ) (g : Disorder n) : Prop :=
  ∀h:Fin n→ℝ,¬rootBad j Aroot ε c r₀ (coupling g) h→∀f:Observables n,
    vectorNorm (centeredSpinCovariance (fieldGibbs (coupling g) h) f)≤
      D*sqrt ((∑x,fieldGibbs (coupling g) h x*(f x-∑y,fieldGibbs (coupling g) h y*f y)^2)+
          varianceEnergy (fieldGibbs (coupling g) h) f)

theorem quenched_posterior_covariance {β Aroot ε c r₀ : ℝ}
    (hβ : 0<β) (hβ1 : β<1) (hAroot : 1<Aroot) (hs : β*Aroot<1)
    (hε : 0<ε) (hc : 0<c) (hr₀ : 0<r₀) :
    ∃D : ℝ,0≤D ∧ Whp β (fun n g=>PosteriorCovarianceProperty (n := n) (β^2) Aroot ε c r₀ D g) := by
  classical
  let j:=β^2
  let K:=physicalNormBound j
  let R:=2*log Aroot
  have hj : 0≤j:=sq_nonneg β
  have hK : 0≤K:=(physicalNormBound_pos j).le
  have hR : 0<R:=mul_pos (by norm_num) (log_pos hAroot)
  have hAR : exp (R/2)=Aroot:=by dsimp [R]; rw [mul_div_cancel_left₀ _ (by norm_num : (2:ℝ)≠0),exp_log (by linarith)]
  obtain ⟨ρ,hρ,h1,h2,h3,h4,h5⟩:=posterior_buffer_exists j K c r₀ R ε hc hr₀ hR hε
  obtain ⟨m,hm,δ,hδ,hdepth,hδm⟩:=posterior_selection_parameters hρ
  have hbudget : 1≤residualCoefficientBudget j 2 (2*m) 0 :=
    (by norm_num : (1:ℝ)≤2).trans (residualCoefficientBudget_ge j (by norm_num) (2*m) 0)
  obtain ⟨B,W,C,hB,hW,hC,hevent⟩:=disorder_fixed_norm_recipe_probability hβ hβ1 hbudget (2*m+1) (2*(2*m))
  obtain ⟨A,hA,hbound⟩:=buffered_posterior_covariance.{0} hj hK hB hAroot.le hc hr₀ hρ hε.le hAR.le h1 h2 h3 h4 h5
  let r:=2*m-1
  have hex : ∀k:Fin r,∃Bk Wk Ck:ℝ,0≤Bk ∧ 0≤Wk ∧ 0<Ck ∧
      Whp β (fun n g=>StartedMatrixEvent j K Aroot (max Aroot (A k)) (c/2)
        Bk Wk Ck (k+3) (2+2*(k+1)) (coupling g)) := by
    intro k
    exact disorder_started_matrix_event hβ hβ1 (by linarith) (by simpa only [sqrt_sq hβ.le] using hs)
      (le_max_left _ _) ((hA k).trans (le_max_right _ _)) (half_pos hc) _ _
  choose Bk Wk Ck hBk hWk hCk hpk using hex
  let W':=W+∑k:Fin r,Wk k
  let C':=C+∑k:Fin r,Ck k
  have hW' : W≤W':=le_add_of_nonneg_right (Finset.sum_nonneg (fun k _=>hWk k))
  have hC' : C≤C':=le_add_of_nonneg_right (Finset.sum_nonneg (fun k _=>(hCk k).le))
  have hwk (k:Fin r) : Wk k≤W':=by
    have hsum:=Finset.single_le_sum (fun k _=>hWk k) (Finset.mem_univ k)
    dsimp [W']
    linarith
  have hck (k:Fin r) : Ck k≤C':=by
    have hsum:=Finset.single_le_sum (fun k _=>(hCk k).le) (Finset.mem_univ k)
    dsimp [C']
    linarith
  let P : ∀n,Disorder n→Prop:=fun n g=>
    RecipeMatrixEvent j K (residualCoefficientBudget j 2 (2*m) 0) B W C (2*m+1) (2*(2*m)) (coupling g) ∧
    ∀k:Fin r,StartedMatrixEvent j K Aroot (max Aroot (A k)) (c/2) (Bk k) (Wk k) (Ck k)
      (k+3) (2+2*(k+1)) (coupling g)
  have hP : Whp β P:=by
    have hh:=whp_finset Finset.univ
      (fun (k:Fin r) n g=>StartedMatrixEvent j K Aroot (max Aroot (A k)) (c/2) (Bk k) (Wk k) (Ck k)
        (k+3) (2+2*(k+1)) (coupling g)) (fun k _=>hpk k)
    simpa only [Finset.mem_univ,forall_true_left] using (show Whp β _ from hevent).and hh
  let Dim (n:ℕ) : Prop:=∀k<r,4*(residualDerivativeBudget j K B k+residualDerivativeBudget j K B (k+1))≤ρ*sqrt (n:ℝ)
  have hDim : ∀ᶠ n:ℕ in atTop,Dim n:=by
    have ht : Tendsto (fun n:ℕ=>ρ*sqrt (n:ℝ)) atTop atTop:=
      (tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hρ
    have hh : ∀k:Fin r,∀ᶠ n:ℕ in atTop,4*(residualDerivativeBudget j K B k+residualDerivativeBudget j K B (k+1))≤ρ*sqrt (n:ℝ):=
      fun k=>ht.eventually_ge_atTop _
    have hh':=Filter.eventually_all.mpr hh
    filter_upwards [hh'] with n hn
    exact fun k hk=>hn ⟨k,hk⟩
  let Ω:Type:={a:Σn,Disorder n × (Fin n→ℝ) // 0<a.1 ∧ P a.1 a.2.1 ∧
      ¬rootBad j Aroot ε c r₀ (coupling a.2.1) a.2.2 ∧ Dim a.1}
  obtain ⟨D,hD,hDall⟩:=hbound m δ hδ hdepth hδm W' C' (hW.trans hW') (hC.le.trans hC')
    Ω (fun a=>a.1.1) (fun a=>coupling a.1.2.1) (fun a=>a.1.2.2)
    (fun a=>a.2.1) (fun a=>by ext i k;exact coupling_symm a.1.2.1 k i)
    (fun a=>coupling_diag a.1.2.1)
    (fun a k hk=>by
      have ht:=(a.2.2.1.2 ⟨k,hk⟩).mono_budget (le_max_right Aroot (A k))
      have ht' : StartedMatrixEvent j K (exp (R/2)) (A k) (c/2) (Bk ⟨k,hk⟩) (Wk ⟨k,hk⟩) (Ck ⟨k,hk⟩) (k+3) (2+2*(k+1)) (coupling a.1.2.1) := by
        simpa only [hAR] using ht
      apply started_replace_shapes ht' _ (hwk ⟨k,hk⟩) (hck ⟨k,hk⟩)
      intro h x l hl
      exact a.2.2.1.1.2.1 h x l (by omega))
    (fun a=>recipe_increase_diagnostics a.2.2.1.1 hW' hC')
    (fun a=>a.2.2.2.1) (fun a=>a.2.2.2.2)
  refine ⟨D,hD,hP.mono ?_⟩
  filter_upwards [eventually_ge_atTop 1,hDim] with n hn hd
  intro g hg h hb f
  apply hDall ⟨⟨n,g,h⟩,?_⟩ f
  exact ⟨show 0<n from by omega,hg,hb,hd⟩

end
end SKGap.FullMain

end OAI
