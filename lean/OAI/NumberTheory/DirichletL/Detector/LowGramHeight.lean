import OAI.NumberTheory.DirichletL.Detector.LowGramProfile

namespace OAI

noncomputable section
open scoped Classical ContDiff SchwartzMap Topology
open Filter Set CompletedHeight FourierBridge
namespace SevenEighths.ProbePhysical

def lowGramBaseWindow (W : ℝ→ℂ) (r : ℝ) : ℂ := W r/(r:ℂ)

lemma lowGramBaseWindow_support (W : ℝ→ℂ) :
    Function.support (lowGramBaseWindow W)⊆Function.support W := by
  intro r hr hz
  exact hr (by simp [lowGramBaseWindow,hz])

lemma lowGramBaseWindow_smooth (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (lowGramBaseWindow W) := by
  rw [contDiff_iff_contDiffAt]
  intro r
  by_cases hr : r=0
  · subst r
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ=>(0:ℂ)) 0).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds ha] with x hx
    have hz : W x=0 := by
      by_contra h
      exact (not_le.mpr hx) (hs h).1
    simp [lowGramBaseWindow,hz]
  · unfold lowGramBaseWindow
    simp only [div_eq_mul_inv]
    exact hW.contDiffAt.mul (Complex.ofRealCLM.contDiff.contDiffAt.fun_inv (Complex.ofReal_ne_zero.mpr hr))

lemma lowGramProfile_twist (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (v r : ℝ) :
    lowGramProfile W v r=normTwistedSource (lowGramBaseWindow W) (v/(2*Real.pi)) r := by
  by_cases hz : W r=0
  · simp [lowGramProfile,normTwistedSource,lowGramBaseWindow,hz]
  have hr : 0<r := ha.trans_le (hs hz).1
  have hrc : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hp : (r:ℂ)^((v:ℂ)*Complex.I)=logPhase (v/(2*Real.pi)) (Real.log r) := by
    rw [Complex.cpow_def_of_ne_zero hrc,←Complex.ofReal_log hr.le]
    unfold logPhase
    congr 1
    push_cast
    field_simp
  rw [lowGramProfile,Complex.cpow_add _ _ hrc,Complex.cpow_neg_one,hp]
  unfold normTwistedSource lowGramBaseWindow
  ring

def lowGramSchwartz (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) (v : ℝ) : SchwartzMap ℝ ℂ :=
  uniformTwistedSchwartz (lowGramBaseWindow W) a b ha
    ((lowGramBaseWindow_support W).trans hs) (lowGramBaseWindow_smooth W a b ha hs hW) (v/(2*Real.pi))

lemma lowGramSchwartz_apply (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) (v r : ℝ) :
    lowGramSchwartz W a b ha hs hW v r=lowGramProfile W v r := by
  rw [lowGramSchwartz,uniformTwistedSchwartz_apply,lowGramProfile_twist W a b ha hs]

theorem lowGramProfile_uniform_degree (a b : ℝ) (ha : 0<a) (S : Finset (ℕ×ℕ)) :
    ∃n : ℕ,∀W : ℝ→ℂ,∀hs : Function.support W⊆Set.Icc a b,∀hW : ContDiff ℝ ∞ W,
      ∃C : ℝ,0<C ∧ ∀v : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (lowGramSchwartz W a b ha hs hW v)≤C*(1+‖v‖)^n := by
  obtain ⟨n,hn⟩ := normTwistedSource_uniform_degree a b ha S
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨C,hC,hb⟩ := hn (lowGramBaseWindow W) ((lowGramBaseWindow_support W).trans hs)
    (lowGramBaseWindow_smooth W a b ha hs hW)
  refine ⟨C,hC,?_⟩
  intro v
  apply (hb (v/(2*Real.pi))).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply pow_le_pow_left₀ (by positivity)
  gcongr
  simp only [norm_div,Real.norm_eq_abs,abs_of_pos (show (0:ℝ)<2*Real.pi by positivity)]
  exact div_le_self (norm_nonneg v) (by linarith [Real.pi_gt_three])

end SevenEighths.ProbePhysical
end

end OAI
