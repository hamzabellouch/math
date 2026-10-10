import OAI.Analysis.LipschitzHilbert.Phase.AngularMassMotion
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

namespace OAI

/-! Relative motion of nonnegative logarithmic losses. Both the submass
and its complement are actual positive sums. Vanishing complements give
identically zero loss and need no logarithmic positivity assumption. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

/-- Concavity of the logarithm controls multiplicative changes in its
nonnegative argument, uniformly even at argument zero. -/
theorem log_one_add_scaled_le {c q : ℝ} (hc : 1 ≤ c) (hq : 0 ≤ q) :
    Real.log (1+c*q) ≤ c*Real.log (1+q) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hi : 0 ≤ 1/c := by positivity
  have hi1 : 1/c ≤ 1 := (div_le_one hc0).mpr hc
  have h := strictConcaveOn_log_Ioi.concaveOn.2
    (show (1:ℝ) ∈ Set.Ioi 0 by norm_num)
    (show 1+c*q ∈ Set.Ioi 0 by change 0 < 1+c*q; positivity)
    (sub_nonneg.mpr hi1) hi (by ring : (1-1/c)+1/c=1)
  have heq : (1-1/c)*1+(1/c)*(1+c*q)=1+q := by field_simp [hc0.ne']; ring
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add] at h
  rw [heq] at h
  have hm := mul_le_mul_of_nonneg_left h hc0.le
  have hcancel : c*((1/c)*Real.log (1+c*q))=Real.log (1+c*q) := by field_simp [hc0.ne']
  rw [hcancel] at hm
  exact hm

theorem positive_le_exp_mul_of_log_motion {a b delta : ℝ}
    (ha : 0 < a) (hb : 0 < b) (h : |Real.log b-Real.log a| ≤ delta) :
    b ≤ Real.exp delta*a := by
  calc
    b = Real.exp (Real.log b) := (Real.exp_log hb).symm
    _ ≤ Real.exp (delta+Real.log a) := Real.exp_le_exp.mpr (by linarith [(abs_le.mp h).2])
    _ = _ := by rw [Real.exp_add, Real.exp_log ha]

/-- The loss log((a+b)/a) varies relatively with the positive submass and
complement, instead of paying a constant independent of that loss. -/
theorem positive_complement_loss_motion {a b a' b' delta : ℝ}
    (ha : 0 < a) (hb : 0 < b) (ha' : 0 < a') (hb' : 0 < b')
    (hdelta : 0 ≤ delta)
    (hA : |Real.log a'-Real.log a| ≤ delta)
    (hB : |Real.log b'-Real.log b| ≤ delta) :
    |Real.log ((a'+b')/a')-Real.log ((a+b)/a)| ≤
      (Real.exp (2*delta)-1)*Real.log ((a+b)/a) := by
  let c := Real.exp (2*delta)
  have hc : 1 ≤ c := Real.one_le_exp (by positivity)
  have ha0 : 0 < b/a := div_pos hb ha
  have ha1 : 0 < b'/a' := div_pos hb' ha'
  have hodds := positive_ratio_log_motion hb ha hb' ha' hB hA
  have hforward : b'/a' ≤ c*(b/a) :=
    positive_le_exp_mul_of_log_motion ha0 ha1 hodds
  have hreverse : b/a ≤ c*(b'/a') := positive_le_exp_mul_of_log_motion ha1 ha0 (by
    simpa only [abs_sub_comm] using hodds)
  have hup : Real.log (1+b'/a') ≤ c*Real.log (1+b/a) := by
    exact (Real.log_le_log (by positivity) (show 1+b'/a' ≤ 1+c*(b/a) from add_le_add le_rfl hforward)).trans
      (log_one_add_scaled_le hc ha0.le)
  have hrev : Real.log (1+b/a) ≤ c*Real.log (1+b'/a') := by
    exact (Real.log_le_log (by positivity) (show 1+b/a ≤ 1+c*(b'/a') from add_le_add le_rfl hreverse)).trans
      (log_one_add_scaled_le hc ha1.le)
  have hnonneg : 0 ≤ Real.log (1+b/a) := Real.log_nonneg (by linarith)
  have hnonneg' : 0 ≤ Real.log (1+b'/a') := Real.log_nonneg (by linarith)
  have habs : |Real.log (1+b'/a')-Real.log (1+b/a)| ≤
      (c-1)*Real.log (1+b/a) := by
    apply abs_le.mpr
    constructor
    · by_cases hle : Real.log (1+b'/a') ≤ Real.log (1+b/a)
      · have hm := mul_le_mul_of_nonneg_left hle (sub_nonneg.mpr hc)
        nlinarith
      · have hm : 0 ≤ (c-1)*Real.log (1+b/a) := mul_nonneg (sub_nonneg.mpr hc) hnonneg
        linarith
    · nlinarith
  simpa only [add_div, div_self ha.ne', div_self ha'.ne'] using habs

/-- A finite submass and its actual set complement give relative loss
motion. Empty complements are handled exactly, as zero loss. -/
theorem finite_submass_loss_motion {ι : Type*} [DecidableEq ι] (C A : Finset ι) (hsub : A ⊆ C)
    (hA : A.Nonempty) (w0 w1 : ι → ℝ)
    (hw0 : ∀ t ∈ C, 0 < w0 t) (hw1 : ∀ t ∈ C, 0 < w1 t)
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (hmass : |Real.log (∑ t ∈ A, w1 t)-Real.log (∑ t ∈ A, w0 t)| ≤ delta)
    (hcomplement : (C\A).Nonempty →
      |Real.log (∑ t ∈ C\A, w1 t)-Real.log (∑ t ∈ C\A, w0 t)| ≤ delta) :
    |Real.log ((∑ t ∈ C, w1 t)/(∑ t ∈ A, w1 t)) -
      Real.log ((∑ t ∈ C, w0 t)/(∑ t ∈ A, w0 t))| ≤
        (Real.exp (2*delta)-1)*Real.log ((∑ t ∈ C, w0 t)/(∑ t ∈ A, w0 t)) := by
  classical
  have hpos0 : 0 < ∑ t ∈ A, w0 t := Finset.sum_pos (fun t ht => hw0 t (hsub ht)) hA
  have hpos1 : 0 < ∑ t ∈ A, w1 t := Finset.sum_pos (fun t ht => hw1 t (hsub ht)) hA
  have hsum (w : ι → ℝ) : (∑ t ∈ C, w t) = (∑ t ∈ A, w t)+(∑ t ∈ C\A, w t) := by
    have h := Finset.sum_sdiff (f := w) hsub
    linarith
  rw [hsum w0, hsum w1]
  by_cases hnonempty : (C\A).Nonempty
  · have hc0 : 0 < ∑ t ∈ C\A, w0 t :=
      Finset.sum_pos (fun t ht => hw0 t (Finset.mem_sdiff.mp ht).1) hnonempty
    have hc1 : 0 < ∑ t ∈ C\A, w1 t :=
      Finset.sum_pos (fun t ht => hw1 t (Finset.mem_sdiff.mp ht).1) hnonempty
    exact positive_complement_loss_motion hpos0 hc0 hpos1 hc1 hdelta hmass
      (hcomplement hnonempty)
  · have he : C\A=∅ := Finset.not_nonempty_iff_eq_empty.mp hnonempty
    simp only [he, Finset.sum_empty, add_zero, div_self hpos0.ne', div_self hpos1.ne',
      Real.log_one, sub_self, abs_zero, mul_zero, le_refl]

/-- On the small-motion range the relative loss factor is linear in
that motion, with an absolute constant. -/
theorem relative_loss_factor_le {delta : ℝ} (hdelta : 0 ≤ delta) (hsmall : delta ≤ 1/2) :
    Real.exp (2*delta)-1 ≤ (2*Real.exp 1)*delta := by
  have h := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_deriv_le
    (fun x _ => Real.differentiableAt_exp)
    (fun x hx => by
      rw [Real.deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)]
      exact Real.exp_le_exp.mpr hx.2)
    (show (0:ℝ) ∈ Set.Icc 0 1 by norm_num)
    (show 2*delta ∈ Set.Icc (0:ℝ) 1 by constructor <;> linarith)
  have hnonneg : 0 ≤ Real.exp (2*delta)-1 :=
    sub_nonneg.mpr (Real.one_le_exp (by positivity))
  simp only [Real.exp_zero, Real.norm_eq_abs, sub_zero] at h
  rw [abs_of_nonneg hnonneg, abs_of_nonneg (show 0 ≤ 2*delta by positivity)] at h
  nlinarith

namespace AngularGrid

/-- At the source mesh scale, the child-to-containing-mass loss has a
relative error of order G^(-1/2), including identically zero losses. -/
theorem source_relative_loss_motion {ι : Type*} (g : AngularGrid) (tops : Finset ι)
    (T : ι → SlopeBox) (w B K D : ℝ) (hw : 0 < w) (hB : 1 ≤ B)
    (hK : 0 < K) (hD : 0 ≤ D) (hwidth : ∀ t ∈ tops, B^2*w ≤ (T t).width)
    (base h i : ℕ) (hhi : h ≤ i) (gap : ℝ) (hgap0 : 0 ≤ gap) (hgap : gap ≤ g.width h)
    (s sR : ℝ) (hs : g.index h s = g.index h sR)
    (child : ℝ) (hchild : 0 < child) (hblock : g.width h ≤ B*child)
    (C A : Finset ι) (hsub : A ⊆ C) (hA : A.Nonempty)
    (hC : C ⊆ g.boundaryTops tops (fun t => (T t).slope)
      (fun t => w/(T t).length) (g.rootWidth/B^2) base i gap s)
    (a : ℝ) (ha : |a| ≤ w/(child*Real.sqrt (g.branching:ℝ))) (z : ℝ × ℝ) :
    let loss := fun x => Real.log ((∑ t ∈ C, (T t).weight K D x)/(∑ t ∈ A, (T t).weight K D x))
    let delta := (5*D/K)/Real.sqrt (g.branching:ℝ)
    |loss (SlopeBox.lineShift sR a z)-loss z| ≤ (Real.exp (2*delta)-1)*loss z := by
  classical
  dsimp only
  apply finite_submass_loss_motion C A hsub hA
    (fun t => (T t).weight K D z) (fun t => (T t).weight K D (SlopeBox.lineShift sR a z))
    (fun t _ => (T t).weight_pos hK D z) (fun t _ => (T t).weight_pos hK D _)
  · positivity
  · exact g.boundary_submass_source_motion tops T w B K D hw hB hK hD hwidth
      base h i hhi gap hgap0 hgap s sR hs child hchild hblock A hA (hsub.trans hC) a ha z
  · intro hnonempty
    exact g.boundary_submass_source_motion tops T w B K D hw hB hK hD hwidth
      base h i hhi gap hgap0 hgap s sR hs child hchild hblock (C\A) hnonempty
      (fun t ht => hC (Finset.mem_sdiff.mp ht).1) a ha z

end AngularGrid
end LipschitzHilbert

end

end OAI
