import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

namespace OAI

/-! Uniform finite-difference error estimates including error in function
values. They will be applied to coordinate lines of the explicit C6 field. -/

namespace ContinuumCoulomb.FiniteDifferenceError

theorem linear_remainder (f f' : ℝ → ℝ) {a h b B : ℝ} (hh : 0 ≤ h)
    (hf : ∀ s ∈ Set.Icc a (a+h), HasDerivAt f (f' s) s)
    (hb : ∀ s ∈ Set.Ico a (a+h), |f' s-b| ≤ B) :
    |f (a+h)-f a-h*b| ≤ B*h := by
  let F : ℝ → ℝ := fun s => f s-(s-a)*b
  have hF (s : ℝ) (hs : s ∈ Set.Icc a (a+h)) :
      HasDerivWithinAt F (f' s-b) (Set.Icc a (a+h)) s := by
    have hd := ((hasDerivAt_id s).sub_const a).mul_const b
    simpa only [F,id_eq,one_mul] using ((hf s hs).fun_sub hd).hasDerivWithinAt
  have he := norm_image_sub_le_of_norm_deriv_le_segment' hF
    (fun s hs => by simpa only [Real.norm_eq_abs] using hb s hs)
    (a+h) (show a+h ∈ Set.Icc a (a+h) from ⟨by linarith,le_rfl⟩)
  have hid : f (a+h)-f a-h*b = F (a+h)-F a := by dsimp [F]; ring
  rw [hid]
  simpa only [Real.norm_eq_abs,add_sub_cancel_left] using he

theorem forward_difference (f f' evaluate : ℝ → ℝ) {x h L ε : ℝ}
    (hh : 0 < h) (hL : 0 ≤ L) (_hε : 0 ≤ ε)
    (hf : ∀ s ∈ Set.Icc x (x+h), HasDerivAt f (f' s) s)
    (hLip : ∀ s ∈ Set.Ico x (x+h), |f' s-f' x| ≤ L*|s-x|)
    (he0 : |evaluate x-f x| ≤ ε) (he1 : |evaluate (x+h)-f (x+h)| ≤ ε) :
    |(evaluate (x+h)-evaluate x)/h-f' x| ≤ L*h+2*ε/h := by
  have hr := linear_remainder f f' hh.le hf (b := f' x) (B := L*h) (by
    intro s hs
    have ht : |s-x| ≤ h := by rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]; linarith [hs.2]
    exact (hLip s hs).trans (mul_le_mul_of_nonneg_left ht hL))
  have hsum : |evaluate (x+h)-evaluate x-h*f' x| ≤ L*h^2+2*ε := by
    have hid : evaluate (x+h)-evaluate x-h*f' x =
        (evaluate (x+h)-f (x+h))-(evaluate x-f x)+(f (x+h)-f x-h*f' x) := by ring
    rw [hid]
    exact ((abs_add_le _ _).trans (add_le_add (abs_sub _ _ |>.trans (add_le_add he1 he0)) hr)).trans_eq (by ring)
  have hid : (evaluate (x+h)-evaluate x)/h-f' x =
      (evaluate (x+h)-evaluate x-h*f' x)/h := by field_simp
  rw [hid,abs_div,abs_of_pos hh]
  apply (div_le_div_of_nonneg_right hsum hh.le).trans_eq
  field_simp

theorem centered_remainder (f f' f'' : ℝ → ℝ) {x h L : ℝ}
    (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hf : ∀ s, HasDerivAt f (f' s) s)
    (hf' : ∀ s, HasDerivAt f' (f'' s) s)
    (hLip : ∀ s ∈ Set.Icc (x-h) (x+h), |f'' s-f'' x| ≤ L*|s-x|) :
    |f (x+h)+f (x-h)-2*f x-h^2*f'' x| ≤ L*h^3 := by
  let G : ℝ → ℝ := fun s => f (s+h)-f s
  let G' : ℝ → ℝ := fun s => f' (s+h)-f' s
  have hG (s : ℝ) (_hs : s ∈ Set.Icc (x-h) (x-h+h)) : HasDerivAt G (G' s) s := by
    exact ((hf (s+h)).comp s ((hasDerivAt_id s).add_const h)).sub (hf s) |>.congr_deriv (by ring)
  have hGbound (s : ℝ) (hs : s ∈ Set.Ico (x-h) (x-h+h)) :
      |G' s-h*f'' x| ≤ L*h^2 := by
    have hr := linear_remainder f' f'' hh (fun r _ => hf' r) (a := s) (b := f'' x)
      (B := L*h) (by
        intro r hr
        have hri : r ∈ Set.Icc (x-h) (x+h) := by constructor <;> linarith [hs.1,hs.2,hr.1,hr.2]
        have hdist : |r-x| ≤ h := abs_le.mpr ⟨by linarith [hri.1],by linarith [hri.2]⟩
        exact (hLip r hri).trans (mul_le_mul_of_nonneg_left hdist hL))
    exact hr.trans_eq (by ring)
  have hr := linear_remainder G G' hh hG hGbound
  have hid : G (x-h+h)-G (x-h)-h*(h*f'' x) =
      f (x+h)+f (x-h)-2*f x-h^2*f'' x := by
    dsimp [G]
    rw [sub_add_cancel]
    ring
  rw [hid] at hr
  exact hr.trans_eq (by ring)

theorem centered_difference (f f' f'' evaluate : ℝ → ℝ) {x h L ε : ℝ}
    (hh : 0 < h) (hL : 0 ≤ L)
    (hf : ∀ s, HasDerivAt f (f' s) s) (hf' : ∀ s, HasDerivAt f' (f'' s) s)
    (hLip : ∀ s ∈ Set.Icc (x-h) (x+h), |f'' s-f'' x| ≤ L*|s-x|)
    (he0 : |evaluate x-f x| ≤ ε) (hep : |evaluate (x+h)-f (x+h)| ≤ ε)
    (hem : |evaluate (x-h)-f (x-h)| ≤ ε) :
    |(evaluate (x+h)+evaluate (x-h)-2*evaluate x)/h^2-f'' x| ≤ L*h+4*ε/h^2 := by
  have hr := centered_remainder f f' f'' hh.le hL hf hf' hLip
  have herr : |evaluate (x+h)+evaluate (x-h)-2*evaluate x-h^2*f'' x| ≤ L*h^3+4*ε := by
    have hid : evaluate (x+h)+evaluate (x-h)-2*evaluate x-h^2*f'' x =
        (f (x+h)+f (x-h)-2*f x-h^2*f'' x)+
          ((evaluate (x+h)-f (x+h))+(evaluate (x-h)-f (x-h))-2*(evaluate x-f x)) := by ring
    rw [hid]
    have hnoise : |(evaluate (x+h)-f (x+h))+(evaluate (x-h)-f (x-h))-2*(evaluate x-f x)| ≤ 4*ε := by
      apply (abs_sub _ _).trans
      have hs := (abs_add_le _ _).trans (add_le_add hep hem)
      rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
      linarith
    exact (abs_add_le _ _).trans (add_le_add hr hnoise)
  have hid : (evaluate (x+h)+evaluate (x-h)-2*evaluate x)/h^2-f'' x =
      (evaluate (x+h)+evaluate (x-h)-2*evaluate x-h^2*f'' x)/h^2 := by field_simp
  rw [hid,abs_div,abs_of_nonneg (sq_nonneg h)]
  apply (div_le_div_of_nonneg_right herr (sq_nonneg h)).trans_eq
  field_simp

end ContinuumCoulomb.FiniteDifferenceError

end OAI
