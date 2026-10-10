import OAI.Geometry.Convex.GeneralMahler.Hermite.L2

namespace OAI
/-! Hermite coefficient recurrence for functions with suitable local
Lipschitz bounds. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Metric Real ProbabilityTheory ContinuousLinearMap
open scoped Topology NNReal ENNReal RealInnerProductSpace
namespace GeneralMahler.HMode
variable {m:ℕ}
variable {F:Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

omit [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
lemma shift_bound_poly {f:Rn m→F} (hf:PolyBound f) :
    ∃ g:Rn m→ℝ, PolyBound g ∧ Continuous g ∧ ∀ x y:Rn m, y∈closedBall x 1 → ‖f y‖ ≤ g x := by
  obtain ⟨C,n,hc,h⟩ := hf
  let g := fun x:Rn m=> C*(2+‖x‖)^n
  refine ⟨g,(PolyBound.const _).mul (((PolyBound.const _).add PolyBound.id.norm).pow _),
    by unfold g; fun_prop,fun x y hy => ?_⟩
  apply le_trans (h y)
  unfold g; gcongr C * ?_ ^ n; change dist y x ≤ 1 at hy; rw [dist_eq_norm] at hy
  have he : ‖y‖ ≤ ‖y-x‖+‖x‖ := by simpa using norm_add_le (y-x) x
  linarith

def PLip (f:Rn m→F) := ∃ g:Rn m→ℝ, PolyBound g ∧ Continuous g ∧
    ∀ x b:Rn m, ‖b‖ < 1 → ‖f (x+b)-f x‖ ≤ g x*‖b‖
namespace PLip
omit [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
lemma lip {f:Rn m→F} {K:ℝ≥0} (hk:LipschitzWith K f) : PLip f := by
  use fun _=> (K:ℝ)
  refine ⟨PolyBound.const _,continuous_const,fun x b _ =>?_⟩
  simpa only [dist_eq_norm, add_sub_cancel_left] using hk.dist_le_mul (x+b) x
omit [FiniteDimensional ℝ F] in
lemma smul {f:Rn m→ℝ} {h:Rn m→F} (hf:PolyBound f) (hh:PolyBound h) -- measurable h via cont
    (hc:Continuous h) (hl:PLip f) (hl':PLip h) : PLip fun x=> f x • h x := by
  obtain ⟨g,hg,hg',H⟩ := shift_bound_poly hf
  obtain ⟨c,h₁,h₂,he⟩ := hl
  obtain ⟨d,h₃,h₄,ht⟩ := hl'
  let k := fun x=> g x*d x + ‖h x‖*c x
  refine ⟨k,(hg.mul h₃).add (hh.norm.mul h₁),(hg'.mul h₄).add (hc.norm.mul h₂),fun x b hb => ?_⟩
  have hy : x+b∈closedBall x 1 := by simpa only [mem_closedBall,dist_eq_norm,
    add_sub_cancel_left] using hb.le
  have hh := H x (x+b) hy
  have ha := he x b hb
  have hu := ht x b hb
  have hp : 0 ≤ g x := le_trans (norm_nonneg _) hh
  calc
    _ = ‖f (x+b) • (h (x+b)-h x) + (f (x+b)-f x) • h x‖ := by rw [smul_sub,sub_smul]; congr 1; abel
    _ ≤ _ := norm_add_le ..
    _ ≤ k x*‖b‖ := by
      rw [norm_smul,norm_smul]
      apply le_trans (add_le_add (mul_le_mul hh hu (norm_nonneg _) hp)
        (mul_le_mul_of_nonneg_right ha (norm_nonneg _)))
      apply le_of_eq; unfold k; ring
omit [FiniteDimensional ℝ F] in
lemma fd {f:Rn m→F} (hf:Differentiable ℝ f)
    (hp:PolyBound (fderiv ℝ f)) : PLip f := by
  obtain ⟨g,hg,hc,h⟩ := shift_bound_poly hp
  use g
  refine ⟨hg,hc,fun x b hb=>?_⟩
  have hs := closedBall x (1:ℝ)
  have hy : x+b∈closedBall x 1 := by change dist (x+b) x≤1; simpa [dist_eq_norm] using hb.le
  have he := (convex_closedBall x 1).norm_image_sub_le_of_norm_fderiv_le (fun y _=>hf y)
    (fun y hy => h x y hy) (mem_closedBall_self (by norm_num)) hy
  simpa only [add_sub_cancel_left] using he
end PLip

lemma p_sum {I X F:Type*} [SeminormedAddCommGroup X] [SeminormedAddCommGroup F]
    {f:I→X→F} (h:∀ i,PolyBound (f i)) (s:Finset I) :
    PolyBound fun x=> ∑ i∈s, f i x := by
  classical
  induction s using Finset.induction with
  | empty=>simpa using PolyBound.const (X:=X) (0:F)
  | insert x u h' ih=>simpa [h'] using (h x).add ih

lemma fdMP (a:MI m) : PolyBound (fderiv ℝ (MM a)) := by
  let B := EuclideanSpace.basisFun (Fin m) ℝ
  let g := fun i (x:Rn m)=> (sn (a i)*MM (decM a i) x) • (ProjField.coord i)
  have he (x:Rn m) : fderiv ℝ (MM a) x = ∑ i, g i x := by
    ext y
    have hl := B.sum_repr y
    calc
      _ = ∑ i, B.repr y i * (fderiv ℝ (MM a) x (e i)) := by
        conv_lhs => rw [← hl]
        rw [_root_.map_sum]; simp [B,e]
      _ = _ := by simp_rw [part_lower]; simp [g,B,mul_comm]
  rw [show fderiv ℝ (MM a)=_ from funext he]
  apply p_sum (f:=g)
  intro i
  exact ((PolyBound.const _).mul (M_poly _)).smul (PolyBound.const _)

def cof (f:Rn m→F) (a:MI m) : F := ∫ x,MM a x • f x ∂normal m
omit [FiniteDimensional ℝ F] in
lemma i_cof {f:Rn m→F} (hf:PolyBound f) (hm:AEStronglyMeasurable f (normal m)) (a:MI m) :
    Integrable (fun x=>MM a x • f x) (normal m) :=
  ((M_poly a).smul hf).gaussian_integrable ((M_cont a).aestronglyMeasurable.smul hm)
lemma qcf_cof (f:Rn m→ℝ) (a) : qcf f a=cof f a := by
  unfold qcf cof; congr 1; ext x; exact mul_comm ..
lemma coef_raise {f:Rn m→F} (hf:PolyBound f) (hF:PLip f) (hc:Continuous f)
    {D:Rn m→(Rn m→L[ℝ]F)}
    (hD:∀ᵐ x∂normal m,HasFDerivAt f (D x) x)
    (i:Fin m)
    (hP:PolyBound (fun x=> D x (e i))) (hm:AEStronglyMeasurable (fun x=>D x (e i)) (normal m))
    (a:MI m) :
    cof (fun x=> D x (e i)) a=sn (a i+1) • cof f (inc a i) := by
  let g := fun x=> MM a x • f x
  obtain ⟨b,h₁,h₂,hb⟩ :=
    PLip.smul (M_poly a) hf hc (PLip.fd (M_diff a) (fdMP a)) hF
  have he : ∀ᵐ x∂normal m,
      DifferentiableAt ℝ g x ∧ fderiv ℝ g x (e i) =
        sn (a i) • (MM (decM a i) x • f x)+ MM a x • D x (e i) := by
    filter_upwards [hD] with x hx
    have hh := (M_diff a x).hasFDerivAt.smul hx
    refine ⟨hh.differentiableAt,?_⟩
    rw [show fderiv ℝ g x=_ from hh.fderiv]
    simp only [_root_.add_apply,_root_.smul_apply,smulRight_apply,part_lower,mul_smul]; rw [add_comm]
  have h := normal_IBP (f:=g) ((M_poly a).smul hf) ((M_cont a).smul hc)
    (he.mono fun x hx=> hx.1) (h₁.gaussian_integrable h₂.aestronglyMeasurable) hb (e i)
  have hi := i_cof hP hm a
  have ih (a) := i_cof hf hc.aestronglyMeasurable a
  have hr (x:Rn m) :
      ⟪x,e i⟫ • g x=sn (a i+1) • (MM (inc a i) x • f x)+sn (a i) • (MM (decM a i) x • f x) := by
    rw [ee]; unfold g
    simp only [smul_smul,ladder,add_smul]
  rw [integral_congr_ae (he.mono fun x hx=>hx.2)] at h; simp_rw [hr] at h
  rw [integral_add,integral_add,integral_smul,integral_smul] at h
  · exact add_left_cancel (h.trans (add_comm _ _))
  all_goals first | exact (ih _).smul (_:ℝ) | exact hi
end GeneralMahler.HMode

end

end OAI
