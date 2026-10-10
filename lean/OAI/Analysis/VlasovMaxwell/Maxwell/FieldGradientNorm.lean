import Mathlib
import OAI.Analysis.VlasovMaxwell.LocalPDE.EquationsBefore
import OAI.Analysis.VlasovMaxwell.LocalPDE.PicardBoundary

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma curl_norm_le_gradient {F : Vec → Vec} (hF : Differentiable ℝ F) (x : Vec) :
    ‖curl F x‖≤6*‖fderiv ℝ F x‖ := by
  have hb : ∀ i : Fin 3, |curl F x i|≤2*‖fderiv ℝ F x‖ := by
    intro i
    have he : curl F x i=spatialPartial (fun y => F y (curlB i)) x (curlA i)-
        spatialPartial (fun y => F y (curlA i)) x (curlB i) := by
      fin_cases i <;> simp [curl,curlA,curlB]
    have hb (j k : Fin 3) : |spatialPartial (fun y => F y k) x j|≤‖fderiv ℝ F x‖ := by
      rw [spatialPartial,coordinate_fderiv_apply hF]
      simpa only [show ‖basis j‖=1 by simp [basis,PiLp.norm_single],mul_one] using
        (norm_coordinate_le _ k).trans ((fderiv ℝ F x).le_opNorm (basis j))
    rw [he]
    exact (abs_sub _ _).trans ((add_le_add (hb _ _) (hb _ _)).trans_eq (by ring))
  exact (norm_le_three_of_coordinate_bound (by positivity) hb).trans_eq (by ring)

lemma full_field_derivative_bound {F : Field} {t : ℝ} {x : Vec}
    (hF : DifferentiableAt ℝ F (t,x)) :
    ‖fderiv ℝ F (t,x)‖≤‖deriv (fun r => F (r,x)) t‖+‖fderiv ℝ (fun y => F (t,y)) x‖ := by
  let L := fderiv ℝ F (t,x)
  have ht := hF.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  have hx := hF.hasFDerivAt.comp x ((hasFDerivAt_const (c:=t) x).prodMk (hasFDerivAt_id x))
  have hd (v : Vec) : fderiv ℝ (fun y => F (t,y)) x v=L (0,v) := by
    exact congrArg (fun K : Vec →L[ℝ] Vec => K v) hx.fderiv
  have he : deriv (fun r => F (r,x)) t=L (1,0) := ht.deriv
  apply ContinuousLinearMap.opNorm_le_bound _ (add_nonneg (norm_nonneg _) (norm_nonneg _))
  intro p
  have hp : p=p.1 • (1,0)+(0,p.2) := by ext <;> simp
  have hr : L p=p.1 • deriv (fun r => F (r,x)) t+fderiv ℝ (fun y => F (t,y)) x p.2 := by
    rw [he,hd, hp, map_add, map_smul]
    simp
  change ‖L p‖≤_
  rw [hr]
  apply (norm_add_le _ _).trans
  rw [norm_smul]
  have h₁ : ‖p.1‖≤‖p‖ := norm_fst_le p
  have h₂ : ‖p.2‖≤‖p‖ := norm_snd_le p
  have ha := (fderiv ℝ (fun y => F (t,y)) x).le_opNorm p.2
  nlinarith [mul_le_mul_of_nonneg_right h₁ (norm_nonneg (deriv (fun r => F (r,x)) t)),
    mul_le_mul_of_nonneg_left h₂ (norm_nonneg (fderiv ℝ (fun y => F (t,y)) x))]

lemma current_norm_bound_of_momentum {f : Phase → ℝ} {P A : ℝ}
    (hA : 0≤A) (hfA : ∀ y v,|f (y,v)|≤A) (hP : ∀ y v,P<‖v‖ → f (y,v)=0) (x : Vec) :
    ‖current f x‖≤A*(volume (closedBall (0:Vec) P)).toReal := by
  rw [current,←setIntegral_eq_integral_of_forall_compl_eq_zero (s:=closedBall (0:Vec) P)]
  · exact (norm_setIntegral_le_of_norm_le_const (C:=A) ((isCompact_closedBall (0:Vec) P).measure_lt_top) (by
      intro v _
      rw [norm_smul,Real.norm_eq_abs]
      simpa only [mul_one] using
        mul_le_mul (hfA x v) (norm_velocity_lt_one v).le (norm_nonneg _) hA)).trans_eq (by rfl)
  · intro v hv
    have hh : P<‖v‖ := by simpa only [mem_closedBall,dist_zero_right,not_le] using hv
    rw [hP x v hh,zero_smul]

lemma maxwell_full_derivative_bound {s : Solution} {U t P A g : ℝ}
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (heq : EquationsBefore s U) (ht : 0<t) (htU : t<U)
    (hA : 0≤A) (hfA : ∀ y v,|s.f (t,y,v)|≤A)
    (hP : ∀ y v,P<‖v‖ → s.f (t,y,v)=0)
    (hb : ∀ y,‖fderiv ℝ (fun z => s.E (t,z)) y‖+‖fderiv ℝ (fun z => s.B (t,z)) y‖≤g)
    (x : Vec) :
    ‖fderiv ℝ s.E (t,x)‖≤7*g+A*(volume (closedBall (0:Vec) P)).toReal ∧
    ‖fderiv ℝ s.B (t,x)‖≤7*g+A*(volume (closedBall (0:Vec) P)).toReal := by
  have he := field_differentiableAt_positive hE ht x
  have hm := field_differentiableAt_positive hB ht x
  have hes : Differentiable ℝ (fun y => s.E (t,y)) := fun y =>
    (field_differentiableAt_positive hE ht y).comp y ((differentiableAt_const t).prodMk differentiableAt_id)
  have hbs : Differentiable ℝ (fun y => s.B (t,y)) := fun y =>
    (field_differentiableAt_positive hB ht y).comp y ((differentiableAt_const t).prodMk differentiableAt_id)
  have eqE := (heq t ht.le htU).2.1 x
  have eqB := (heq t ht.le htU).2.2.1 x
  rw [derivWithin_of_mem_nhds (Ici_mem_nhds ht)] at eqE eqB
  have hcb := curl_norm_le_gradient hbs x
  have hce := curl_norm_le_gradient hes x
  have hj := current_norm_bound_of_momentum (f:=fun z => s.f (t,z)) (P:=P) hA hfA hP x
  have hj0 : 0≤A*(volume (closedBall (0:Vec) P)).toReal := by positivity
  have heb : ‖deriv (fun r => s.E (r,x)) t‖≤6*‖fderiv ℝ (fun z => s.B (t,z)) x‖+A*(volume (closedBall (0:Vec) P)).toReal := by
    have hh : deriv (fun r => s.E (r,x)) t=curl (fun z => s.B (t,z)) x-current (fun z => s.f (t,z)) x := by
      have hh := sub_eq_iff_eq_add.mp eqE
      rw [hh]; abel
    rw [hh]
    exact (norm_sub_le _ _).trans (add_le_add hcb hj)
  have hbb : ‖deriv (fun r => s.B (r,x)) t‖≤6*‖fderiv ℝ (fun z => s.E (t,z)) x‖ := by
    have hh : deriv (fun r => s.B (r,x)) t=-curl (fun z => s.E (t,z)) x := eq_neg_of_add_eq_zero_left eqB
    simpa only [hh,norm_neg] using hce
  have hn := hb x
  constructor
  · have hh := full_field_derivative_bound he
    nlinarith [norm_nonneg (fderiv ℝ (fun z => s.E (t,z)) x),norm_nonneg (fderiv ℝ (fun z => s.B (t,z)) x)]
  · have hh := full_field_derivative_bound hm
    nlinarith [norm_nonneg (fderiv ℝ (fun z => s.E (t,z)) x),norm_nonneg (fderiv ℝ (fun z => s.B (t,z)) x)]

lemma spatial_field_lipschitz_of_gradient {F : Vec → Vec} {L : ℝ}
    (hF : Differentiable ℝ F) (hL : ∀ x,‖fderiv ℝ F x‖≤L) (x y : Vec) :
    ‖F x-F y‖≤L*‖x-y‖ := by
  exact (convex_univ : Convex ℝ (univ : Set Vec)).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => hF z) (fun z _ => hL z) (mem_univ y) (mem_univ x)

lemma norm_clm_le_nine_components (L : Vec →L[ℝ] Vec) {C : ℝ} (hC : 0≤C)
    (hb : ∀ i j : Fin 3, |L (basis j) i|≤C) : ‖L‖≤9*C := by
  have hb' (j : Fin 3) : ‖L (basis j)‖≤3*C := norm_le_three_of_coordinate_bound hC (fun i => hb i j)
  apply L.opNorm_le_bound (by positivity)
  intro v
  have he : L v=∑ j : Fin 3, v j • L (basis j) := by
    conv_lhs => rw [←sum_basis v]
    simp only [map_sum,map_smul]
  rw [he]
  calc
    _ ≤ ∑ j : Fin 3, ‖v j • L (basis j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin 3, ‖v‖*(3*C) := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul (norm_coordinate_le v j) (hb' j) (norm_nonneg _) (norm_nonneg v)
    _ = 9*C*‖v‖ := by simp; ring

end RVM
end

end OAI
