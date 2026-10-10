import Mathlib
import OAI.Analysis.Conductivity.Flux.AntisymmetricFlux

namespace OAI

noncomputable section

namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

section Direction
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}

@[simp] lemma direction_const (v x : E) (c : ℝ) : direction v (fun _ : E => c) x = 0 := by
  simp [direction]
lemma direction_add {f g : E → ℝ} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (v : E) : direction v (fun y => f y+g y) x = direction v f x+direction v g x := by
  simp only [direction,fderiv_fun_add hf hg,add_apply]
lemma direction_sub {f g : E → ℝ} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (v : E) : direction v (fun y => f y-g y) x = direction v f x-direction v g x := by
  simp only [direction,fderiv_fun_sub hf hg,sub_apply]
lemma direction_mul {f g : E → ℝ} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (v : E) : direction v (fun y => f y*g y) x = f x*direction v g x+g x*direction v f x := by
  simp only [direction,fderiv_fun_mul hf hg,add_apply,
    smul_apply,smul_eq_mul]
lemma direction_const_mul {f : E → ℝ} (hf : DifferentiableAt ℝ f x) (c : ℝ) (v : E) :
    direction v (fun y => c*f y) x = c*direction v f x := by
  rw [direction_mul (differentiableAt_const _) hf,direction_const,mul_zero,add_zero]
lemma direction_comp_real {f : E → ℝ} {g : ℝ → ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g (f x)) (v : E) :
    direction v (fun y => g (f y)) x = deriv g (f x)*direction v f x := by
  have hh := hg.hasDerivAt.comp_hasFDerivAt x hf.hasFDerivAt
  change (fderiv ℝ (g ∘ f) x) v = deriv g (f x)*direction v f x
  rw [hh.fderiv]
  simp only [smul_apply,smul_eq_mul]
  rfl
lemma direction_congr_nhds {f g : E → ℝ} (h : f =ᶠ[𝓝 x] g) (v : E) :
    direction v f x = direction v g x := by rw [direction,direction,h.fderiv_eq]
end Direction

@[simp] lemma direction_coord (i j : Fin 3) (x : Coord3) :
    direction (Pi.single i 1) (fun y : Coord3 => y j) x = if j=i then 1 else 0 := by
  let P : Coord3 →L[ℝ] ℝ := ContinuousLinearMap.proj j
  change (fderiv ℝ P x) (Pi.single i 1) = _
  rw [P.fderiv]
  change (Pi.single i 1 : Coord3) j = _
  simp [Pi.single_apply,eq_comm]

lemma direction_scalar_coord {f : ℝ → ℝ} (hf : Differentiable ℝ f) (i j : Fin 3) (x : Coord3) :
    direction (Pi.single i 1) (fun y : Coord3 => f (y j)) x =
      deriv f (x j)*(if j=i then 1 else 0) := by
  rw [direction_comp_real (differentiableAt_pi.1 differentiableAt_id j) (hf _) _,
    direction_coord]

def wedgePotential (a b : Fin 3) (H : Coord3 → ℝ) (i j : Fin 3) (x : Coord3) : ℝ :=
  (if i=a ∧ j=b then H x else 0) - (if j=a ∧ i=b then H x else 0)

lemma wedgePotential_flux (a b i : Fin 3) {H : Coord3 → ℝ} (hH : Differentiable ℝ H) (x : Coord3) :
    (∑ j, direction (Pi.single j 1) (wedgePotential a b H i j) x) =
      (if i=a then direction (Pi.single b 1) H x else 0) -
      (if i=b then direction (Pi.single a 1) H x else 0) := by
  have hd (i j : Fin 3) : direction (Pi.single j 1) (wedgePotential a b H i j) x =
      (if i=a ∧ j=b then direction (Pi.single j 1) H x else 0) -
      (if j=a ∧ i=b then direction (Pi.single j 1) H x else 0) := by
    unfold wedgePotential
    split <;> split <;>
      simp only [direction_sub (hH x) (hH x),
        direction_sub (differentiableAt_const _) (hH x), direction_const,sub_zero]
  simp_rw [hd]
  rw [Finset.sum_sub_distrib]
  congr 1
  · by_cases h : i=a <;> simp only [h,true_and,false_and,ite_true,ite_false] <;> simp
  · by_cases h : i=b <;> simp only [h,and_true,and_false,ite_true,ite_false] <;> simp

lemma direction_dilation {f : Coord3 → ℝ} (hf : Differentiable ℝ f)
    (s r : ℝ) (c v x : Coord3) :
    direction v (fun y => s*f (r • (y-c))) x = s*r*direction v f (r • (x-c)) := by
  have hl : HasFDerivAt (fun y : Coord3 => r • (y-c)) (r • ContinuousLinearMap.id ℝ Coord3) x :=
    ((hasFDerivAt_id x).sub_const c).const_smul r
  have hh : HasFDerivAt (fun y => s*f (r • (y-c)))
      (s • (fderiv ℝ f (r • (x-c))).comp (r • ContinuousLinearMap.id ℝ Coord3)) x :=
    ((hf _).hasFDerivAt.comp x hl).const_mul s
  change (fderiv ℝ (fun y => s*f (r • (y-c))) x) v = _
  rw [hh.fderiv]
  simp only [smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,map_smul,smul_eq_mul,direction]
  ring

lemma direction_sin_coord (r : ℝ) (i j : Fin 3) (x : Coord3) :
    direction (Pi.single i 1) (fun y : Coord3 => sin (r*y j)) x =
      r*cos (r*x j)*(if j=i then 1 else 0) := by
  have hh (t : ℝ) : HasDerivAt (fun t => sin (r*t)) (r*cos (r*t)) t := by
    convert ((hasDerivAt_id t).const_mul r).sin using 1 <;> simp [mul_comm]
  rw [direction_scalar_coord (fun t => (hh t).differentiableAt), (hh _).deriv]
lemma direction_cos_coord (r : ℝ) (i j : Fin 3) (x : Coord3) :
    direction (Pi.single i 1) (fun y : Coord3 => cos (r*y j)) x =
      -r*sin (r*x j)*(if j=i then 1 else 0) := by
  have hh (t : ℝ) : HasDerivAt (fun t => cos (r*t)) (-r*sin (r*t)) t := by
    convert ((hasDerivAt_id t).const_mul r).cos using 1 <;> simp [mul_comm]
  rw [direction_scalar_coord (fun t => (hh t).differentiableAt), (hh _).deriv]

lemma direction_scalar_sin {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (r : ℝ) (i a : Fin 3) (x : Coord3) :
    direction (Pi.single i 1) (fun y : Coord3 => f (y 0)*sin (r*y a)) x =
      f (x 0)*(r*cos (r*x a)*(if a=i then 1 else 0)) +
      sin (r*x a)*(deriv f (x 0)*(if (0:Fin 3)=i then 1 else 0)) := by
  rw [direction_mul (by fun_prop) (by fun_prop),direction_sin_coord,direction_scalar_coord hf]

def angularStream (F G : ℝ → ℝ) (a b : Fin 3) (x : Coord3) : ℝ :=
  F (x 0)/4*sin (4*x b)*sin (x a) -
    G (x 0)/2*cos (x a)*sin (x a)*sin (2*x b)

lemma angularStream_diff {F G : ℝ → ℝ} (hF : Differentiable ℝ F) (hG : Differentiable ℝ G)
    (a b : Fin 3) : Differentiable ℝ (angularStream F G a b) := by
  unfold angularStream
  fun_prop

lemma angularStream_b {F G : ℝ → ℝ} (hF : Differentiable ℝ F) (hG : Differentiable ℝ G)
    {a b : Fin 3} (hb : b≠0) (hab : a≠b) (x : Coord3) :
    direction (Pi.single b 1) (angularStream F G a b) x =
      F (x 0)*cos (4*x b)*sin (x a) - G (x 0)*cos (x a)*sin (x a)*cos (2*x b) := by
  have zF : direction (Pi.single b 1) (fun y : Coord3 => F (y 0)/4) x = 0 := by
    have he : (fun y : Coord3 => F (y 0)/4) = fun y => (1/4)*F (y 0) := by funext y; ring
    rw [he,direction_const_mul (by fun_prop),direction_scalar_coord hF]
    simp [Ne.symm hb]
  have zG : direction (Pi.single b 1) (fun y : Coord3 => G (y 0)/2) x = 0 := by
    have he : (fun y : Coord3 => G (y 0)/2) = fun y => (1/2)*G (y 0) := by funext y; ring
    rw [he,direction_const_mul (by fun_prop),direction_scalar_coord hG]
    simp [Ne.symm hb]
  have hsin : direction (Pi.single b 1) (fun y : Coord3 => sin (y a)) x = 0 := by
    simpa [hab] using direction_sin_coord 1 b a x
  have hcos : direction (Pi.single b 1) (fun y : Coord3 => cos (y a)) x = 0 := by
    simpa [hab] using direction_cos_coord 1 b a x
  unfold angularStream
  simp (disch := fun_prop) only [direction_sub,direction_mul,zF,zG,hsin,hcos,direction_sin_coord]
  simp only [ite_true,mul_zero,add_zero,zero_add]
  ring

lemma angularStream_a {F G : ℝ → ℝ} (hF : Differentiable ℝ F) (hG : Differentiable ℝ G)
    {a b : Fin 3} (ha : a≠0) (hab : a≠b) (x : Coord3) :
    direction (Pi.single a 1) (angularStream F G a b) x =
      F (x 0)/4*sin (4*x b)*cos (x a) -
        G (x 0)/2*((cos (x a))^2-(sin (x a))^2)*sin (2*x b) := by
  have zF : direction (Pi.single a 1) (fun y : Coord3 => F (y 0)/4) x = 0 := by
    have he : (fun y : Coord3 => F (y 0)/4) = fun y => (1/4)*F (y 0) := by funext y; ring
    rw [he,direction_const_mul (by fun_prop),direction_scalar_coord hF]
    simp [Ne.symm ha]
  have zG : direction (Pi.single a 1) (fun y : Coord3 => G (y 0)/2) x = 0 := by
    have he : (fun y : Coord3 => G (y 0)/2) = fun y => (1/2)*G (y 0) := by funext y; ring
    rw [he,direction_const_mul (by fun_prop),direction_scalar_coord hG]
    simp [Ne.symm ha]
  have hsin : direction (Pi.single a 1) (fun y : Coord3 => sin (y a)) x = cos (x a) := by
    simpa using direction_sin_coord 1 a a x
  have hcos : direction (Pi.single a 1) (fun y : Coord3 => cos (y a)) x = -sin (x a) := by
    simpa using direction_cos_coord 1 a a x
  unfold angularStream
  simp (disch := fun_prop) only [direction_sub,direction_mul,zF,zG,hsin,hcos,direction_sin_coord]
  simp only [Ne.symm hab,ite_false,mul_zero,add_zero,zero_add]
  ring

end ScalarConductivity

end

end OAI
