import OAI.Analysis.AllenCahn.HessianControl

namespace OAI

noncomputable section
namespace DeGiorgi
open scoped ContDiff

def defectRoot {n : ℕ} (v : Space n → ℝ) (x : Space n) : ℝ :=
  Real.exp ((1 / 2 : ℝ) * Real.log (diffuseDefect v x))

lemma defectRoot_pos {n : ℕ} (v : Space n → ℝ) (x : Space n) : 0 < defectRoot v x :=
  Real.exp_pos _

lemma defectRoot_sq {n : ℕ} {v : Space n → ℝ} {x : Space n}
    (hp : 0 < diffuseDefect v x) : defectRoot v x ^ 2 = diffuseDefect v x := by
  rw [defectRoot, pow_two, ← Real.exp_add]
  convert Real.exp_log hp using 1; congr 1; ring

lemma defectRoot_eq_sqrt {n : ℕ} {v : Space n → ℝ} {x : Space n}
    (hp : 0 < diffuseDefect v x) : defectRoot v x = Real.sqrt (diffuseDefect v x) := by
  nlinarith [defectRoot_pos v x, Real.sqrt_nonneg (diffuseDefect v x),
    Real.sq_sqrt hp.le, defectRoot_sq hp]

lemma defectRoot_smooth {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1)
    (hp : ∀ x, 0 < diffuseDefect v x) : ContDiff ℝ ∞ (defectRoot v) :=
  (contDiff_const.mul ((diffuseDefect_smooth hv hi).log (fun x => (hp x).ne'))).exp

lemma defectRoot_gradient {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1)
    (hp : ∀ x, 0 < diffuseDefect v x) (x : Space n) :
    gradient (defectRoot v) x = ((1 / 2 : ℝ) * defectRoot v x) •
      gradient (fun y => Real.log (diffuseDefect v y)) x := by
  have hh := ((diffuseDefect_smooth hv hi).log fun x => (hp x).ne').differentiable (by simp)
  change gradient (fun y => Real.exp ((1/2 : ℝ) * Real.log (diffuseDefect v y))) x = _
  simp only [gradient, defectRoot,
    fderiv_exp ((differentiable_const (1/2 : ℝ)).fun_mul hh x),
    fderiv_const_mul (hh x), map_smul, smul_smul]
  congr 1
  ring

lemma defectRoot_drift {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (hAC : AllenCahn v)
    (hp : ∀ x, 0 < diffuseDefect v x) (x : Space n) :
    Laplacian.laplacian (defectRoot v) x - fderiv ℝ (defectRoot v) x (diffuseDrift v x) =
      defectRoot v x * ((1 / 2 : ℝ) * (defectSource v x / diffuseDefect v x) -
        (1 / 4 : ℝ) * ‖gradient (fun y => Real.log (diffuseDefect v y)) x‖ ^ 2) := by
  let h := fun y => Real.log (diffuseDefect v y)
  have hh : ContDiff ℝ ∞ h := (diffuseDefect_smooth hv hi).log (fun y => (hp y).ne')
  have hd := hh.differentiable (by simp)
  have hL := (positive_defect_log_bounds hv hi hAC hp).1 x
  have hg : gradient (fun y => (1 / 2 : ℝ) * h y) x = (1 / 2 : ℝ) • gradient h x := by
    simp only [gradient, fderiv_const_mul (hd x), map_smul]
  change Laplacian.laplacian (fun y => Real.exp ((1 / 2 : ℝ) * h y)) x - _ = _
  rw [laplacian_exp (contDiff_const.mul (smooth_C2 hh)), laplacian_fun_const_mul (smooth_C2 hh),
    hg, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1/2)]
  change _ - fderiv ℝ (fun y => Real.exp ((1 / 2 : ℝ) * h y)) x (diffuseDrift v x) = _
  rw [fderiv_exp ((differentiable_const (1/2 : ℝ)).fun_mul hd x),
    fderiv_const_mul (hd x), smul_apply, smul_apply, smul_eq_mul, smul_eq_mul]
  dsimp only [h] at hL
  change _ = Real.exp ((1 / 2 : ℝ) * h x) * _
  dsimp only [h] at *
  rw [sub_eq_iff_eq_add.mp hL]
  ring

lemma defectRoot_bounds {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (hAC : AllenCahn v)
    (hp : ∀ x, 0 < diffuseDefect v x) (x : Space n) :
    ‖gradient (defectRoot v) x‖ ≤ relativeDefectConstant n * defectRoot v x ∧
    |Laplacian.laplacian (defectRoot v) x - fderiv ℝ (defectRoot v) x (diffuseDrift v x)| ≤
      (defectSourceConstant n + relativeDefectConstant n ^ 2) * defectRoot v x := by
  have hb := positive_defect_log_bounds hv hi hAC hp
  have hC := relativeDefectConstant_pos n
  have hS := defectSourceConstant_pos n
  have hr : |defectSource v x / diffuseDefect v x| ≤ defectSourceConstant n := by
    rw [abs_div, abs_of_pos (hp x)]
    exact (div_le_iff₀ (hp x)).mpr ((defectSource_bounds hv hi hAC).1 x)
  constructor
  · rw [defectRoot_gradient hv hi hp, norm_smul, Real.norm_eq_abs,
      abs_of_pos (mul_pos (by norm_num) (defectRoot_pos v x))]
    have H := mul_le_mul_of_nonneg_left (hb.2.1 x) (defectRoot_pos v x).le
    nlinarith [mul_nonneg (defectRoot_pos v x).le
      (norm_nonneg (gradient (fun y => Real.log (diffuseDefect v y)) x))]
  · rw [defectRoot_drift hv hi hAC hp, abs_mul, abs_of_pos (defectRoot_pos v x)]
    have H := abs_sub ((1/2 : ℝ) * (defectSource v x / diffuseDefect v x))
      ((1/4 : ℝ) * ‖gradient (fun y => Real.log (diffuseDefect v y)) x‖ ^ 2)
    have Hpos : 0 ≤ (1/4 : ℝ) * ‖gradient (fun y => Real.log (diffuseDefect v y)) x‖ ^ 2 := by positivity
    have He : |(1/2 : ℝ) * (defectSource v x / diffuseDefect v x)| =
        (1/2 : ℝ) * |defectSource v x / diffuseDefect v x| := by rw [abs_mul]; norm_num
    rw [He, abs_of_nonneg Hpos] at H
    have Hg := (sq_le_sq₀ (norm_nonneg _) hC.le).mpr (hb.2.1 x)
    have hh : |(1/2 : ℝ) * (defectSource v x / diffuseDefect v x) -
        (1/4 : ℝ) * ‖gradient (fun y => Real.log (diffuseDefect v y)) x‖ ^ 2| ≤
          defectSourceConstant n + relativeDefectConstant n ^ 2 := by nlinarith
    nlinarith [defectRoot_pos v x]

lemma defectRoot_le_one {n : ℕ} {v : Space n → ℝ} (hp : ∀ x, 0 < diffuseDefect v x) (x : Space n) :
    defectRoot v x ≤ 1 := by
  nlinarith [defectRoot_sq (hp x), defectRoot_pos v x, diffuseDefect_le_one v x]

lemma normalized_tensor_square_bounds {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (hAC : AllenCahn v)
    (hp : ∀ x, 0 < diffuseDefect v x) (x : Space n) :
    Real.sqrt (hessianSquare v x) ≤ Real.sqrt (tensorBernsteinConstant n + 3) * defectRoot v x ∧
    Real.sqrt (tensorDerivativeSquare v x) ≤ Real.sqrt (derivativeDefectConstant n) * defectRoot v x := by
  have hB : 0 ≤ tensorBernsteinConstant n + 3 := by dsimp [tensorBernsteinConstant]; positivity
  have he : Real.sqrt (diffuseDefect v x) = defectRoot v x := (defectRoot_eq_sqrt (hp x)).symm
  constructor
  · have H := Real.sqrt_le_sqrt (hessianSquare_le_defect hv hi hAC x)
    rwa [Real.sqrt_mul hB, he] at H
  · have H := Real.sqrt_le_sqrt (tensorDerivativeSquare_le_defect hv hi hAC x)
    rwa [Real.sqrt_mul (derivativeDefectConstant_pos n).le, he] at H

def normalizedTensorSourceConstant (n : ℕ) : ℝ :=
  tensorCoeffConstant n * (1 + 6 * n) *
    (1 + Real.sqrt (tensorBernsteinConstant n + 3) + Real.sqrt (derivativeDefectConstant n))

def normalizedTensorSecondConstant (n : ℕ) : ℝ :=
  2 * (2 * Real.sqrt (derivativeDefectConstant n) +
    (normalizedTensorSourceConstant n + Real.sqrt (derivativeDefectConstant n) *
      (defectSourceConstant n + relativeDefectConstant n ^ 2)) + 3) *
    (2 * Real.sqrt 2 + 2 * relativeDefectConstant n + 1) +
    Real.sqrt (derivativeDefectConstant n) * relativeDefectConstant n

lemma normalizedTensorSourceConstant_nonneg (n : ℕ) : 0 ≤ normalizedTensorSourceConstant n := by
  have hC := tensorCoeffConstant_pos n
  dsimp [normalizedTensorSourceConstant]; positivity

lemma normalizedTensorSecondConstant_nonneg (n : ℕ) : 0 ≤ normalizedTensorSecondConstant n := by
  have hC := relativeDefectConstant_pos n
  have hS := defectSourceConstant_pos n
  have hT := normalizedTensorSourceConstant_nonneg n
  dsimp [normalizedTensorSecondConstant]; positivity

theorem inverseHessian_second_relative {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (hAC : AllenCahn v)
    (hp : ∀ x, 0 < diffuseDefect v x) (i j k : Fin n) (x : Space n) :
    ‖gradient (coordDeriv (inverseHessian v i j) k) x‖ ≤
      normalizedTensorSecondConstant n * Real.sqrt (diffuseDefect v x) := by
  have hb (y) := normalized_tensor_square_bounds hv hi hAC hp y
  have hfb (y) : |coordDeriv (inverseHessian v i j) k y| ≤
      Real.sqrt (derivativeDefectConstant n) * defectRoot v y :=
    (inverseHessian_deriv_abs_le_sqrt v i j k y).trans (hb y).2
  have hfL (y) : |Laplacian.laplacian (coordDeriv (inverseHessian v i j) k) y -
      fderiv ℝ (coordDeriv (inverseHessian v i j) k) y (diffuseDrift v y)| ≤
        normalizedTensorSourceConstant n * defectRoot v y := by
    apply (inverseHessian_deriv_drift_bound hv hi hAC i j k y).trans
    have hD : diffuseDefect v y ≤ defectRoot v y := by
      nlinarith [defectRoot_sq (hp y), defectRoot_pos v y, defectRoot_le_one hp y]
    have hsum := add_le_add (add_le_add hD (hb y).1) (hb y).2
    have hC : 0 ≤ tensorCoeffConstant n * (1 + 6 * n) := by
      have := tensorCoeffConstant_pos n; positivity
    have H := mul_le_mul_of_nonneg_left hsum hC
    dsimp [normalizedTensorSourceConstant]
    nlinarith
  have H := carrier_gradient_estimate
    (smooth_C2 (coordDeriv_smooth (inverseHessian_smooth hv hi i j) k))
    (smooth_C2 (defectRoot_smooth hv hi hp)) (defectRoot_pos v) (diffuseDrift v)
    (Real.sqrt_nonneg (derivativeDefectConstant n)) (normalizedTensorSourceConstant_nonneg n)
    (show 0 ≤ 2 * Real.sqrt 2 by positivity) (relativeDefectConstant_pos n).le
    (add_nonneg (defectSourceConstant_pos n).le (sq_nonneg _))
    hfb (diffuseDrift_bound (smooth_C2 hv) hi hAC)
    (fun y => (defectRoot_bounds hv hi hAC hp y).1) hfL
    (fun y => (defectRoot_bounds hv hi hAC hp y).2) x
  rw [defectRoot_eq_sqrt (hp x)] at H
  exact H

def coordinateJet {n : ℕ} (f : Space n → ℝ) : List (Fin n) → Space n → ℝ
  | [] => f
  | i :: l => coordDeriv (coordinateJet f l) i

lemma coordinateJet_smooth {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (l : List (Fin n)) : ContDiff ℝ ∞ (coordinateJet f l) := by
  induction l with
  | nil => exact hf
  | cons i l ih => exact coordDeriv_smooth ih i

lemma coordinateJet_laplacian {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (l : List (Fin n)) :
    Laplacian.laplacian (coordinateJet f l) = coordinateJet (Laplacian.laplacian f) l := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    funext x
    change Laplacian.laplacian (coordDeriv (coordinateJet f l) i) x = _
    rw [laplacian_coordDeriv (coordinateJet_smooth hf l), ih]
    rfl

def jetSplits {α : Type*} : List α → List (List α × List α)
  | [] => [([], [])]
  | i :: l => (jetSplits l).map (fun p => (i :: p.1, p.2)) ++
      (jetSplits l).map (fun p => (p.1, i :: p.2))

lemma jetSplits_length {α : Type*} (l : List α) (p : List α × List α)
    (hp : p ∈ jetSplits l) : p.1.length ≤ l.length ∧ p.2.length ≤ l.length := by
  induction l generalizing p with
  | nil => simp [jetSplits] at hp; subst p; simp
  | cons i l ih =>
    simp only [jetSplits, List.mem_append, List.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · obtain ⟨h1,h2⟩ := ih q hq
      simp only [List.length_cons]; omega
    · obtain ⟨h1,h2⟩ := ih q hq
      simp only [List.length_cons]; omega

lemma differentiable_list_sum {n : ℕ} {α : Type*} (l : List α) (f : α → Space n → ℝ)
    (hf : ∀ a ∈ l, Differentiable ℝ (f a)) :
    Differentiable ℝ (fun y => (l.map (fun a => f a y)).sum) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hf a (by simp)).add (ih (fun b hb => hf b (by simp [hb])))

lemma coordDeriv_list_sum {n : ℕ} {α : Type*} (l : List α) (f : α → Space n → ℝ)
    (hf : ∀ a ∈ l, Differentiable ℝ (f a)) (i : Fin n) (x : Space n) :
    coordDeriv (fun y => (l.map (fun a => f a y)).sum) i x =
      (l.map (fun a => coordDeriv (f a) i x)).sum := by
  induction l with
  | nil => simp [coordDeriv]
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [coordDeriv_add (hf a (by simp))
      (differentiable_list_sum l f (fun b hb => hf b (by simp [hb]))),
      ih (fun b hb => hf b (by simp [hb]))]

lemma coordinateJet_mul {n : ℕ} {f g : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (l : List (Fin n)) (x : Space n) :
    coordinateJet (fun y => f y*g y) l x =
      ((jetSplits l).map (fun p => coordinateJet f p.1 x * coordinateJet g p.2 x)).sum := by
  induction l generalizing x with
  | nil => simp [coordinateJet, jetSplits]
  | cons i l ih =>
    have he : coordinateJet (fun y => f y*g y) l = fun y =>
        ((jetSplits l).map (fun p => coordinateJet f p.1 y * coordinateJet g p.2 y)).sum := funext ih
    change coordDeriv (coordinateJet (fun y => f y*g y) l) i x = _
    rw [he, coordDeriv_list_sum]
    · simp only [jetSplits, List.map_append, List.map_map, List.sum_append, Function.comp_def,
        coordinateJet]
      rw [← List.sum_map_add]
      apply congrArg List.sum
      apply List.map_congr_left
      intro p hp
      rw [coordDeriv_mul ((coordinateJet_smooth hf p.1).differentiable (by simp))
        ((coordinateJet_smooth hg p.2).differentiable (by simp))]
      ring
    · intro p hp
      exact ((coordinateJet_smooth hf p.1).mul (coordinateJet_smooth hg p.2)).differentiable (by simp)

lemma coordinateJet_zero {n : ℕ} (l : List (Fin n)) :
    coordinateJet (fun _ : Space n => (0 : ℝ)) l = fun _ => 0 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    funext x
    change coordDeriv (coordinateJet (fun _ => 0) l) i x = 0
    rw [ih]
    simp [coordDeriv]

lemma coordinateJet_const {n : ℕ} (a : ℝ) (l : List (Fin n)) :
    coordinateJet (fun _ : Space n => a) l = fun _ => if l=[] then a else 0 := by
  induction l with
  | nil => simp [coordinateJet]
  | cons i l ih =>
    funext x
    change coordDeriv (coordinateJet (fun _ => a) l) i x = 0
    rw [ih]
    by_cases hl : l=[]
    · simp only [hl]
      simp [coordDeriv]
    · simp only [ite_eq_right hl]
      simp [coordDeriv]

lemma coordinateJet_add {n : ℕ} {f g : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (l : List (Fin n)) :
    coordinateJet (fun x => f x+g x) l = fun x => coordinateJet f l x+coordinateJet g l x := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    funext x
    change coordDeriv (coordinateJet (fun x => f x+g x) l) i x = _
    rw [ih, coordDeriv_add ((coordinateJet_smooth hf l).differentiable (by simp))
      ((coordinateJet_smooth hg l).differentiable (by simp))]
    rfl

lemma coordinateJet_const_mul {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (a : ℝ) (l : List (Fin n)) :
    coordinateJet (fun x => a*f x) l = fun x => a*coordinateJet f l x := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    funext x
    change coordDeriv (coordinateJet (fun x => a*f x) l) i x = _
    rw [ih]
    simp only [coordinateJet, coordDeriv,
      fderiv_const_mul ((coordinateJet_smooth hf l).differentiable (by simp) x),
      smul_apply, smul_eq_mul]

lemma coordinateJet_sum {n : ℕ} {ι : Type*} (s : Finset ι)
    {f : ι → Space n → ℝ} (hf : ∀ i ∈ s, ContDiff ℝ ∞ (f i)) (l : List (Fin n)) :
    coordinateJet (fun x => ∑ i ∈ s, f i x) l = fun x => ∑ i ∈ s, coordinateJet (f i) l x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using coordinateJet_zero l
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [coordinateJet_add (hf i (by simp)) (ContDiff.sum (fun j hj => hf j (by simp [hj]))),
      ih (fun j hj => hf j (by simp [hj]))]

lemma coordinateJet_coordDeriv {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (l : List (Fin n)) (i : Fin n) :
    coordinateJet (coordDeriv f i) l = coordDeriv (coordinateJet f l) i := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    change coordDeriv (coordinateJet (coordDeriv f i) l) j = _
    rw [ih, coordDeriv_comm (smooth_C2 (coordinateJet_smooth hf l))]
    rfl

def jetRestSplits {α : Type*} : List α → List (List α × List α)
  | [] => []
  | i::l => (jetSplits l).map (fun p => (i::p.1,p.2)) ++
      (jetRestSplits l).map (fun p => (p.1,i::p.2))

lemma jetSplits_perm_rest {α : Type*} (l : List α) :
    (jetSplits l).Perm (([],l)::jetRestSplits l) := by
  induction l with
  | nil => simp [jetSplits, jetRestSplits]
  | cons i l ih =>
    simp only [jetSplits, jetRestSplits]
    have H := List.Perm.append_left ((jetSplits l).map (fun p => (i::p.1,p.2)))
      (ih.map (fun p => (p.1,i::p.2)))
    simp only [List.map_cons] at H
    exact H.trans List.perm_middle

lemma jetRestSplits_length {α : Type*} (l : List α) (p : List α × List α)
    (hp : p ∈ jetRestSplits l) : p.1.length ≤ l.length ∧ p.2.length < l.length := by
  induction l generalizing p with
  | nil => simp [jetRestSplits] at hp
  | cons i l ih =>
    simp only [jetRestSplits, List.mem_append, List.mem_map] at hp
    rcases hp with ⟨q,hq,rfl⟩ | ⟨q,hq,rfl⟩
    · obtain ⟨h1,h2⟩ := jetSplits_length l q hq
      simp only [List.length_cons]; omega
    · obtain ⟨h1,h2⟩ := ih q hq
      simp only [List.length_cons]; omega

end DeGiorgi
end

end OAI
