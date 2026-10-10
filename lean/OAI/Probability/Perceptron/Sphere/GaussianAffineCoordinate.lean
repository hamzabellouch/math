import Mathlib
import OAI.Probability.Perceptron.Variational.GaussianMarkRecursion
import OAI.Probability.Perceptron.Variational.TensorFeatures

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

variable {I : Type} [Fintype I] [DecidableEq I]

def eraseMarkCoordinate (i : I) (x : EuclideanSpace ℝ I) : EuclideanSpace ℝ I :=
  WithLp.toLp 2 (Function.update (fun j => x j) i 0)

omit [Fintype I] in
lemma eraseMarkCoordinate_continuous (i : I) : Continuous (eraseMarkCoordinate i) := by
  unfold eraseMarkCoordinate
  fun_prop

lemma pi_coordinate_rest_indep (μ : I→Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (i : I) :
    IndepFun (fun x : I→ℝ => Function.update x i 0) (fun x => x i) (Measure.pi μ) := by
  have hi : iIndepFun (fun i (x : I→ℝ) => x i) (Measure.pi μ) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hh := hi.indepFun_finset (Finset.univ.erase i) {i} (by simp) (fun j => measurable_pi_apply j)
  let R : ({j // j∈Finset.univ.erase i}→ℝ)→I→ℝ := fun x j =>
    if hj : j=i then 0 else x ⟨j,by simp [hj]⟩
  have hR : Measurable R := by
    apply Measurable.of_eval
    intro j
    dsimp [R]
    split_ifs <;> fun_prop
  have hr := hh.comp hR (measurable_pi_apply (⟨i,by simp⟩ : ({i}:Finset I)))
  convert hr using 1
  · funext x j
    by_cases hj : j=i
    · subst j
      simp [R]
    · simp [R,hj]
  · rfl

lemma gaussian_coordinate_rest_indep (i : I) :
    IndepFun (eraseMarkCoordinate i) (fun x : EuclideanSpace ℝ I => x i)
      (stdGaussian (EuclideanSpace ℝ I)) := by
  have hp := (pi_coordinate_rest_indep (fun _ => gaussianReal 0 1) i).comp
    (by fun_prop : Measurable (WithLp.toLp 2 : (I→ℝ)→EuclideanSpace ℝ I)) measurable_id
  have he := (eraseMarkCoordinate_continuous i).measurable
  have hx : Measurable (fun x : EuclideanSpace ℝ I => x i) := by fun_prop
  have ht : Measurable (WithLp.toLp 2 : (I→ℝ)→EuclideanSpace ℝ I) := by fun_prop
  apply (indepFun_iff_map_prod_eq_prod_map_map he.aemeasurable hx.aemeasurable).mpr
  rw [← map_pi_eq_stdGaussian,
    Measure.map_map (he.prodMk hx) ht, Measure.map_map he ht, Measure.map_map hx ht]
  convert hp.map_prod_eq_prod_map_map
    (ht.comp (Measurable.of_eval (fun coordinate => by fun_prop))).aemeasurable
    (measurable_pi_apply i).aemeasurable using 1 <;> rfl

omit [DecidableEq I] in
lemma stdGaussian_coordinate_law (i : I) :
    (stdGaussian (EuclideanSpace ℝ I)).map (fun x => x i)=gaussianReal 0 1 := by
  rw [← map_pi_eq_stdGaussian,Measure.map_map (by fun_prop) (by fun_prop)]
  exact (measurePreserving_eval (fun _ => gaussianReal 0 1) i).map_eq

omit [DecidableEq I] in
lemma gaussian_coordinate_cgf (i : I) (c t : ℝ) :
    cgf (fun x : EuclideanSpace ℝ I => c*x i) (stdGaussian (EuclideanSpace ℝ I)) t=
      c^2*t^2/2 := by
  have he : cgf (fun x : EuclideanSpace ℝ I => c*x i) (stdGaussian (EuclideanSpace ℝ I)) t=
      cgf (fun x : EuclideanSpace ℝ I => x i) (stdGaussian (EuclideanSpace ℝ I)) (t*c) := by
    simp only [cgf,mgf,mul_assoc]
  have hlaw : HasLaw (fun x : EuclideanSpace ℝ I => x i) (gaussianReal 0 1)
      (stdGaussian (EuclideanSpace ℝ I)) := ⟨by fun_prop, stdGaussian_coordinate_law i⟩
  rw [he,cgf_gaussianReal hlaw]
  simp only [zero_mul,NNReal.coe_one,one_mul]
  ring

omit [Fintype I] in
lemma eraseMarkCoordinate_add (i : I) (x y : EuclideanSpace ℝ I) :
    eraseMarkCoordinate i (x+y)=eraseMarkCoordinate i x+eraseMarkCoordinate i y := by
  ext j
  by_cases hj : j=i
  · subst j; simp [eraseMarkCoordinate]
  · simp [eraseMarkCoordinate,Function.update_of_ne hj]

lemma eraseMarkCoordinate_diagonal (i : I) (a : I→ℝ) (x : EuclideanSpace ℝ I) :
    eraseMarkCoordinate i (diagonalMark a x)=diagonalMark a (eraseMarkCoordinate i x) := by
  ext j
  by_cases hj : j=i
  · subst j; simp [eraseMarkCoordinate]
  · simp [eraseMarkCoordinate,Function.update_of_ne hj]

omit [DecidableEq I] in
lemma gaussian_coordinate_mean (i : I) :
    (∫ x : EuclideanSpace ℝ I, x i ∂stdGaussian (EuclideanSpace ℝ I))=0 := by
  have H := integral_map (μ := stdGaussian (EuclideanSpace ℝ I))
    (φ := fun x => x i) (f := id) (by fun_prop) (by fun_prop)
  rw [stdGaussian_coordinate_law] at H
  simpa using H.symm.trans integral_id_gaussianReal

lemma all_exp_indep_add {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X Y : Ω→ℝ} (hi : IndepFun X Y μ)
    (hX : Measurable X) (hY : Measurable Y)
    (hXI : ∀ t:ℝ, Integrable (fun x => Real.exp (t*X x)) μ)
    (hYI : ∀ t:ℝ, Integrable (fun x => Real.exp (t*Y x)) μ) :
    ∀ t:ℝ, Integrable (fun x => Real.exp (t*(X x+Y x))) μ := by
  intro t
  convert
    (hi.comp₀ hX.aemeasurable hY.aemeasurable
      (by fun_prop : AEMeasurable (fun value:ℝ => Real.exp (t*value)) (μ.map X))
      (by fun_prop : AEMeasurable (fun value:ℝ => Real.exp (t*value)) (μ.map Y))).integrable_mul
      (hXI t) (hYI t) using 1
  funext x
  simp [mul_add,Real.exp_add,Function.comp_def]

lemma entropicMean_indep_add {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X Y : Ω→ℝ} (hi : IndepFun X Y μ)
    (hX : Measurable X) (hY : Measurable Y)
    (hXI : ∀ t:ℝ, Integrable (fun x => Real.exp (t*X x)) μ)
    (hYI : ∀ t:ℝ, Integrable (fun x => Real.exp (t*Y x)) μ) (b : ℝ) :
    entropicMean μ b (fun x => X x+Y x)=entropicMean μ b X+entropicMean μ b Y := by
  by_cases hb : b=0
  · subst b
    rw [entropicMean_zero μ (all_exp_indep_add hi hX hY hXI hYI),
      entropicMean_zero μ hXI,entropicMean_zero μ hYI]
    exact integral_add (integrable_of_all_exp μ hXI) (integrable_of_all_exp μ hYI)
  · rw [entropicMean_eq_div μ (all_exp_indep_add hi hX hY hXI hYI) hb,
      entropicMean_eq_div μ hXI hb,entropicMean_eq_div μ hYI hb]
    change cgf (X+Y) μ b / b = _
    rw [hi.cgf_add (hXI b) (hYI b),add_div]

omit [DecidableEq I] in
lemma gaussian_coordinate_entropic (i : I) (c b : ℝ) :
    entropicMean (stdGaussian (EuclideanSpace ℝ I)) b (fun x => c*x i)=b*c^2/2 := by
  have hL := (c • EuclideanSpace.proj (𝕜 := ℝ) i).lipschitzWith
  have hI : ∀ t:ℝ, Integrable (fun x : EuclideanSpace ℝ I => Real.exp (t*(c*x i)))
      (stdGaussian (EuclideanSpace ℝ I)) := by
    intro t
    simpa using gaussian_integrable_exp_lipschitz _ hL t 1 (0:EuclideanSpace ℝ I)
  by_cases hb : b=0
  · subst b
    rw [entropicMean_zero _ hI,integral_const_mul,gaussian_coordinate_mean]
    ring
  · rw [entropicMean_eq_div _ hI hb,gaussian_coordinate_cgf]
    field_simp

lemma gaussianLinearEntropic_free_coordinate (i : I) (a : I→ℝ)
    {f : EuclideanSpace ℝ I→ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (hfree : ∀ x, f (eraseMarkCoordinate i x)=f x) (b c : ℝ) (x : EuclideanSpace ℝ I) :
    gaussianLinearEntropic (stdGaussian (EuclideanSpace ℝ I)) b (diagonalMark a)
      (fun y => f y+c*y i) x=
      gaussianLinearEntropic (stdGaussian (EuclideanSpace ℝ I)) b (diagonalMark a) f x+
        c*x i+b*c^2*(a i)^2/2 := by
  let X := fun y : EuclideanSpace ℝ I => f (x+diagonalMark a y)
  let Y := fun y : EuclideanSpace ℝ I => c*a i*y i
  have hx : Measurable X := hf.continuous.measurable.comp (by fun_prop)
  have hy : Measurable Y := by fun_prop
  have hXI := fun t => gaussian_integrable_exp_linear_shift (stdGaussian (EuclideanSpace ℝ I)) hf (diagonalMark a) t x
  have hYI : ∀ t:ℝ, Integrable (fun y => Real.exp (t*Y y)) (stdGaussian (EuclideanSpace ℝ I)) := by
    intro t
    simpa [Y] using gaussian_integrable_exp_lipschitz _
      ((c*a i) • EuclideanSpace.proj (𝕜 := ℝ) i).lipschitzWith t 1 (0:EuclideanSpace ℝ I)
  have hi : IndepFun X Y (stdGaussian (EuclideanSpace ℝ I)) := by
    have H := (gaussian_coordinate_rest_indep i).comp
      (hf.continuous.measurable.comp (by fun_prop : Measurable (fun y => x+diagonalMark a y)))
      (by fun_prop : Measurable (fun r:ℝ => c*a i*r))
    convert H using 1
    · funext y
      dsimp [X,Function.comp_def]
      rw [← hfree (x+diagonalMark a y),← hfree (x+diagonalMark a (eraseMarkCoordinate i y))]
      congr 1
      rw [eraseMarkCoordinate_add,eraseMarkCoordinate_add,
        eraseMarkCoordinate_diagonal,eraseMarkCoordinate_diagonal]
      congr 2
      ext j
      by_cases hj : j=i
      · subst j; simp [eraseMarkCoordinate]
      · simp [eraseMarkCoordinate,Function.update_of_ne hj]
    · rfl
  have he : (fun y => f (x+diagonalMark a y)+c*(x+diagonalMark a y) i)=
      (fun y => (X y+Y y)+c*x i) := by
    funext y
    change f (x+diagonalMark a y)+c*(x i+a i*y i)=(f (x+diagonalMark a y)+c*a i*y i)+c*x i
    ring
  simp only [gaussianLinearEntropic,he]
  rw [entropicMean_add_const _ (all_exp_indep_add hi hx hy hXI hYI),
    entropicMean_indep_add hi hx hy hXI hYI]
  dsimp only [Y]
  rw [gaussian_coordinate_entropic]
  dsimp only [X]
  ring

omit [DecidableEq I] in
lemma gaussianLinearEntropic_add_const (a : I→ℝ)
    {f : EuclideanSpace ℝ I→ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (b c : ℝ) :
    gaussianLinearEntropic (stdGaussian (EuclideanSpace ℝ I)) b (diagonalMark a)
      (fun y => f y+c)=fun x =>
      gaussianLinearEntropic (stdGaussian (EuclideanSpace ℝ I)) b (diagonalMark a) f x+c := by
  funext x
  exact entropicMean_add_const _
    (fun t => gaussian_integrable_exp_linear_shift _ hf (diagonalMark a) t x) b c

lemma gaussianLinearEntropic_preserves_free (i : I) (a : I→ℝ)
    {f : EuclideanSpace ℝ I→ℝ} (hfree : ∀ x, f (eraseMarkCoordinate i x)=f x) (b : ℝ) :
    ∀ x, gaussianLinearEntropic (stdGaussian (EuclideanSpace ℝ I)) b (diagonalMark a) f
        (eraseMarkCoordinate i x)=
      gaussianLinearEntropic (stdGaussian (EuclideanSpace ℝ I)) b (diagonalMark a) f x := by
  intro x
  unfold gaussianLinearEntropic
  congr 1
  funext y
  rw [← hfree (eraseMarkCoordinate i x+diagonalMark a y),← hfree (x+diagonalMark a y)]
  congr 1
  ext j
  by_cases hj : j=i
  · subst j; simp [eraseMarkCoordinate]
  · simp [eraseMarkCoordinate,Function.update_of_ne hj]

def diagonalWord (l : List (ℝ×(I→ℝ))) : List (ℝ×(EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)) :=
  l.map (fun a => (a.1,diagonalMark a.2))

omit [DecidableEq I] in
lemma diagonalWord_nonneg (l : List (ℝ×(I→ℝ))) (hl : ∀ a∈l, 0≤a.1) :
    ∀ a∈diagonalWord l, 0≤a.1 := by
  intro a ha
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
  exact hl b hb

lemma gaussianLinearBackward_preserves_free (i : I) (l : List (ℝ×(I→ℝ)))
    {f : EuclideanSpace ℝ I→ℝ} (hfree : ∀ x, f (eraseMarkCoordinate i x)=f x) :
    ∀ x, gaussianLinearBackward (stdGaussian (EuclideanSpace ℝ I)) (diagonalWord l) f
        (eraseMarkCoordinate i x)=
      gaussianLinearBackward (stdGaussian (EuclideanSpace ℝ I)) (diagonalWord l) f x := by
  induction l with
  | nil => exact hfree
  | cons a l ih => exact gaussianLinearEntropic_preserves_free i a.2 ih a.1

lemma gaussianLinearBackward_free_coordinate (i : I) (l : List (ℝ×(I→ℝ)))
    (hl : ∀ a∈l, 0≤a.1)
    {f : EuclideanSpace ℝ I→ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (hfree : ∀ x, f (eraseMarkCoordinate i x)=f x) (c : ℝ) :
    gaussianLinearBackward (stdGaussian (EuclideanSpace ℝ I)) (diagonalWord l)
      (fun y => f y+c*y i)=fun x =>
      gaussianLinearBackward (stdGaussian (EuclideanSpace ℝ I)) (diagonalWord l) f x+
        c*x i+c^2/2*(l.map (fun a => a.1*(a.2 i)^2)).sum := by
  induction l with
  | nil => funext x; simp [diagonalWord,gaussianLinearBackward]
  | cons a l ih =>
    have hl' : ∀ a∈l, 0≤a.1 := fun b hb => hl b (List.mem_cons_of_mem a hb)
    let g := gaussianLinearBackward (stdGaussian (EuclideanSpace ℝ I)) (diagonalWord l) f
    have hg := gaussianLinearBackward_lipschitz (stdGaussian (EuclideanSpace ℝ I)) hf
      (diagonalWord l) (diagonalWord_nonneg l hl')
    have hgfree := gaussianLinearBackward_preserves_free i l hfree
    have hgc := hg.add ((c • EuclideanSpace.proj (𝕜 := ℝ) i).lipschitzWith)
    change LipschitzWith _ (fun x => g x+c*x i) at hgc
    simp only [diagonalWord,List.map_cons,gaussianLinearBackward]
    change gaussianLinearEntropic _ a.1 (diagonalMark a.2)
      (gaussianLinearBackward _ (diagonalWord l) (fun y => f y+c*y i)) = _
    rw [ih hl',gaussianLinearEntropic_add_const a.2 hgc]
    funext x
    rw [gaussianLinearEntropic_free_coordinate i a.2 hg hgfree]
    simp only [List.sum_cons]
    dsimp only [g,diagonalWord]
    ring

lemma gaussianLinearBackward_affine_root_mean (i : I) (l : List (ℝ×(I→ℝ)))
    (hl : ∀ a∈l, 0≤a.1) (root : I→ℝ)
    {f : EuclideanSpace ℝ I→ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (hfree : ∀ x, f (eraseMarkCoordinate i x)=f x) (c : ℝ) :
    (∫ x, gaussianLinearBackward (stdGaussian (EuclideanSpace ℝ I)) (diagonalWord l)
      (fun y => f y+c*y i) (diagonalMark root x) ∂stdGaussian (EuclideanSpace ℝ I)) =
    (∫ x, gaussianLinearBackward (stdGaussian (EuclideanSpace ℝ I)) (diagonalWord l) f
      (diagonalMark root x) ∂stdGaussian (EuclideanSpace ℝ I))+
      c^2/2*(l.map (fun a => a.1*(a.2 i)^2)).sum := by
  have hG := gaussianLinearBackward_lipschitz (stdGaussian (EuclideanSpace ℝ I)) hf
    (diagonalWord l) (diagonalWord_nonneg l hl)
  have hGI := integrable_of_all_exp (stdGaussian (EuclideanSpace ℝ I))
    (fun t => gaussian_integrable_exp_linear_shift _ hG (diagonalMark root) t 0)
  simp only [zero_add] at hGI
  have hCI : Integrable (fun x : EuclideanSpace ℝ I => c*root i*x i)
      (stdGaussian (EuclideanSpace ℝ I)) := by
    apply integrable_of_all_exp
    intro t
    simpa using gaussian_integrable_exp_lipschitz _
      ((c*root i) • EuclideanSpace.proj (𝕜 := ℝ) i).lipschitzWith t 1 (0:EuclideanSpace ℝ I)
  rw [gaussianLinearBackward_free_coordinate i l hl hf hfree]
  simp only [diagonalMark_apply,← mul_assoc]
  have hsum : Integrable (fun x =>
      gaussianLinearBackward (stdGaussian (EuclideanSpace ℝ I)) (diagonalWord l) f
        (diagonalMark root x)+c*root i*x i) (stdGaussian (EuclideanSpace ℝ I)) := by
    convert hGI.add hCI using 1
  rw [integral_add hsum (integrable_const _),integral_add hGI hCI,
    integral_const_mul,gaussian_coordinate_mean,integral_const]
  simp

end SphericalPerceptronFreeEnergy
end

end OAI
