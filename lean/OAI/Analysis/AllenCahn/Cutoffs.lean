import OAI.Analysis.AllenCahn.Conjugation
import OAI.Analysis.AllenCahn.ResolventJets

namespace OAI

noncomputable section
namespace DeGiorgi
open Filter Set Topology
open scoped NNReal
open scoped SchwartzMap Laplacian ContDiff
open FourierTransform
open scoped ContDiff Polynomial
open Filter Topology

lemma coordinate_polynomial_profile {n : ℕ} (ν : Space n) (p : Polynomial ℝ)
    (i : Fin n) (x : Space n) :
    coordDeriv (fun z => p.eval (profile (inner ℝ ν z))) i x =
      p.derivative.eval (profile (inner ℝ ν x))*
        (inner ℝ ν (basis n i)/Real.sqrt 2)*profileWeight (inner ℝ ν x) := by
  have H := (p.hasDerivAt (profile (inner ℝ ν x))).comp_hasFDerivAt x
    ((profile_contDiff.comp (innerSL ℝ ν).contDiff).differentiable (by simp) x).hasFDerivAt
  simp only [Function.comp_def] at H
  change HasFDerivAt (fun z : Space n => p.eval (profile (inner ℝ ν z)))
    (p.derivative.eval (profile (inner ℝ ν x)) •
      fderiv ℝ (fun z : Space n => profile (inner ℝ ν z)) x) x at H
  unfold coordDeriv
  rw [H.fderiv]
  simp only [smul_apply,smul_eq_mul]
  rw [← coordDeriv,profile_comp_inner_coord]
  ring

lemma weight_polynomial_jets {n : ℕ} (ν : Space n) (l : List (Fin n)) :
    ∃ p : Polynomial ℝ, ∀ x,
      coordinateJet (fun z => profileWeight (inner ℝ ν z)) l x =
        p.eval (profile (inner ℝ ν x))*profileWeight (inner ℝ ν x) := by
  induction l with
  | nil => exact ⟨1,fun x => by simp [coordinateJet]⟩
  | cons i l ih =>
    obtain ⟨p,hp⟩ := ih
    refine ⟨p.derivative*Polynomial.C (inner ℝ ν (basis n i)/Real.sqrt 2)*(1-Polynomial.X^2)+
      p*Polynomial.C (-Real.sqrt 2*inner ℝ ν (basis n i))*Polynomial.X,fun x => ?_⟩
    have he := funext hp
    change coordDeriv (coordinateJet (fun z => profileWeight (inner ℝ ν z)) l) i x=_
    rw [he,coordDeriv_mul
      (f := fun z : Space n => p.eval (profile (inner ℝ ν z)))
      (g := fun z : Space n => profileWeight (inner ℝ ν z))
      (p.differentiable.comp (profile_contDiff.comp (innerSL ℝ ν).contDiff |>.differentiable (by simp)))
      (profileWeight_contDiff.comp (innerSL ℝ ν).contDiff |>.differentiable (by simp))]
    · rw [coordinate_polynomial_profile,weight_comp_inner_coord]
      simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_sub,
        Polynomial.eval_one,Polynomial.eval_pow,Polynomial.eval_X,profileWeight]
      ring

lemma profileWeight_relative_jets {n : ℕ} (ν : Space n) (l : List (Fin n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      |coordinateJet (fun z => profileWeight (inner ℝ ν z)) l x| ≤ C*profileWeight (inner ℝ ν x) := by
  obtain ⟨p,hp⟩ := weight_polynomial_jets ν l
  obtain ⟨z,hz,hm⟩ := isCompact_Icc.exists_isMaxOn
    (show (Set.Icc (-1 : ℝ) 1).Nonempty from ⟨0,by norm_num⟩) p.continuous.abs.continuousOn
  refine ⟨|p.eval z|,abs_nonneg _,fun x => ?_⟩
  rw [hp,abs_mul,abs_of_pos (profileWeight_pos _)]
  exact mul_le_mul_of_nonneg_right (hm ⟨(Real.neg_one_lt_tanh _).le,(Real.tanh_lt_one _).le⟩)
    (profileWeight_pos _).le

lemma relative_jets_carrier {n : ℕ} {F : Space n → ℝ} (hF : ContDiff ℝ ∞ F)
    (_hF0 : ∀ x, 0 ≤ F x)
    (hJ : ∀ l, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |coordinateJet F l x| ≤ C*F x) :
    ∃ G W : ℝ, 0 ≤ G ∧ 0 ≤ W ∧ (∀ x, ‖gradient F x‖ ≤ G*F x) ∧
      (∀ x, |Laplacian.laplacian F x| ≤ W*F x) := by
  choose C hC hb using fun i : Fin n => hJ [i]
  choose B hB hbb using fun i : Fin n => hJ [i,i]
  refine ⟨∑ i, C i,∑ i, B i,Finset.sum_nonneg (fun i _ => hC i),
    Finset.sum_nonneg (fun i _ => hB i),fun x => ?_,fun x => ?_⟩
  · calc _ ≤ ∑ i : Fin n, |coordDeriv F i x| := gradient_norm_le_sum_abs F x
      _ ≤ ∑ i : Fin n, C i*F x := Finset.sum_le_sum (fun i _ => hb i x)
      _ = _ := by rw [Finset.sum_mul]
  · rw [laplacian_eq_sum_coordDeriv (smooth_C2 hF)]
    calc _ ≤ ∑ i : Fin n, |coordDeriv (coordDeriv F i) i x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin n, B i*F x := Finset.sum_le_sum (fun i _ => hbb i x)
      _ = _ := by rw [Finset.sum_mul]

end DeGiorgi
end

noncomputable section
namespace DeGiorgi
open Filter Set Topology
open scoped NNReal
open scoped SchwartzMap Laplacian ContDiff
open FourierTransform
open scoped ContDiff
open Filter Topology

def normalReflection {n : ℕ} (ν : Space n) : Space n ≃ₗᵢ[ℝ] Space n :=
  (ℝ ∙ ν)ᗮ.reflection

lemma normalReflection_apply {n : ℕ} {ν : Space n} (hν : ‖ν‖=1) (x : Space n) :
    normalReflection ν x = x+(-2*inner ℝ ν x) • ν := by
  rw [normalReflection,Submodule.reflection_orthogonal_apply,Submodule.reflection_singleton_apply,hν]
  simp only [neg_sub]
  module

lemma normalReflection_inner {n : ℕ} {ν : Space n} (hν : ‖ν‖=1) (x : Space n) :
    inner ℝ ν (normalReflection ν x) = -inner ℝ ν x := by
  rw [normalReflection_apply hν,inner_add_right,real_inner_smul_right,real_inner_self_eq_norm_sq,hν]
  ring

lemma profileWeight_neg (s : ℝ) : profileWeight (-s)=profileWeight s := by
  simp [profileWeight,profile,neg_div,Real.tanh_neg]

lemma SmallDefectConverges.tensor_normal_translate {n : ℕ} {v : ℕ → Space n → ℝ}
    {g : SmallDefectIndex n → Space n → ℝ} (hg : SmallDefectConverges v g)
    (hv : ∀ j, v j ∈ positiveDefectClass n) (h0 : ∀ j, v j 0=0)
    (he : Tendsto (fun j => diffuseDefect (v j) 0) atTop (𝓝 0)) {ν : Space n}
    (horient : ∀ j, gradient (inverseProfile (v j)) 0 = Real.sqrt (1-diffuseDefect (v j) 0) • ν)
    (a b : Fin n) (x : Space n) (t : ℝ) :
    g (some (some (a,b))) (x+t • ν)=g (some (some (a,b))) x := by
  let T := g (some (some (a,b)))
  have hTf (y : Space n) : fderiv ℝ T y ν=0 := by
    have H := hg.tensor_transport hv he a b y
    rw [hg.profile_limit hv h0 he horient,← inner_gradient_eq_sum,gradient_inner,
      real_inner_comm,inner_gradient_left] at H
    exact H
  have hder (s : ℝ) : HasDerivAt (fun t : ℝ => T (x+t • ν)) 0 s := by
    have H := ((hg.1 (some (some (a,b)))).differentiable (by simp) (x+s • ν)).hasFDerivAt.comp_hasDerivAt s
      (((hasDerivAt_id s).smul_const ν).const_add x)
    simp only [Function.comp_def,id_eq,one_smul] at H
    change HasDerivAt (fun t : ℝ => T (x+t • ν)) (fderiv ℝ T (x+s • ν) ν) s at H
    simpa only [hTf] using H
  have H := is_const_of_deriv_eq_zero (fun s => (hder s).differentiableAt)
    (fun s => (hder s).deriv) t 0
  simpa only [zero_smul,add_zero] using H

lemma limit_source_relative_jets {n : ℕ} {v : ℕ → Space n → ℝ}
    {g : SmallDefectIndex n → Space n → ℝ} (hg : SmallDefectConverges v g)
    (hv : ∀ j, v j ∈ positiveDefectClass n) (ν : Space n) :
    let V := fun x => profileWeight (inner ℝ ν x)
    let F := fun x => V x*g (some none) x
    let S := fun x => 2*V x*(∑ i : Fin n, ∑ j : Fin n, g (some (some (i,j))) x^2)
    (∀ l, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |coordinateJet F l x| ≤ C*F x) ∧
      (∀ l, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |coordinateJet S l x| ≤ C*F x) := by
  dsimp only
  let V := fun x => profileWeight (inner ℝ ν x)
  let d := g (some none)
  let T := fun i j => g (some (some (i,j)))
  have hV : ContDiff ℝ ∞ V := profileWeight_contDiff.comp (innerSL ℝ ν).contDiff
  have hd : ContDiff ℝ ∞ d := hg.1 (some none)
  have hT (i j) : ContDiff ℝ ∞ (T i j) := hg.1 (some (some (i,j)))
  have hd0 (x) : 0 < d x := (hg.positive hv).2 x
  have hV0 (x) : 0 < V x := profileWeight_pos _
  have hJV (k) : JetControl (Set.univ : Set Unit) (fun _ => V) (fun _ => V) k := by
    intro l hl
    obtain ⟨C,hC,hb⟩ := profileWeight_relative_jets ν l
    exact ⟨C,hC,fun _ _ => hb⟩
  have hJd (k) : JetControl (Set.univ : Set Unit) (fun _ => d) (fun _ => d) k := by
    intro l hl
    obtain ⟨C,hC,hb⟩ := hg.relative_D_jets hv l
    exact ⟨C,hC,fun _ _ => hb⟩
  have hJT (k i j) : JetControl (Set.univ : Set Unit) (fun _ x => Real.sqrt (d x)) (fun _ => T i j) k := by
    intro l hl
    obtain ⟨C,hC,hb⟩ := hg.relative_T_jets hv i j l
    exact ⟨C,hC,fun _ _ => hb⟩
  have hJF (k) := (hJV k).mul (fun _ _ => hV) (fun _ _ => hd)
    (fun _ _ x => (hV0 x).le) (fun _ _ x => (hd0 x).le) (hJd k)
  have hJT2 (k i j) : JetControl (Set.univ : Set Unit) (fun _ => d) (fun _ x => T i j x^2) k := by
    have H := (hJT k i j).mul (fun _ _ => hT i j) (fun _ _ => hT i j)
      (fun _ _ x => Real.sqrt_nonneg (d x)) (fun _ _ x => Real.sqrt_nonneg (d x)) (hJT k i j)
    simpa only [← pow_two,Real.sq_sqrt (hd0 _).le] using H
  have hJQ (k) : JetControl (Set.univ : Set Unit) (fun _ => d)
      (fun _ x => ∑ i : Fin n, ∑ j : Fin n, T i j x^2) k := by
    simpa using
      JetControl.sum Finset.univ (fun i _ _ _ => ContDiff.sum (fun j _ => (hT i j).pow 2))
        (fun i _ => JetControl.sum Finset.univ (fun j _ _ _ => (hT i j).pow 2) (fun j _ => hJT2 k i j))
  have hQ : ContDiff ℝ ∞ (fun x => ∑ i : Fin n, ∑ j : Fin n, T i j x^2) :=
    ContDiff.sum (fun i _ => ContDiff.sum (fun j _ => (hT i j).pow 2))
  have hJS (k) : JetControl (Set.univ : Set Unit) (fun _ x => V x*d x)
      (fun _ x => 2*V x*(∑ i : Fin n, ∑ j : Fin n, T i j x^2)) k := by
    have H := ((hJV k).mul (fun _ _ => hV) (fun _ _ => hQ)
      (fun _ _ x => (hV0 x).le) (fun _ _ x => (hd0 x).le) (hJQ k)).const_mul
        (fun _ _ => hV.mul hQ) 2
    simpa only [mul_assoc] using H
  constructor
  · intro l
    obtain ⟨C,hC,hb⟩ := hJF l.length l le_rfl
    exact ⟨C,hC,hb () (Set.mem_univ ())⟩
  · intro l
    obtain ⟨C,hC,hb⟩ := hJS l.length l le_rfl
    exact ⟨C,hC,hb () (Set.mem_univ ())⟩

theorem SmallDefectConverges.even_source_removed {n : ℕ} {v : ℕ → Space n → ℝ}
    {g : SmallDefectIndex n → Space n → ℝ} (hg : SmallDefectConverges v g)
    (hv : ∀ j, v j ∈ positiveDefectClass n) (h0 : ∀ j, v j 0=0)
    (he : Tendsto (fun j => diffuseDefect (v j) 0) atTop (𝓝 0)) {ν : Space n}
    (hν : ‖ν‖=1) (horient : ∀ j, gradient (inverseProfile (v j)) 0 =
      Real.sqrt (1-diffuseDefect (v j) 0) • ν) :
    let F := fun x => profileWeight (inner ℝ ν x)*g (some none) x
    let S := fun x => 2*profileWeight (inner ℝ ν x)*
      (∑ i : Fin n, ∑ j : Fin n, g (some (some (i,j))) x^2)
    ∃ E : Space n → ℝ, ContDiff ℝ ∞ E ∧ (∀ x, 0 ≤ E x) ∧ (∀ x, E x ≤ F x) ∧
      (∀ x, -Laplacian.laplacian E x+(2-profileWeight (inner ℝ ν x))*E x=S x) ∧
      (∀ x, E (normalReflection ν x)=E x) := by
  dsimp only
  let V := fun x => profileWeight (inner ℝ ν x)
  let F := fun x => V x*g (some none) x
  let S := fun x => 2*V x*(∑ i : Fin n, ∑ j : Fin n, g (some (some (i,j))) x^2)
  have hV : V.HasTemperateGrowth := profileWeight_temperate.comp (Function.hasTemperateGrowth_inner_right ν)
  have hF : ContDiff ℝ ∞ F := hV.1.mul (hg.1 (some none))
  have hS : ContDiff ℝ ∞ S := (contDiff_const.mul hV.1).mul
    (ContDiff.sum (fun i _ => ContDiff.sum (fun j _ => (hg.1 (some (some (i,j)))).pow 2)))
  have hF0 (x) : 0 < F x := mul_pos (profileWeight_pos _) ((hg.positive hv).2 x)
  obtain ⟨hJF,hJS⟩ := limit_source_relative_jets hg hv ν
  obtain ⟨G,W,hG,hW,hGb,hWb⟩ := relative_jets_carrier hF (fun x => (hF0 x).le) hJF
  apply even_source_exhaustion hV (fun x => (profileWeight_pos _).le) hS
    (fun x => mul_nonneg (mul_nonneg (by norm_num) (profileWeight_pos _).le)
      (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)))) hF hF0
    (hg.conjugated_equation hv h0 he hν horient) hG hW hGb hWb (fun l => ?_) hJS
    (normalReflection ν) (fun x => ?_) (fun x => ?_)
  · obtain ⟨C,hC,hb⟩ := profileWeight_relative_jets ν l
    exact ⟨C,hC,fun x => (hb x).trans (mul_le_of_le_one_right hC (profileWeight_le_one _))⟩
  · dsimp [V]
    rw [normalReflection_inner hν,profileWeight_neg]
  · dsimp [S,V]
    rw [normalReflection_inner hν,profileWeight_neg]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [normalReflection_apply hν,hg.tensor_normal_translate hv h0 he horient]

def unitCutoff {n : ℕ} (z x : Space n) : ℝ := 1 - ‖x - z‖ ^ 2

lemma unitCutoff_smooth {n : ℕ} (z : Space n) : ContDiff ℝ ∞ (unitCutoff z) :=
  contDiff_const.sub ((contDiff_id.sub contDiff_const).norm_sq ℝ)

lemma fderiv_unitCutoff {n : ℕ} (z x : Space n) :
    fderiv ℝ (unitCutoff z) x = (-2 : ℝ) • innerSL ℝ (x - z) := by
  have hd := (hasStrictFDerivAt_norm_sq (x - z)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).sub_const z)
  have hn : HasFDerivAt (fun y : Space n => ‖y - z‖ ^ 2)
      ((2 : ℝ) • innerSL ℝ (x-z)) x := by
    simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id,
      ← Nat.cast_smul_eq_nsmul ℝ 2, Nat.cast_ofNat] using hd
  have H := (hasFDerivAt_const (1 : ℝ) x).fun_sub hn
  change fderiv ℝ (fun y : Space n => 1 - ‖y-z‖ ^ 2) x = _
  simpa only [zero_sub, neg_smul] using H.fderiv

lemma gradient_unitCutoff {n : ℕ} (z x : Space n) :
    gradient (unitCutoff z) x = (-2 : ℝ) • (x - z) := by
  rw [gradient, fderiv_unitCutoff, map_smul]
  congr 1
  exact (InnerProductSpace.toDual ℝ (Space n)).symm_apply_apply (x-z)

lemma laplacian_unitCutoff {n : ℕ} (z x : Space n) :
    Laplacian.laplacian (unitCutoff z) x = -2 * n := by
  have hs : ContDiff ℝ 2 (fun y : Space n => ‖y - z‖ ^ 2) :=
    (contDiff_id.sub contDiff_const).norm_sq ℝ
  have he : (fun y : Space n => ‖y - z‖ ^ 2) = fun y => ‖-z + y‖ ^ 2 := by
    funext y
    rw [sub_eq_add_neg, add_comm]
  change Laplacian.laplacian (fun y => (1 : ℝ) - ‖y - z‖ ^ 2) x = _
  rw [laplacian_fun_sub contDiff_const hs]
  rw [InnerProductSpace.laplacian_const]
  rw [he, laplacian_translate (f := fun y : Space n => ‖y‖ ^ 2) (contDiff_id.norm_sq ℝ) (-z) x, laplacian_norm_sq]
  simp only [Pi.zero_apply]
  ring

lemma gradient_fun_square {n : ℕ} {f : Space n → ℝ}
    (hf : Differentiable ℝ f) (x : Space n) :
    gradient (fun y => f y ^ 2) x = (2 * f x) • gradient f x := by
  rw [gradient, fderiv_fun_pow 2 (hf x), map_smul]
  simp [gradient]

lemma cutoff_max_calculus {n : ℕ} {w r : Space n → ℝ}
    (hw : ContDiff ℝ 2 w) (hr : ContDiff ℝ 2 r) {x : Space n}
    (hx : 0 < r x) (hm : IsLocalMax (fun y => r y ^ 2 * w y) x) :
    r x ^ 2 * Laplacian.laplacian w x ≤
      (6 * ‖gradient r x‖ ^ 2 - 2 * r x * Laplacian.laplacian r x) * w x ∧
    ∀ b : Space n, -(r x ^ 2) * fderiv ℝ w x b =
      2 * r x * w x * fderiv ℝ r x b := by
  have hrd := hr.differentiable (by norm_num)
  have hwd := hw.differentiable (by norm_num)
  have he (b : Space n) : r x ^ 2 * fderiv ℝ w x b +
      2 * r x * w x * fderiv ℝ r x b = 0 := by
    have H := congrArg (fun L : Space n →L[ℝ] ℝ => L b) hm.fderiv_eq_zero
    rw [fderiv_fun_mul (c := fun y => r y ^ 2) (d := w) ((hrd x).fun_pow 2) (hwd x), fderiv_fun_pow 2 (hrd x)] at H
    simp only [add_apply, smul_apply, smul_eq_mul, zero_apply, show (2 - 1 : ℕ) = 1 from rfl, pow_one, two_smul] at H
    nlinarith
  refine ⟨?_, fun b => by linarith [he b]⟩
  have hl := laplacian_nonpos_of_local_max ((hr.pow 2).mul hw) hm
  rw [laplacian_fun_mul (hr.pow 2) hw, laplacian_sq hr,
    gradient_fun_square hrd, real_inner_smul_left] at hl
  have hi := he (gradient r x)
  rw [← inner_gradient_left, ← inner_gradient_left, real_inner_self_eq_norm_sq,
    real_inner_comm (gradient r x) (gradient w x)] at hi
  have hl' := mul_le_mul_of_nonneg_left hl hx.le
  nlinarith

lemma quartic_cubic_bound {t L A C : ℝ} (hL : 0 ≤ L) (hA : 0 ≤ A)
    (_hC : 0 ≤ C) (_ht : 0 ≤ t) (h : t ^ 4 ≤ L + A * t ^ 2 + C * t ^ 3) :
    t ^ 2 ≤ 2 * A + C ^ 2 + 2 * L + 1 := by
  have H : t ^ 4 ≤ 2 * L + (2 * A + C ^ 2) * t ^ 2 := by
    nlinarith [sq_nonneg (t ^ 2 - C * t)]
  by_contra hh
  have hh' : 2 * A + C ^ 2 + 2 * L + 1 < t ^ 2 := lt_of_not_ge hh
  have ht1 : 1 < t ^ 2 := by nlinarith [sq_nonneg C]
  have hp := mul_pos (sub_pos.mpr hh') (by linarith : 0 < t ^ 2)
  have hq := mul_nonneg (by linarith : 0 ≤ 2 * L + 1) (by linarith : 0 ≤ t ^ 2 - 1)
  nlinarith

lemma cutoff_bernstein_algebra {r w lap drv L p Q B C : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hw : 0 ≤ w) (hL : 0 ≤ L) (hp : 0 ≤ p)
    (hQ : 0 ≤ Q) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hpde : w ^ 2 ≤ L * (1 + w) + p * (lap - drv))
    (hlap : r ^ 2 * lap ≤ Q * w)
    (hdrv : -(r ^ 2) * drv ≤ 4 * r * w * (B + C * Real.sqrt w)) :
    r ^ 2 * w ≤ 2 * (L + p * (Q + 4 * B)) + (4 * p * C) ^ 2 + 2 * L + 1 := by
  let t := r * Real.sqrt w
  have ht : 0 ≤ t := mul_nonneg hr.le (Real.sqrt_nonneg w)
  have ht2 : t ^ 2 = r ^ 2 * w := by dsimp [t]; rw [mul_pow, Real.sq_sqrt hw]
  have ht3 : t ^ 3 = r ^ 3 * w * Real.sqrt w := by
    dsimp [t]
    rw [mul_pow, pow_succ (Real.sqrt w) 2, Real.sq_sqrt hw]
    ring
  have hr2 : r ^ 2 ≤ 1 := by nlinarith
  have hr4 : r ^ 4 ≤ 1 := by nlinarith [sq_nonneg (r ^ 2)]
  have hl : r ^ 2 * (r ^ 2 * lap) ≤ Q * t ^ 2 := by
    rw [ht2]
    nlinarith [mul_le_mul_of_nonneg_left hlap (sq_nonneg r)]
  have hd : r ^ 2 * (-(r ^ 2) * drv) ≤ 4 * B * t ^ 2 + 4 * C * t ^ 3 := by
    calc r ^ 2 * (-(r ^ 2) * drv) ≤ r ^ 2 * (4 * r * w * (B + C * Real.sqrt w)) :=
           mul_le_mul_of_nonneg_left hdrv (sq_nonneg r)
         _ = 4 * B * r * t ^ 2 + 4 * C * t ^ 3 := by rw [ht2, ht3]; ring
         _ ≤ 4 * B * t ^ 2 + 4 * C * t ^ 3 := by
           have H := mul_le_mul_of_nonneg_left hr1 (by positivity : 0 ≤ 4 * B * t ^ 2)
           nlinarith
  have hpoly : t ^ 4 ≤ L + (L + p * (Q + 4 * B)) * t ^ 2 + (4 * p * C) * t ^ 3 := by
    calc t ^ 4 = r ^ 4 * w ^ 2 := by rw [show t ^ 4 = (t ^ 2) ^ 2 by ring, ht2]; ring
         _ ≤ r ^ 4 * (L * (1 + w) + p * (lap - drv)) :=
           mul_le_mul_of_nonneg_left hpde (pow_nonneg hr.le 4)
         _ = L * r ^ 4 + L * r ^ 2 * t ^ 2 +
             p * (r ^ 2 * (r ^ 2 * lap) + r ^ 2 * (-(r ^ 2) * drv)) := by rw [ht2]; ring
         _ ≤ L + L * t ^ 2 + p * (Q * t ^ 2 + (4 * B * t ^ 2 + 4 * C * t ^ 3)) := by
           gcongr <;> nlinarith [mul_le_mul_of_nonneg_left hr4 hL,
             mul_le_mul_of_nonneg_left hr2 hL]
         _ = _ := by ring
  rw [← ht2]
  exact quartic_cubic_bound hL (by positivity) (by positivity) ht hpoly

end DeGiorgi
end

end OAI
