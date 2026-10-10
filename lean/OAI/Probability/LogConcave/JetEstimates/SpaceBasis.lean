import Mathlib
import OAI.Probability.LogConcave.Sampling.MaterialScalar
import OAI.Probability.LogConcave.JetEstimates.Mdir
import OAI.Probability.LogConcave.Sampling.SmoothTimeLocalization
import OAI.Probability.LogConcave.Analysis.GaussianMarginalLowerTail
import OAI.Probability.LogConcave.Sampling.DirectionalBasisSum

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace

lemma PolySmooth.linear {d : ℕ} (L : Point d →L[ℝ] ℝ) : PolySmooth L := by
  apply PolySmooth.of_basis_growth L.contDiff
  intro l
  cases l with
  | nil => exact growth_of_lipschitz L.lipschitzWith
  | cons i l =>
    change HasPolynomialGrowth (LogConcaveSampling.directional (EuclideanSpace.basisFun (Fin d) ℝ i)
      (JetCalculus.jet (EuclideanSpace.basisFun (Fin d) ℝ) l L))
    rw [←jet_directional L.contDiff]
    have he : LogConcaveSampling.directional (EuclideanSpace.basisFun (Fin d) ℝ i) L=
        fun _ => L (EuclideanSpace.basisFun (Fin d) ℝ i) := by
      funext y
      simp [LogConcaveSampling.directional]
    rw [he,JetCalculus.jet_const]
    split_ifs <;> exact growth_const _

lemma growth_potential_of_gradient_lipschitz {d : ℕ} {H : Point d → ℝ} {K : ℝ≥0}
    (hH : ContDiff ℝ 2 H) (hK : LipschitzWith K (gradient H)) : HasPolynomialGrowth H := by
  let C := |H 0|+‖gradient H 0‖+(K:ℝ)+1
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨C,hC,2,fun y => ?_⟩
  have ht := quadratic_remainder_of_gradient_lipschitz hH hK 0 y
  rw [zero_add] at ht
  have hi := abs_real_inner_le_norm y (gradient H 0)
  have hb : |H y|≤|H 0|+‖y‖*‖gradient H 0‖+(K:ℝ)*‖y‖^2/2 := by
    have he : H y=(H y-H 0-inner ℝ y (gradient H 0))+H 0+inner ℝ y (gradient H 0) := by ring
    calc
      |H y| = |(H y-H 0-inner ℝ y (gradient H 0))+H 0+inner ℝ y (gradient H 0)| := congrArg abs he
      _ ≤ |H y-H 0-inner ℝ y (gradient H 0)|+|H 0|+|inner ℝ y (gradient H 0)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ _ := by linarith
  have hy : ‖y‖≤1+‖y‖^2 := by nlinarith [sq_nonneg (‖y‖-1)]
  have hh := mul_le_mul_of_nonneg_right hy (norm_nonneg (gradient H 0))
  change ‖H y‖≤C*(1+‖y‖^2)
  rw [Real.norm_eq_abs]
  dsimp [C]
  nlinarith [mul_nonneg (abs_nonneg (H 0)) (sq_nonneg ‖y‖),
    mul_nonneg (show (0:ℝ)≤K from K.coe_nonneg) (sq_nonneg ‖y‖)]

lemma interpolationPotential_polySmooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) :
    PolySmooth (interpolationPotential F x r ρ) := by
  have hs := interpolationPotential_smooth hF x hr.le hl hρ0 hρ1
  apply PolySmooth.of_basis_growth hs
  intro l
  cases l with
  | nil =>
    exact growth_potential_of_gradient_lipschitz (hs.of_le (WithTop.coe_le_coe.mpr (show (2:ℕ∞)≤⊤ from le_top)))
      (interpolationPotential_gradient_lipschitz hF x hr.le hl hρ0 hρ1)
  | cons i l =>
    let v := EuclideanSpace.basisFun (Fin d) ℝ i
    change HasPolynomialGrowth (directional v
      (JetCalculus.jet (EuclideanSpace.basisFun (Fin d) ℝ) l (interpolationPotential F x r ρ)))
    rw [←jet_directional hs]
    have he : directional v (interpolationPotential F x r ρ)=fun y =>
        inner ℝ v y+(r*ρ)*inner ℝ v (conditionalFieldMean F x r ρ y) := by
      funext y
      rw [directional_gradient,interpolationPotential_gradient hF x hr.le hl hρ0 hρ1,
        real_inner_comm,inner_add_right,inner_smul_right]
    rw [he]
    exact ((PolySmooth.linear (innerSL ℝ v)).add ((PolySmooth.const (r*ρ)).mul
      (conditionalFieldMean_component_polySmooth hF x hr hlam hl hρ0 hρ1 i))).jet_growth _ l

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators RealInnerProductSpace NNReal

namespace JetCalculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma dir_right_slice_at {A : ℝ × E → ℝ} {t : ℝ} {y : E}
    (hA : DifferentiableAt ℝ A (t,y)) (v : E) :
    dir v (fun z => A (t,z)) y=dir (0,v) A (t,y) := by
  have hh := hA.hasFDerivAt.comp y ((hasFDerivAt_const t y).prodMk (hasFDerivAt_id y))
  unfold dir
  change (fderiv ℝ (A ∘ Prod.mk t) y) v=_
  rw [hh.fderiv]
  simp

lemma dir_left_slice_at {A : ℝ × E → ℝ} {t : ℝ} {y : E}
    (hA : DifferentiableAt ℝ A (t,y)) :
    deriv (fun s => A (s,y)) t=dir (1,0) A (t,y) := by
  have hh := hA.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))
  exact hh.deriv

end JetCalculus

lemma joint_mdir_eq_material {d : ℕ} (F : Point d → ℝ) (x : Point d) (r : ℝ)
    {A : ℝ × Point d → ℝ} {ρ : ℝ} {y : Point d}
    (hA : DifferentiableAt ℝ A (ρ,y)) :
    JetCalculus.mdir (1,0) (fun i => (0,EuclideanSpace.basisFun (Fin d) ℝ i)) r
      (fun i p => inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ i)
        (conditionalFieldMean F x r p.1 p.2)) A (ρ,y)=
      materialScalar F x r (fun t y => A (t,y)) ρ y := by
  unfold JetCalculus.mdir materialScalar
  rw [JetCalculus.dir_left_slice_at hA,directional_basis_sum]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  rw [←JetCalculus.dir_right_slice_at hA]
  simp only [OrthonormalBasis.repr_apply_apply]
  rfl

lemma dir_inner_map {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d : ℕ} {A : E → Point d} {y : E} (hA : DifferentiableAt ℝ A y) (u : Point d) (v : E) :
    JetCalculus.dir v (fun z => inner ℝ u (A z)) y=inner ℝ u ((fderiv ℝ A y) v) := by
  unfold JetCalculus.dir
  change (fderiv ℝ ((innerSL ℝ u) ∘ A) y) v=_
  rw [((innerSL ℝ u).hasFDerivAt.comp y hA.hasFDerivAt).fderiv]
  rfl

theorem conditionalFieldMean_directional_symm {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0<ρ) (hρ1 : ρ<1) (y u v : Point d) :
    JetCalculus.dir v (fun y => inner ℝ u (conditionalFieldMean F x r ρ y)) y=
      JetCalculus.dir u (fun y => inner ℝ v (conditionalFieldMean F x r ρ y)) y := by
  have hm := (conditionalFieldMean_smooth hF x hr.le hl hρ0.le hρ1).differentiable (by simp)
  rw [dir_inner_map (hm y),dir_inner_map (hm y)]
  have hg : gradient (interpolationPotential F x r ρ)=
      fun y => y+(r*ρ) • conditionalFieldMean F x r ρ y :=
    funext (interpolationPotential_gradient hF x hr.le hl hρ0.le hρ1)
  have hd : fderiv ℝ (gradient (interpolationPotential F x r ρ)) y=
      ContinuousLinearMap.id ℝ (Point d)+(r*ρ) • fderiv ℝ (conditionalFieldMean F x r ρ) y := by
    rw [hg]
    exact ((hasFDerivAt_id y).add ((hm y).hasFDerivAt.const_smul (r*ρ))).fderiv
  have hsym := ContDiff.isSymmetric_gradient_derivative
    ((interpolationPotential_smooth hF x hr.le hl hρ0.le hρ1).of_le (by norm_cast)) y u v
  change inner ℝ ((fderiv ℝ (gradient (interpolationPotential F x r ρ)) y) u) v=
    inner ℝ u ((fderiv ℝ (gradient (interpolationPotential F x r ρ)) y) v) at hsym
  rw [hd] at hsym
  simp only [add_apply,smul_apply,ContinuousLinearMap.id_apply,
    inner_add_left,inner_add_right,real_inner_smul_left,inner_smul_right] at hsym
  rw [real_inner_comm v ((fderiv ℝ (conditionalFieldMean F x r ρ) y) u)] at hsym
  have hp : 0<r*ρ := mul_pos hr hρ0
  nlinarith

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling.JetCalculus
open scoped Classical BigOperators RealInnerProductSpace

abbrev spaceBasis (d : ℕ) := EuclideanSpace.basisFun (Fin d) ℝ

def linearScore {d : ℕ} (i : Fin d) (y : Point d) : ℝ := inner ℝ (spaceBasis d i) y

def euler {d : ℕ} (f : Point d → ℝ) (y : Point d) : ℝ :=
  ∑i,linearScore i y*dir (spaceBasis d i) f y

lemma linearScore_smooth {d : ℕ} (i : Fin d) : ContDiff ℝ (⊤:ℕ∞) (linearScore i) :=
  (innerSL ℝ (spaceBasis d i)).contDiff

lemma dir_linearScore {d : ℕ} (i : Fin d) (v y : Point d) :
    dir v (linearScore i) y=inner ℝ (spaceBasis d i) v := by
  change (fderiv ℝ (innerSL ℝ (spaceBasis d i)) y) v=_
  rw [(innerSL ℝ (spaceBasis d i)).fderiv]
  rfl

lemma smooth_euler {d : ℕ} {f : Point d → ℝ} (hf : ContDiff ℝ (⊤:ℕ∞) f) :
    ContDiff ℝ (⊤:ℕ∞) (euler f) :=
  ContDiff.sum fun i _ => (linearScore_smooth i).mul (smooth_dir hf _)

lemma dir_euler {d : ℕ} {f : Point d → ℝ} (hf : ContDiff ℝ (⊤:ℕ∞) f) (v : Point d) :
    dir v (euler f)=fun y => euler (dir v f) y+dir v f y := by
  unfold euler
  rw [dir_sum Finset.univ (fun i _ => ((linearScore_smooth i).mul (smooth_dir hf _)).differentiable (by simp))]
  simp_rw [dir_mul ((linearScore_smooth _).differentiable (by simp))
    ((smooth_dir hf _).differentiable (by simp)),dir_dir hf v]
  funext y
  simp only [dir_linearScore,Finset.sum_add_distrib]
  have he : (∑i,inner ℝ (spaceBasis d i) v*dir (spaceBasis d i) f y)=dir v f y := by
    simpa only [OrthonormalBasis.repr_apply_apply,spaceBasis,dir,directional] using (congrFun (directional_basis_sum v f) y).symm
  rw [he]
  ring

lemma jet_euler {d : ℕ} {κ : Type*} {f : Point d → ℝ}
    (hf : ContDiff ℝ (⊤:ℕ∞) f) (v : κ → Point d) (l : List κ) :
    jet v l (euler f)=fun y => euler (jet v l f) y+(l.length:ℝ)*jet v l f y := by
  induction l with
  | nil => simp [jet]
  | cons i l ih =>
    simp only [jet,ih]
    rw [dir_add ((smooth_euler (smooth_jet hf v l)).differentiable (by simp))
      ((contDiff_const.mul (smooth_jet hf v l)).differentiable (by simp)),
      dir_euler (smooth_jet hf v l),dir_const_mul ((smooth_jet hf v l).differentiable (by simp))]
    funext y
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    ring

lemma gadj_linearScore {d : ℕ} (f : Point d → ℝ) :
    gadj (spaceBasis d) linearScore (fun i => dir (spaceBasis d i) f)=
      fun y => -(∑i,dir (spaceBasis d i) (dir (spaceBasis d i) f) y)+euler f y := by
  funext y
  simp [gadj,cadj,euler,Finset.sum_add_distrib,Finset.sum_neg_distrib]

lemma jet_gadj_linearScore {d : ℕ} {κ : Type*} {f : Point d → ℝ}
    (hf : ContDiff ℝ (⊤:ℕ∞) f) (v : κ → Point d) (l : List κ) :
    jet v l (gadj (spaceBasis d) linearScore (fun i => dir (spaceBasis d i) f))=
      fun y => gadj (spaceBasis d) linearScore (fun i => dir (spaceBasis d i) (jet v l f)) y+
        (l.length:ℝ)*jet v l f y := by
  rw [gadj_linearScore]
  have hs : ContDiff ℝ (⊤:ℕ∞) (fun y => ∑i,dir (spaceBasis d i) (dir (spaceBasis d i) f) y) :=
    ContDiff.sum fun i _ => smooth_dir (smooth_dir hf _) _
  have he : (fun y => -(∑i,dir (spaceBasis d i) (dir (spaceBasis d i) f) y)+euler f y)=
      fun y => (-1)*(∑i,dir (spaceBasis d i) (dir (spaceBasis d i) f) y)+euler f y := by
    funext y; ring
  rw [he,jet_add (contDiff_const.mul hs) (smooth_euler hf),jet_const_mul hs,
    jet_sum Finset.univ (fun i _ => smooth_dir (smooth_dir hf _) _),jet_euler hf,gadj_linearScore]
  simp_rw [jet_dir (smooth_dir hf _),jet_dir hf]
  funext y
  ring

lemma gadj_perturb {d : ℕ} (M : Fin d → Point d → ℝ) (c : ℝ) (f : Point d → ℝ) :
    gadj (spaceBasis d) (fun i y => linearScore i y+c*M i y) (fun i => dir (spaceBasis d i) f)=
      fun y => gadj (spaceBasis d) linearScore (fun i => dir (spaceBasis d i) f) y+
        c*∑i,M i y*dir (spaceBasis d i) f y := by
  unfold gadj cadj
  funext y
  rw [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem jet_gadj_gradient {d : ℕ} {κ : Type*} [DecidableEq κ]
    {M : Fin d → Point d → ℝ} (hM : ∀i,ContDiff ℝ (⊤:ℕ∞) (M i))
    {f : Point d → ℝ} (hf : ContDiff ℝ (⊤:ℕ∞) f) (c : ℝ)
    (v : κ → Point d) (l : List κ) (hl : l.Nodup) :
    jet v l (gadj (spaceBasis d) (fun i y => linearScore i y+c*M i y)
      (fun i => dir (spaceBasis d i) f))=
      fun y => gadj (spaceBasis d) (fun i y => linearScore i y+c*M i y)
        (fun i => dir (spaceBasis d i) (jet v l f)) y+
        (l.length:ℝ)*jet v l f y+
        c*∑s∈l.toFinset.powerset.erase ∅,∑i,
          jet v (l.filter (fun j => j∈s)) (M i) y*
            dir (spaceBasis d i) (jet v (l.filter (fun j => j∉s)) f) y := by
  have hs : ContDiff ℝ (⊤:ℕ∞) (fun y => ∑i,M i y*dir (spaceBasis d i) f y) :=
    ContDiff.sum fun i _ => (hM i).mul (smooth_dir hf _)
  have hga : ContDiff ℝ (⊤:ℕ∞)
      (gadj (spaceBasis d) linearScore (fun i => dir (spaceBasis d i) f)) :=
    ContDiff.sum fun i _ => smooth_cadj _ (linearScore_smooth i) (smooth_dir hf _)
  rw [gadj_perturb,jet_add hga (contDiff_const.mul hs),jet_const_mul hs,
    jet_gadj_linearScore hf,jet_sum Finset.univ (fun i _ => (hM i).mul (smooth_dir hf _))]
  simp_rw [jet_mul (hM _) (smooth_dir hf _) v l hl,jet_dir hf]
  funext y
  rw [Finset.sum_comm,←Finset.add_sum_erase _ _ (by simp : (∅:Finset κ)∈l.toFinset.powerset)]
  simp only [Finset.notMem_empty,decide_false,List.filter_false,not_false_eq_true,decide_true,List.filter_true,jet]
  rw [gadj_perturb]
  ring

end LogConcaveSampling.JetCalculus

end

end

section

noncomputable section
namespace LogConcaveSampling.JetCalculus
open scoped Classical BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

lemma smooth_dir_at {f : E → ℝ} {p : E} (hf : ContDiffAt ℝ (⊤:ℕ∞) f p) (v : E) :
    ContDiffAt ℝ (⊤:ℕ∞) (dir v f) p :=
  (hf.fderiv_right (by simp)).clm_apply contDiffAt_const

lemma dir_dir_at {f : E → ℝ} {p : E} (hf : ContDiffAt ℝ (⊤:ℕ∞) f p) (v w : E) :
    dir v (dir w f) p=dir w (dir v f) p := by
  have hs : ContDiffAt ℝ (⊤:ℕ∞) (fderiv ℝ f) p := hf.fderiv_right (by simp)
  have hd := hs.differentiableAt (by simp)
  change (fderiv ℝ (fun y => fderiv ℝ f y w) p) v =
    (fderiv ℝ (fun y => fderiv ℝ f y v) p) w
  rw [fderiv_clm_apply hd (differentiableAt_const _),
    fderiv_clm_apply hd (differentiableAt_const _)]
  simpa only [add_apply,ContinuousLinearMap.comp_apply,
    zero_apply,ContinuousLinearMap.map_zero,zero_add,
    ContinuousLinearMap.flip_apply,fderiv_const_apply] using
    (hf.isSymmSndFDerivAt (by
      simp only [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr (show (2:ℕ∞)≤⊤ from le_top))).eq v w

lemma dir_add_at {f g : E → ℝ} {p : E} (hf : DifferentiableAt ℝ f p)
    (hg : DifferentiableAt ℝ g p) (v : E) :
    dir v (fun x => f x+g x) p=dir v f p+dir v g p := by
  unfold dir
  rw [show (fun x => f x+g x)=f+g from rfl,fderiv_add hf hg]
  rfl

lemma dir_sub_at {f g : E → ℝ} {p : E} (hf : DifferentiableAt ℝ f p)
    (hg : DifferentiableAt ℝ g p) (v : E) :
    dir v (fun x => f x-g x) p=dir v f p-dir v g p := by
  unfold dir
  rw [show (fun x => f x-g x)=f-g from rfl,fderiv_sub hf hg]
  rfl

lemma dir_mul_at {f g : E → ℝ} {p : E} (hf : DifferentiableAt ℝ f p)
    (hg : DifferentiableAt ℝ g p) (v : E) :
    dir v (fun x => f x*g x) p=dir v f p*g p+f p*dir v g p := by
  unfold dir
  rw [show (fun x => f x*g x)=f*g from rfl,(hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul]
  ring

lemma dir_const_mul_at {f : E → ℝ} {p : E} (hf : DifferentiableAt ℝ f p) (v : E) (c : ℝ) :
    dir v (fun x => c*f x) p=c*dir v f p := by
  unfold dir
  rw [hf.hasFDerivAt.const_mul c |>.fderiv]
  rfl

lemma dir_sum_at {N : Type*} (s : Finset N) {f : N → E → ℝ} {p : E}
    (hf : ∀n∈s,DifferentiableAt ℝ (f n) p) (v : E) :
    dir v (fun x => ∑n∈s,f n x) p=∑n∈s,dir v (f n) p := by
  simp only [dir,(HasFDerivAt.fun_sum (fun n hn => (hf n hn).hasFDerivAt)).fderiv,sum_apply]

lemma smooth_mdir_at (w : E) (b : ι → E) (r : ℝ) {M : ι → E → ℝ} {f : E → ℝ} {p : E}
    (hM : ∀i,ContDiffAt ℝ (⊤:ℕ∞) (M i) p) (hf : ContDiffAt ℝ (⊤:ℕ∞) f p) :
    ContDiffAt ℝ (⊤:ℕ∞) (mdir w b r M f) p :=
  (smooth_dir_at hf w).sub (contDiffAt_const.mul
    (ContDiffAt.sum fun i _ => (hM i).mul (smooth_dir_at hf _)))

lemma mdir_sum_at {N : Type*} (s : Finset N) (w : E) (b : ι → E) (r : ℝ)
    (M : ι → E → ℝ) {f : N → E → ℝ} {p : E} (hf : ∀n∈s,DifferentiableAt ℝ (f n) p) :
    mdir w b r M (fun p => ∑n∈s,f n p) p=∑n∈s,mdir w b r M (f n) p := by
  unfold mdir
  simp_rw [dir_sum_at s hf]
  simp only [Finset.sum_sub_distrib,Finset.mul_sum]
  rw [Finset.sum_comm]

lemma mdir_add_at (w : E) (b : ι → E) (r : ℝ) (M : ι → E → ℝ)
    {f g : E → ℝ} {p : E} (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) :
    mdir w b r M (fun p => f p+g p) p=mdir w b r M f p+mdir w b r M g p := by
  unfold mdir
  simp_rw [dir_add_at hf hg]
  simp only [mul_add,Finset.sum_add_distrib]
  ring

lemma mdir_const_mul_at (w : E) (b : ι → E) (r : ℝ) (M : ι → E → ℝ)
    {f : E → ℝ} {p : E} (hf : DifferentiableAt ℝ f p) (c : ℝ) :
    mdir w b r M (fun p => c*f p) p=c*mdir w b r M f p := by
  unfold mdir
  simp_rw [dir_const_mul_at hf]
  have he : (∑i,M i p*(c*dir (b i) f p))=c*∑i,M i p*dir (b i) f p := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  ring

lemma mdir_mul_at (w : E) (b : ι → E) (r : ℝ) (M : ι → E → ℝ)
    {f g : E → ℝ} {p : E} (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) :
    mdir w b r M (fun p => f p*g p) p=
      mdir w b r M f p*g p+f p*mdir w b r M g p := by
  unfold mdir
  simp_rw [dir_mul_at hf hg]
  have he : (∑i,M i p*(dir (b i) f p*g p+f p*dir (b i) g p))=
      (∑i,M i p*dir (b i) f p)*g p+f p*∑i,M i p*dir (b i) g p := by
    rw [Finset.mul_sum,Finset.sum_mul,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  ring

lemma mdir_dir_at (w : E) (b : ι → E) (r : ℝ) {M : ι → E → ℝ} {f : E → ℝ} {p : E}
    (hM : ∀i,ContDiffAt ℝ (⊤:ℕ∞) (M i) p) (hf : ContDiffAt ℝ (⊤:ℕ∞) f p) (v : E) :
    mdir w b r M (dir v f) p=dir v (mdir w b r M f) p+
      r*∑i,dir v (M i) p*dir (b i) f p := by
  have hMi : ∀i,DifferentiableAt ℝ (M i) p := fun i => (hM i).differentiableAt (by simp)
  have hdf : ∀z,DifferentiableAt ℝ (dir z f) p := fun z => (smooth_dir_at hf z).differentiableAt (by simp)
  have hterm (i : ι) : DifferentiableAt ℝ (fun y => M i y*dir (b i) f y) p :=
    (hMi i).mul (hdf (b i))
  have hsum : DifferentiableAt ℝ (fun y => ∑i,M i y*dir (b i) f y) p :=
    DifferentiableAt.fun_sum fun i _ => hterm i
  have he : dir v (mdir w b r M f) p=dir v (dir w f) p-
      r*∑i,(dir v (M i) p*dir (b i) f p+M i p*dir v (dir (b i) f) p) := by
    unfold mdir
    rw [dir_sub_at (hdf w) (hsum.const_mul r),dir_const_mul_at hsum,
      dir_sum_at Finset.univ (fun i _ => hterm i)]
    simp_rw [dir_mul_at (hMi _) (hdf _)]
  rw [he]
  unfold mdir
  simp_rw [dir_dir_at hf v]
  rw [Finset.sum_add_distrib]
  ring

lemma smooth_cadj_at (v : E) {s f : E → ℝ} {p : E}
    (hs : ContDiffAt ℝ (⊤:ℕ∞) s p) (hf : ContDiffAt ℝ (⊤:ℕ∞) f p) :
    ContDiffAt ℝ (⊤:ℕ∞) (cadj v s f) p :=
  (smooth_dir_at hf v).neg.add (hs.mul hf)

lemma gadj_mul_at (b : ι → E) (s : ι → E → ℝ) {V : ι → E → ℝ} {p : E}
    (hV : ∀i,DifferentiableAt ℝ (V i) p) {f : E → ℝ} (hf : DifferentiableAt ℝ f p) :
    gadj b s (fun i p => V i p*f p) p=gadj b s V p*f p-∑i,V i p*dir (b i) f p := by
  unfold gadj cadj
  simp_rw [dir_mul_at (hV _) hf]
  rw [Finset.sum_mul,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma gadj_sum_at {N : Type*} (a : Finset N) (b : ι → E) (s : ι → E → ℝ)
    {V : N → ι → E → ℝ} {p : E} (hV : ∀n∈a,∀i,DifferentiableAt ℝ (V n i) p) :
    gadj b s (fun i p => ∑n∈a,V n i p) p=∑n∈a,gadj b s (V n) p := by
  unfold gadj cadj
  simp_rw [dir_sum_at a (fun n hn => hV n hn _)]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [Finset.sum_add_distrib,Finset.sum_neg_distrib]

theorem mdir_cadj_at (w : E) (b : ι → E) (r : ℝ)
    {M s : ι → E → ℝ} {f : E → ℝ} {p : E}
    (hM : ∀i,ContDiffAt ℝ (⊤:ℕ∞) (M i) p)
    (hs : ∀i,ContDiffAt ℝ (⊤:ℕ∞) (s i) p) (hf : ContDiffAt ℝ (⊤:ℕ∞) f p) (i : ι)
    (hsi : mdir w b r M (s i) p=r*gadj b s (fun k => dir (b i) (M k)) p) :
    mdir w b r M (cadj (b i) (s i) f) p=
      cadj (b i) (s i) (mdir w b r M f) p+
        r*gadj b s (fun k p => dir (b i) (M k) p*f p) p := by
  have hdf := smooth_dir_at hf (b i)
  have hMi (k : ι) := smooth_dir_at (hM k) (b i)
  have he : cadj (b i) (s i) f=fun p => (-1)*dir (b i) f p+s i p*f p := by
    funext p; simp [cadj]
  rw [he,mdir_add_at w b r M ((contDiffAt_const.mul hdf).differentiableAt (by simp))
    (((hs i).mul hf).differentiableAt (by simp))]
  rw [mdir_const_mul_at w b r M (hdf.differentiableAt (by simp)),
      mdir_mul_at w b r M ((hs i).differentiableAt (by simp)) (hf.differentiableAt (by simp)),
      mdir_dir_at w b r hM hf,hsi,
      gadj_mul_at b s (fun k => (hMi k).differentiableAt (by simp)) (hf.differentiableAt (by simp))]
  simp only [cadj]
  ring

theorem mdir_gadj_at (w : E) (b : ι → E) (r : ℝ)
    {M s V : ι → E → ℝ} {p : E}
    (hM : ∀i,ContDiffAt ℝ (⊤:ℕ∞) (M i) p)
    (hs : ∀i,ContDiffAt ℝ (⊤:ℕ∞) (s i) p) (hV : ∀i,ContDiffAt ℝ (⊤:ℕ∞) (V i) p)
    (hscore : ∀i,mdir w b r M (s i) p=r*gadj b s (fun k => dir (b i) (M k)) p) :
    mdir w b r M (gadj b s V) p=
      gadj b s (fun i => mdir w b r M (V i)) p+
      r*gadj b s (fun k p => ∑i,dir (b i) (M k) p*V i p) p := by
  change mdir w b r M (fun p => ∑i,cadj (b i) (s i) (V i) p) p=_
  rw [mdir_sum_at Finset.univ w b r M (fun i _ =>
    (smooth_cadj_at (b i) (hs i) (hV i)).differentiableAt (by simp))]
  simp_rw [mdir_cadj_at w b r hM hs (hV _) _ (hscore _)]
  have hD (i k : ι) : DifferentiableAt ℝ (fun p => dir (b i) (M k) p*V i p) p :=
    ((smooth_dir_at (hM k) (b i)).mul (hV i)).differentiableAt (by simp)
  rw [gadj_sum_at Finset.univ b s (fun i _ k => hD i k)]
  simp only [Finset.sum_add_distrib,Finset.mul_sum,gadj]

end LogConcaveSampling.JetCalculus

end

end

section

noncomputable section
namespace LogConcaveSampling.JetCalculus
open Filter
open scoped Topology Classical BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι κ : Type*} [Fintype ι]

lemma dir_eventuallyEq {f g : E → ℝ} {p : E} (h : f=ᶠ[nhds p]g) (v : E) :
    dir v f=ᶠ[nhds p]dir v g := by
  filter_upwards [h.fderiv (𝕜:=ℝ)] with y hy
  simp only [dir,hy]

lemma jet_eventuallyEq {f g : E → ℝ} {p : E} (h : f=ᶠ[nhds p]g) (v : κ → E) (l : List κ) :
    jet v l f=ᶠ[nhds p]jet v l g := by
  induction l with
  | nil => exact h
  | cons i l ih => exact dir_eventuallyEq ih (v i)

lemma mdir_eventuallyEq (w : E) (b : ι → E) (r : ℝ)
    {M N : ι → E → ℝ} {f g : E → ℝ} {p : E}
    (hM : ∀i,M i=ᶠ[nhds p]N i) (hf : f=ᶠ[nhds p]g) :
    mdir w b r M f=ᶠ[nhds p]mdir w b r N g := by
  have hMd : ∀ᶠy in nhds p,∀i,M i y=N i y := eventually_all.mpr hM
  have hfd : ∀ᶠy in nhds p,∀i,dir (b i) f y=dir (b i) g y :=
    eventually_all.mpr (fun i => dir_eventuallyEq hf (b i))
  filter_upwards [hMd,hfd,dir_eventuallyEq hf w] with y hM hf hw
  simp only [mdir,hM,hf,hw]

lemma gadj_eventuallyEq (b : ι → E) {s t V W : ι → E → ℝ} {p : E}
    (hs : ∀i,s i=ᶠ[nhds p]t i) (hV : ∀i,V i=ᶠ[nhds p]W i) :
    gadj b s V=ᶠ[nhds p]gadj b t W := by
  have hs' : ∀ᶠy in nhds p,∀i,s i y=t i y := eventually_all.mpr hs
  have hV' : ∀ᶠy in nhds p,∀i,V i y=W i y := eventually_all.mpr hV
  have hVd : ∀ᶠy in nhds p,∀i,dir (b i) (V i) y=dir (b i) (W i) y :=
    eventually_all.mpr (fun i => dir_eventuallyEq (hV i) (b i))
  filter_upwards [hs',hV',hVd] with y hs hV hVd
  simp only [gadj,cadj,hs,hV,hVd]

lemma smooth_jet_at {f : E → ℝ} {p : E} (hf : ContDiffAt ℝ (⊤:ℕ∞) f p)
    (v : κ → E) (l : List κ) : ContDiffAt ℝ (⊤:ℕ∞) (jet v l f) p := by
  induction l with
  | nil => exact hf
  | cons i l ih => exact smooth_dir_at ih (v i)

def TimeSmooth (f : ℝ × E → ℝ) : Prop :=
  ∀p : ℝ × E,-1<p.1 → p.1<1 → ContDiffAt ℝ (⊤:ℕ∞) f p

lemma TimeSmooth.localize {f : ℝ × E → ℝ} (hf : TimeSmooth f) {p : ℝ × E}
    (h0 : -1<p.1) (h1 : p.1<1) :
    ∃g : ℝ × E → ℝ, ContDiff ℝ (⊤:ℕ∞) g ∧ g=ᶠ[nhds p]f := by
  obtain ⟨g,hg,he⟩ := smooth_time_localization h0 h1 hf
  refine ⟨g,hg,?_⟩
  have hh := (continuousAt_fst (p:=p)).eventually he
  filter_upwards [hh] with q hq
  exact hq q.2

theorem mdir_jet_time [DecidableEq κ] (w : ℝ × E) (b : ι → ℝ × E) (r : ℝ)
    {M : ι → ℝ × E → ℝ} (hM : ∀i,TimeSmooth (M i))
    {f : ℝ × E → ℝ} (hf : TimeSmooth f)
    (v : κ → ℝ × E) (l : List κ) (hl : l.Nodup)
    {p : ℝ × E} (h0 : -1<p.1) (h1 : p.1<1) :
    mdir w b r M (jet v l f) p=jet v l (mdir w b r M f) p+
      r*∑s∈l.toFinset.powerset.erase ∅,∑i,
        jet v (l.filter (fun j => j∈s)) (M i) p*
          dir (b i) (jet v (l.filter (fun j => j∉s)) f) p := by
  choose N hN heN using fun i => (hM i).localize h0 h1
  obtain ⟨g,hg,heg⟩ := hf.localize h0 h1
  have hleft := (mdir_eventuallyEq w b r heN (jet_eventuallyEq heg v l)).eq_of_nhds
  have hright := (jet_eventuallyEq (mdir_eventuallyEq w b r heN heg) v l).eq_of_nhds
  rw [←hleft,congrFun (mdir_jet w b r hN hg v l hl) p,hright]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro i _
  rw [(jet_eventuallyEq (heN i) v _).eq_of_nhds,
    (dir_eventuallyEq (jet_eventuallyEq heg v _) (b i)).eq_of_nhds]

end LogConcaveSampling.JetCalculus

end

end

end

end OAI
