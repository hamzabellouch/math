import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationScaleSup

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff Topology
open MeasureTheory Set Complex
namespace SevenEighths.CenteredMomentScaleSupremum
open HeckeFamily HeckeDyadic HeckeDetectorRowwise HeckeDetectorDyadicBridge
open HeckeInverseAmplification (scaleProfile scaleProfile_continuous scaleProfile_support
  scale_normalization scaleSupport scaleSupport_cover)
def scaleSum (χ : Character) (inv : Bool) (W : ℝ→ℂ) (S : Finset (Ideal O)) (l : ℝ) : ℂ :=
  Complex.exp (-(l : ℂ)/2)*∑ J∈S,
    coefficient χ inv J*W ((J.absNorm : ℝ)*Real.exp (-l))

theorem scaleSum_continuous (χ : Character) (inv : Bool) (W : ℝ→ℂ) (S : Finset (Ideal O))
    (hW : Continuous W) : Continuous (scaleSum χ inv W S) := by
  unfold scaleSum
  fun_prop

theorem scaleSum_deriv (χ : Character) (inv : Bool) (W : ℝ→ℂ) (S : Finset (Ideal O))
    (hW : Differentiable ℝ W) (l : ℝ) :
    HasDerivAt (scaleSum χ inv W S) (scaleSum χ inv (scaleProfile W) S l) l := by
  have hE : HasDerivAt (fun t : ℝ => Complex.exp (-(t : ℂ)/2))
      (Complex.exp (-(l : ℂ)/2)*(-(1 : ℂ)/2)) l := by
    convert ((Complex.ofRealCLM.hasDerivAt (x:=l)).neg.div_const (2 : ℂ)).cexp using 1
    all_goals rfl
  have hd (J : Ideal O) (hJ : J∈S) :
      HasDerivAt (fun t => coefficient χ inv J*W ((J.absNorm : ℝ)*Real.exp (-t)))
        (coefficient χ inv J*(deriv W ((J.absNorm : ℝ)*Real.exp (-l))*
          (-((J.absNorm : ℝ)*Real.exp (-l)) : ℝ))) l := by
    have hy := ((hasDerivAt_id l).neg.exp).const_mul (J.absNorm : ℝ)
    convert ((hW _).hasDerivAt.scomp l hy).const_mul (coefficient χ inv J) using 1
    · rfl
    · change coefficient χ inv J*(deriv W ((J.absNorm : ℝ)*Real.exp (-l))*
          (-((J.absNorm : ℝ)*Real.exp (-l)) : ℝ))=
        coefficient χ inv J*(((J.absNorm : ℝ)*(Real.exp (-l)*(-1))) •
          deriv W ((J.absNorm : ℝ)*Real.exp (-l)))
      rw [Complex.real_smul]
      push_cast
      ring
  convert hE.mul (HasDerivAt.sum (u:=S) hd) using 1
  · ext t
    simp only [scaleSum,Pi.mul_apply,Finset.sum_apply]
  · dsimp [scaleSum,scaleProfile]
    simp only [Finset.sum_apply]
    simp_rw [Finset.mul_sum]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro J hJ
    push_cast
    ring

theorem scaleSum_eq_polynomial (χ : Character) (inv : Bool) (W : ℝ→ℂ) (S : Finset (Ideal O))
    (l : ℝ) (hc : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/Real.exp l)≠0 → J∈S) :
    scaleSum χ inv W S l=polynomial χ inv W (Real.exp l) 0 0 := by
  rw [polynomial_eq_finite χ inv W (Real.exp l) 0 0 S hc,scale_normalization]
  simp only [HeckeDyadic.shift,ofReal_zero,zero_mul,sub_self,neg_zero,Complex.cpow_zero,mul_one]
  unfold scaleSum
  congr 1
  apply Finset.sum_congr rfl
  intro J hJ
  rw [Real.exp_neg,div_eq_mul_inv]

def scaleTest (W : ℝ→ℂ) (j : Fin 2) : ℝ→ℂ :=
  if j=0 then W else scaleProfile W

lemma scaleTest_continuous (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (j : Fin 2) :
    Continuous (scaleTest W j) := by
  unfold scaleTest
  split
  · exact hW.continuous
  · exact scaleProfile_continuous W hW

lemma scaleTest_support (W : ℝ→ℂ) (a b : ℝ)
    (hs : Function.support W⊆Icc a b) (j : Fin 2) :
    Function.support (scaleTest W j)⊆Icc a b := by
  unfold scaleTest
  split
  · exact hs
  · exact scaleProfile_support W a b hs

theorem paired_rowwise_scales {ι : Type*} (rows : Finset ι)
    (χ ψ : ι→Character) (P : ι→ℂ) (W V : ℝ→ℂ)
    (a b c d : ℝ) (hb : 0≤b) (hd : 0≤d)
    (hWs : Function.support W⊆Icc a b) (hVs : Function.support V⊆Icc c d)
    (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V)
    (lo hi low high E : ℝ) (hlh : lo≤hi) (hlw : low≤high) (lx ly : ι→ℝ)
    (hlx : ∀ i∈rows,lx i∈Icc lo hi) (hly : ∀ i∈rows,ly i∈Icc low high)
    (henergy : ∀ j k : Fin 2,∀ x∈Icc lo hi,∀ y∈Icc low high,
      ∑ i∈rows,‖polynomial (χ i) false (scaleTest W j) (Real.exp x) 0 0 *
        polynomial (ψ i) false (scaleTest V k) (Real.exp y) 0 0 * P i‖^2≤E) :
    ∑ i∈rows,‖polynomial (χ i) false W (Real.exp (lx i)) 0 0 *
      polynomial (ψ i) false V (Real.exp (ly i)) 0 0 * P i‖^2≤
      (1+2*(hi-lo))*((1+2*(high-low))*E) := by
  let S := scaleSupport hi b
  let T := scaleSupport high d
  let F (j k : Fin 2) (i : ι) (x y : ℝ) :=
    scaleSum (χ i) false (scaleTest W j) S x *
      scaleSum (ψ i) false (scaleTest V k) T y * P i
  have eqW (i : ι) (j : Fin 2) (x : ℝ) (hx : x∈Icc lo hi) :=
    scaleSum_eq_polynomial (χ i) false (scaleTest W j) S x
      (scaleSupport_cover _ a b hi x hb (scaleTest_support W a b hWs j) hx.2)
  have eqV (i : ι) (k : Fin 2) (y : ℝ) (hy : y∈Icc low high) :=
    scaleSum_eq_polynomial (ψ i) false (scaleTest V k) T y
      (scaleSupport_cover _ c d high y hd (scaleTest_support V c d hVs k) hy.2)
  have hc (j k : Fin 2) (i : ι) : Continuous (Function.uncurry (F j k i)) := by
    exact (((scaleSum_continuous (χ i) false _ S (scaleTest_continuous W hW j)).comp
      continuous_fst).mul ((scaleSum_continuous (ψ i) false _ T
      (scaleTest_continuous V hV k)).comp continuous_snd)).mul continuous_const
  have hx (k : Fin 2) (i : ι) (x y : ℝ) :
      HasDerivAt (fun u=>F 0 k i u y) (F 1 k i x y) x := by
    simpa [F,scaleTest] using
      (scaleSum_deriv (χ i) false W S (hW.differentiable (by simp)) x).mul_const
        (scaleSum (ψ i) false (scaleTest V k) T y) |>.mul_const (P i)
  have hy (j : Fin 2) (i : ι) (x y : ℝ) :
      HasDerivAt (F j 0 i x) (F j 1 i x y) y := by
    simpa [F,scaleTest] using
      ((scaleSum_deriv (ψ i) false V T (hV.differentiable (by simp)) y).const_mul
        (scaleSum (χ i) false (scaleTest W j) S x)).mul_const (P i)
  have hh := rowwise_energy_two rows F (fun j k i _=>hc j k i)
    (fun k i _ x y=>hx k i x y) (fun j i _ x y=>hy j i x y)
    lo hi low high E hlh hlw lx ly hlx hly (by
      intro j k x hx y hy
      simpa only [F,eqW _ j x hx,eqV _ k y hy] using henergy j k x hx y hy)
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only [F]
  rw [eqW i 0 (lx i) (hlx i hi),eqV i 0 (ly i) (hly i hi)]
  simp only [scaleTest,ite_true]

theorem exists_paired_scale_majorant {ι : Type*} (rows : Finset ι)
    (χ ψ : ι→Character) (P : ι→ℂ) (W V : ℝ→ℂ)
    (a b c d : ℝ) (hb : 0≤b) (hd : 0≤d)
    (hWs : Function.support W⊆Icc a b) (hVs : Function.support V⊆Icc c d)
    (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V)
    (lo hi low high E : ℝ) (hlh : lo≤hi) (hlw : low≤high)
    (henergy : ∀ j k : Fin 2,∀ x∈Icc lo hi,∀ y∈Icc low high,
      ∑ i∈rows,‖polynomial (χ i) false (scaleTest W j) (Real.exp x) 0 0 *
        polynomial (ψ i) false (scaleTest V k) (Real.exp y) 0 0 * P i‖^2≤E) :
    ∃ B : ι→ℝ,(∀i,0≤B i) ∧
      (∀i,∀ x∈Icc lo hi,∀ y∈Icc low high,
        ‖polynomial (χ i) false W (Real.exp x) 0 0 *
          polynomial (ψ i) false V (Real.exp y) 0 0 * P i‖^2≤B i) ∧
      (∑ i∈rows,B i)≤(1+2*(hi-lo))*((1+2*(high-low))*E) := by
  let S := scaleSupport hi b
  let T := scaleSupport high d
  let F (i : ι) (p : ℝ×ℝ) :=
    scaleSum (χ i) false W S p.1 * scaleSum (ψ i) false V T p.2 * P i
  have hc (i : ι) : Continuous (F i) :=
    (((scaleSum_continuous (χ i) false W S hW.continuous).comp continuous_fst).mul
      ((scaleSum_continuous (ψ i) false V T hV.continuous).comp continuous_snd)).mul continuous_const
  have heq (i : ι) (x y : ℝ) (hx : x∈Icc lo hi) (hy : y∈Icc low high) :
      F i (x,y)=polynomial (χ i) false W (Real.exp x) 0 0 *
        polynomial (ψ i) false V (Real.exp y) 0 0 * P i := by
    dsimp only [F]
    rw [scaleSum_eq_polynomial (χ i) false W S x
      (scaleSupport_cover W a b hi x hb hWs hx.2),
      scaleSum_eq_polynomial (ψ i) false V T y
      (scaleSupport_cover V c d high y hd hVs hy.2)]
  have hm (i : ι) : ∃p∈(Icc lo hi)×ˢ(Icc low high),
      ∀q∈(Icc lo hi)×ˢ(Icc low high),‖F i q‖^2≤‖F i p‖^2 := by
    exact (isCompact_Icc.prod isCompact_Icc).exists_isMaxOn
      ((nonempty_Icc.mpr hlh).prod (nonempty_Icc.mpr hlw)) ((hc i).norm.pow 2).continuousOn
  choose p hp hmax using hm
  refine ⟨fun i=>‖F i (p i)‖^2,fun i=>sq_nonneg _,?_,?_⟩
  · intro i x hx y hy
    have hh := hmax i (x,y) ⟨hx,hy⟩
    rwa [heq i x y hx hy] at hh
  · have hh := paired_rowwise_scales rows χ ψ P W V a b c d hb hd hWs hVs hW hV
      lo hi low high E hlh hlw (fun i=>(p i).1) (fun i=>(p i).2)
      (fun i _=>(hp i).1) (fun i _=>(hp i).2) henergy
    convert hh using 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [←heq i (p i).1 (p i).2 (hp i).1 (hp i).2]

end SevenEighths.CenteredMomentScaleSupremum

end

end OAI
