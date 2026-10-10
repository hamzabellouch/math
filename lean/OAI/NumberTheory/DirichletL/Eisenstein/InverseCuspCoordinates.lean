import OAI.NumberTheory.DirichletL.Eisenstein.BesselDerivatives

namespace OAI

noncomputable section

namespace CubicEisenstein

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ComplexConjugate MatrixGroups Matrix

def inverseCuspCoordinates (c d : ℂ) (v : ℝ) (z : ℂ) : ℂ×ℝ :=
  (-d/c-star z/(c^2*((v^2+‖z‖^2:ℝ):ℂ)),v/(‖c‖^2*(v^2+‖z‖^2)))

lemma inverseCuspCoordinates_height_pos (c d : ℂ) (v : ℝ) (z : ℂ)
    (hc : c≠0) (hv : 0<v) : 0<(inverseCuspCoordinates c d v z).2 := by
  dsimp [inverseCuspCoordinates]
  positivity

lemma inverseCuspCoordinates_line (c d : ℂ) (v : ℝ) (direction : ℂ) (t : ℝ) :
    inverseCuspCoordinates c d v ((t:ℂ)*direction)=inverseCuspPath c d v direction t := by
  simp only [inverseCuspCoordinates,inverseCuspPath,star_mul,Complex.star_def,
    Complex.conj_ofReal,norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs,mul_comm]

theorem inverse_cusp_action (g : SL(2,ℂ)) (hc : g 1 0≠0)
    (v : ℝ) (hv : 0<v) (z : ℂ) :
    g⁻¹ • upperPoint (z+g 0 0/g 1 0) v hv =
      upperPoint (inverseCuspCoordinates (g 1 0) (g 1 1) v z).1
        (inverseCuspCoordinates (g 1 0) (g 1 1) v z).2
        (inverseCuspCoordinates_height_pos _ _ _ _ hc hv) := by
  have hdet : g 0 0*g 1 1-g 0 1*g 1 0=1 := by
    simpa only [Matrix.det_fin_two] using g.property
  have h00 : (g⁻¹) 0 0=g 1 1 := by
    simp [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two]
  have h01 : (g⁻¹) 0 1= -g 0 1 := by
    simp [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two]
  have h10 : (g⁻¹) 1 0= -g 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two]
  have h11 : (g⁻¹) 1 1=g 0 0 := by
    simp [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two]
  have hl : (-g 1 0)*(z+g 0 0/g 1 0)+g 0 0= -(g 1 0*z) := by
    field_simp
    ; ring
  have ht : g 1 1*(z+g 0 0/g 1 0)+(-g 0 1)=g 1 1*z+1/g 1 0 := by
    field_simp
    linear_combination hdet
  have hden : ‖-(g 1 0*z)‖^2+‖-g 1 0‖^2*v^2=
      ‖g 1 0‖^2*(v^2+‖z‖^2) := by rw [norm_neg,norm_neg,norm_mul,mul_pow];ring
  have hnormc : ((‖g 1 0‖^2:ℝ):ℂ)=g 1 0*star (g 1 0) := by
    simpa [Complex.normSq_eq_norm_sq,Complex.star_def] using (Complex.mul_conj (g 1 0)).symm
  have hnormz : ((‖z‖^2:ℝ):ℂ)=z*star z := by
    simpa [Complex.normSq_eq_norm_sq,Complex.star_def] using (Complex.mul_conj z).symm
  have hT : v^2+‖z‖^2≠0 := by positivity
  have hTc : ((v^2+‖z‖^2:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr hT
  have hcc : star (g 1 0)≠0 := star_ne_zero.mpr hc
  rw [mobius_upperPoint]
  apply upperPoint_congr
  · rw [h00,h01,h10,h11,hl,ht,hden]
    dsimp [inverseCuspCoordinates]
    rw [Complex.ofReal_mul,hnormc]
    simp only [Complex.star_def,map_neg,map_mul]
    simp only [Complex.star_def] at hcc
    field_simp [hc,hcc,hTc]
    rw [Complex.ofReal_add,Complex.ofReal_pow,hnormz]
    simp only [Complex.star_def,]
    ; ring
  · rw [h10,h11,hl,hden]
    rfl

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ComplexConjugate

lemma real_linear_horizontal_decompose (A : (ℂ×ℝ)→L[ℝ]ℂ) (z : ℂ) :
    A (z,0)=(z.re:ℂ)*A (1,0)+(z.im:ℂ)*A (Complex.I,0) := by
  have hz : ((z,0):ℂ×ℝ)=z.re • (1,0)+z.im • (Complex.I,0) := by
    apply Prod.ext
    · simpa only [Prod.fst_add,Prod.smul_fst,Complex.real_smul,mul_one] using z.re_add_im.symm
    · simp
  rw [hz,map_add,map_smul,map_smul]
  simp only [Complex.real_smul]

lemma real_linear_wirtinger_swap (A : (ℂ×ℝ)→L[ℝ]ℂ) (k : ℂ) :
    (1/2:ℂ)*(A (k,0)+Complex.I*A (-Complex.I*k,0))=
      k*((1/2:ℂ)*(A (1,0)-Complex.I*A (Complex.I,0))) := by
  rw [real_linear_horizontal_decompose A k,real_linear_horizontal_decompose A (-Complex.I*k)]
  simp only [Complex.mul_re,Complex.mul_im,Complex.neg_re,Complex.neg_im,
    Complex.I_re,Complex.I_im,zero_mul,neg_mul,one_mul,
    zero_add,zero_sub,Complex.ofReal_neg]
  conv_rhs => lhs; rw [←k.re_add_im]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem inverse_cusp_wirtingerBar (c d : ℂ) (v : ℝ) (hc : c≠0) (hv : 0<v)
    (F : ℂ×ℝ→ℂ) (A : (ℂ×ℝ)→L[ℝ]ℂ)
    (hF : HasFDerivAt F A (-d/c,1/(‖c‖^2*v))) :
    horizontalWirtingerBar (fun z=>F (inverseCuspCoordinates c d v z)) 0=
      (-1/(c^2*(v:ℂ)^2))*((1/2:ℂ)*(A (1,0)-Complex.I*A (Complex.I,0))) := by
  have h1 := (inverseCuspPath_comp_hasDerivAt c d v 1 hc hv F A hF).deriv
  have hI := (inverseCuspPath_comp_hasDerivAt c d v Complex.I hc hv F A hF).deriv
  have he1 : (fun t : ℝ=>F (inverseCuspCoordinates c d v (t:ℂ)))=
      (fun t : ℝ=>F (inverseCuspPath c d v 1 t)) := by
    funext t
    rw [←inverseCuspCoordinates_line]
    simp only [mul_one]
  have heI : (fun t : ℝ=>F (inverseCuspCoordinates c d v ((t:ℂ)*Complex.I)))=
      (fun t : ℝ=>F (inverseCuspPath c d v Complex.I t)) := by
    funext t
    rw [inverseCuspCoordinates_line]
  rw [horizontalWirtingerBar]
  simp only [zero_add]
  rw [he1,heI,h1,hI]
  simp only [star_one,Complex.star_def,Complex.conj_I,neg_neg]
  convert real_linear_wirtinger_swap A (-1/(c^2*(v:ℂ)^2)) using 1 ;
    congr 2 ; ring_nf

def horizontalWirtingerZ (f : ℂ→ℂ) (z : ℂ) : ℂ :=
  (1/2:ℂ)*(deriv (fun t : ℝ=>f (z+(t:ℂ))) 0-
    Complex.I*deriv (fun t : ℝ=>f (z+(t:ℂ)*Complex.I)) 0)

lemma horizontalWirtingerZ_eq_fderiv (F : ℂ×ℝ→ℂ) (A : (ℂ×ℝ)→L[ℝ]ℂ)
    (z : ℂ) (v : ℝ) (hF : HasFDerivAt F A (z,v)) :
    horizontalWirtingerZ (fun w=>F (w,v)) z=
      (1/2:ℂ)*(A (1,0)-Complex.I*A (Complex.I,0)) := by
  have hline (direction : ℂ) :
      HasDerivAt (fun t : ℝ=>F (z+(t:ℂ)*direction,v)) (A (direction,0)) 0 := by
    have hz : HasDerivAt (fun t : ℝ=>z+(t:ℂ)*direction) direction 0 := by
      simpa using (((hasDerivAt_id (0:ℝ)).ofReal_comp.mul_const direction).const_add z)
    have hp := hz.prodMk (hasDerivAt_const (0:ℝ) v)
    have hf : HasFDerivAt F A (z+(0:ℂ)*direction,v) := by simpa using hF
    exact hf.comp_hasDerivAt 0 hp
  have h1 := (hline 1).deriv
  have hI := (hline Complex.I).deriv
  simp only [mul_one] at h1
  rw [horizontalWirtingerZ,h1,hI]

theorem inverse_cusp_wirtinger_rule (c d : ℂ) (v : ℝ) (hc : c≠0) (hv : 0<v)
    (F : ℂ×ℝ→ℂ) (A : (ℂ×ℝ)→L[ℝ]ℂ)
    (hF : HasFDerivAt F A (-d/c,1/(‖c‖^2*v))) :
    horizontalWirtingerBar (fun z=>F (inverseCuspCoordinates c d v z)) 0=
      (-1/(c^2*(v:ℂ)^2))*
        horizontalWirtingerZ (fun z=>F (z,1/(‖c‖^2*v))) (-d/c) := by
  rw [horizontalWirtingerZ_eq_fderiv F A _ _ hF]
  exact inverse_cusp_wirtingerBar c d v hc hv F A hF

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology

section

theorem cusp_mellin_reflection (g : ℝ→ℂ) (A s : ℂ) (Q : ℝ) (hQ : 0<Q) :
    mellin (fun v : ℝ=>A*((v:ℂ)^(-2:ℂ)*g ((Q*v)⁻¹))) (2*s)=
      A*(Q:ℂ)^(2-2*s)*mellin g (2-2*s) := by
  have he : (fun v : ℝ=>A*((v:ℂ)^(-2:ℂ)*g ((Q*v)⁻¹)))=
      (fun v : ℝ=>A • ((v:ℂ)^(-2:ℂ) • g ((Q*v)⁻¹))) := by
    funext v; simp only [smul_eq_mul]
  rw [he,mellin_const_smul,mellin_cpow_smul]
  have hm := mellin_comp_mul_left (fun v : ℝ=>g v⁻¹) (2*s+(-2:ℂ)) hQ
  rw [mellin_comp_inv] at hm
  rw [hm]
  simp only [smul_eq_mul]
  rw [show -(2*s+(-2:ℂ))=2-2*s by ring]
  ring

theorem cusp_mellin_reflection_of_identity (f g : ℝ→ℂ) (A s : ℂ)
    (Q : ℝ) (hQ : 0<Q)
    (hfg : ∀v : ℝ,0<v→f v=A*((v:ℂ)^(-2:ℂ)*g ((Q*v)⁻¹))) :
    mellin f (2*s)=A*(Q:ℂ)^(2-2*s)*mellin g (2-2*s) := by
  rw [←cusp_mellin_reflection g A s Q hQ]
  unfold mellin
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  rw [hfg v hv]

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

def horizontalPhaseCLM (freq : ℂ) : ℂ →L[ℝ] ℂ :=
  (2*Real.pi*Complex.I:ℂ) •
    (freq • ContinuousLinearMap.id ℝ ℂ +
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (freq • ContinuousLinearMap.id ℝ ℂ))

lemma horizontalPhaseCLM_apply (freq direction : ℂ) :
    horizontalPhaseCLM freq direction = horizontalPhaseMultiplier freq direction := by
  simp [horizontalPhaseCLM,horizontalPhaseMultiplier]
  ring

lemma brevePhase_hasFDerivAt (freq z : ℂ) :
    HasFDerivAt (fun w : ℂ => ShortDraftTrace.breveE (freq*w))
      (ShortDraftTrace.breveE (freq*z) • horizontalPhaseCLM freq) z := by
  have hh := (horizontalPhaseCLM freq).hasFDerivAt.cexp (x:=z)
  convert! hh using 1

namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

def amplitudeDeriv (v : ℝ) (h : ActualEisensteinCubic.O) : ℂ :=
  if h=0 then 0 else coeff.value h*
    (schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)+
      (v:ℂ)*(4*Real.pi*‖cuspFrequency h‖:ℝ)*
        schlafliBesselK_cubic_derivative (4*Real.pi*‖cuspFrequency h‖*v))

lemma amplitude_hasDerivAt (v : ℝ) (hv : 0<v) (h : ActualEisensteinCubic.O) :
    HasDerivAt (fun y : ℝ => coeff.amplitude y h) (coeff.amplitudeDeriv v h) v := by
  by_cases hh : h=0
  · simp only [amplitude,amplitudeDeriv,ite_eq_left hh]
    exact hasDerivAt_const v 0
  have hr : 0<‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
  have hslope : HasDerivAt (fun y : ℝ => 4*Real.pi*‖cuspFrequency h‖*y)
      (4*Real.pi*‖cuspFrequency h‖) v := by
    simpa only [id_eq,mul_one] using (hasDerivAt_id v).const_mul (4*Real.pi*‖cuspFrequency h‖)
  have hk := (schlafliBesselK_cubic_hasDerivAt (4*Real.pi*‖cuspFrequency h‖*v)
    (by positivity)).scomp v hslope
  have hvd := (Complex.ofRealCLM.hasDerivAt (x:=v)).mul hk
  have hfull := hvd.const_mul (coeff.value h)
  simp only [amplitude,amplitudeDeriv,ite_eq_right hh]
  convert! hfull using 1 <;> simp [Function.comp_def,Pi.mul_apply,Complex.ofRealCLM_apply,Complex.real_smul,mul_assoc]

def termFDeriv (h : ActualEisensteinCubic.O) (p : ℝ × ℂ) : (ℝ × ℂ) →L[ℝ] ℂ :=
  if h=0 then 0 else
    (ContinuousLinearMap.fst ℝ ℝ ℂ).smulRight
      (coeff.amplitudeDeriv p.1 h*ShortDraftTrace.breveE (cuspFrequency h*p.2))+
    coeff.term h p • (horizontalPhaseCLM (cuspFrequency h)).comp
      (ContinuousLinearMap.snd ℝ ℝ ℂ)

lemma term_hasFDerivAt (h : ActualEisensteinCubic.O) (p : ℝ × ℂ) (hp : 0<p.1) :
    HasFDerivAt (coeff.term h) (coeff.termFDeriv h p) p := by
  by_cases hh : h=0
  · have hzero : coeff.term h=(fun _ : ℝ × ℂ => (0:ℂ)) := by
      funext q
      simp only [term,ite_eq_left hh]
    rw [hzero,termFDeriv,ite_eq_left hh]
    exact hasFDerivAt_const (𝕜:=ℝ) (0:ℂ) p
  have hvd := (coeff.amplitude_hasDerivAt p.1 hp h).hasFDerivAt.comp p
    (hasFDerivAt_fst (𝕜:=ℝ) (p:=p))
  have hzd := (brevePhase_hasFDerivAt (cuspFrequency h) p.2).comp p
    (hasFDerivAt_snd (𝕜:=ℝ) (p:=p))
  have hprod : HasFDerivAt (fun q : ℝ × ℂ => coeff.amplitude q.1 h*
      ShortDraftTrace.breveE (cuspFrequency h*q.2)) (coeff.termFDeriv h p) p := by
    convert! hvd.mul hzd using 1
    apply ContinuousLinearMap.ext
    intro direction
    simp only [termFDeriv,ite_eq_right hh]
    change (direction.1:ℂ)*(coeff.amplitudeDeriv p.1 h*
        ShortDraftTrace.breveE (cuspFrequency h*p.2))+
      coeff.term h p*horizontalPhaseCLM (cuspFrequency h) direction.2 =
      coeff.amplitude p.1 h*(ShortDraftTrace.breveE (cuspFrequency h*p.2)*
        horizontalPhaseCLM (cuspFrequency h) direction.2)+
      ShortDraftTrace.breveE (cuspFrequency h*p.2)*
        ((direction.1:ℂ)*coeff.amplitudeDeriv p.1 h)
    rw [coeff.term_eq_amplitude p.1 hp h p.2]
    ring
  apply hprod.congr_of_eventuallyEq
  filter_upwards [continuousAt_fst.tendsto.eventually (Ioi_mem_nhds hp)] with q hq
  exact coeff.term_eq_amplitude q.1 hq h q.2

end SubexponentialBesselCoefficients
end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

section
local notation "O" => ActualEisensteinCubic.O
namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

lemma weighted_bessel_bounds (a : ℝ) (ha : 0<a) :
    ∃A B : ℝ,0≤A ∧ 0≤B ∧ ∀(h : ActualEisensteinCubic.O),h≠0 → ∀v : ℝ,a≤v →
      ‖coeff.value h‖*‖schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)‖≤
        A*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖) ∧
      ‖coeff.value h‖*‖schlafliBesselK_cubic_derivative (4*Real.pi*‖cuspFrequency h‖*v)‖≤
        B*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖) := by
  have hd : 0<‖(3:ℂ)*ConcreteTraceCRT.eisLam‖ := norm_pos_iff.mpr
    (mul_ne_zero (by norm_num) ConcreteTraceCRT.eisLam_ne_zero)
  let delta : ℝ := 4*Real.pi*a*‖(3:ℂ)*ConcreteTraceCRT.eisLam‖⁻¹
  have hdelta : 0<delta := by dsimp [delta];positivity
  have hKu := (cubicBesselUpperAway_pos delta hdelta).le
  have hKd := cubicBesselDerivativeUpper_nonneg delta hdelta
  obtain ⟨C,hC,hcoeff⟩ := coeff.growth (Real.pi*a) (mul_pos Real.pi_pos ha)
  refine ⟨C*cubicBesselUpperAway delta,C*cubicBesselDerivativeUpper delta,
    mul_nonneg hC hKu,mul_nonneg hC hKd,?_⟩
  intro h hh v hv
  have hr : 0<‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
  have hx : delta≤4*Real.pi*‖cuspFrequency h‖*v := by
    have hmul := mul_le_mul (cuspFrequency_norm_lower h hh) hv ha.le (norm_nonneg _)
    dsimp [delta]
    nlinarith [mul_le_mul_of_nonneg_left hmul (by positivity : 0≤4*Real.pi)]
  have hcombine (y D : ℝ) (hy : 0≤y) (hD : 0≤D)
      (hbound : y≤D*Real.exp (-(4*Real.pi*‖cuspFrequency h‖*v)/2)) :
      ‖coeff.value h‖*y≤(C*D)*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖) := by
    calc
      _ ≤ (C*Real.exp ((Real.pi*a)*‖cuspFrequency h‖))*
          (D*Real.exp (-(4*Real.pi*‖cuspFrequency h‖*v)/2)) :=
        mul_le_mul (hcoeff h hh) hbound hy (by positivity)
      _ = (C*D)*Real.exp ((Real.pi*a)*‖cuspFrequency h‖-
          (4*Real.pi*‖cuspFrequency h‖*v)/2) := by
        rw [show (Real.pi*a)*‖cuspFrequency h‖-(4*Real.pi*‖cuspFrequency h‖*v)/2=
          (Real.pi*a)*‖cuspFrequency h‖+(-(4*Real.pi*‖cuspFrequency h‖*v)/2) by ring,
          Real.exp_add]
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC hD)
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hv (mul_pos Real.pi_pos hr).le]
  exact ⟨hcombine _ _ (norm_nonneg _) hKu
    (schlafliBesselK_cubic_upper_away delta _ hdelta hx),
    hcombine _ _ (norm_nonneg _) hKd
    (schlafliBesselK_cubic_derivative_bound delta _ hdelta hx)⟩

lemma amplitudeDeriv_norm_le (v : ℝ) (hv : 0<v) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    ‖coeff.amplitudeDeriv v h‖≤
      ‖coeff.value h‖*‖schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)‖+
      (v*(4*Real.pi*‖cuspFrequency h‖))*
        (‖coeff.value h‖*‖schlafliBesselK_cubic_derivative (4*Real.pi*‖cuspFrequency h‖*v)‖) := by
  rw [amplitudeDeriv,ite_eq_right hh,norm_mul]
  calc
    _ ≤ ‖coeff.value h‖*(‖schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)‖+
      ‖(v:ℂ)*(4*Real.pi*‖cuspFrequency h‖:ℝ)*
        schlafliBesselK_cubic_derivative (4*Real.pi*‖cuspFrequency h‖*v)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
    _ = _ := by
      rw [norm_mul,norm_mul,Complex.norm_of_nonneg hv.le,
        Complex.norm_of_nonneg (by positivity : 0≤4*Real.pi*‖cuspFrequency h‖)]
      ring

lemma termFDeriv_norm_le (h : ActualEisensteinCubic.O) (p : ℝ × ℂ) :
    ‖coeff.termFDeriv h p‖≤‖coeff.amplitudeDeriv p.1 h‖+
      ‖coeff.term h p‖*(4*Real.pi*‖cuspFrequency h‖) := by
  by_cases hh : h=0
  · simp only [termFDeriv,ite_eq_left hh,norm_zero]
    positivity
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro direction
  simp only [termFDeriv,ite_eq_right hh]
  change ‖(direction.1:ℂ)*(coeff.amplitudeDeriv p.1 h*
      ShortDraftTrace.breveE (cuspFrequency h*p.2))+
    coeff.term h p*horizontalPhaseCLM (cuspFrequency h) direction.2‖≤_
  calc
    _ ≤ ‖(direction.1:ℂ)*(coeff.amplitudeDeriv p.1 h*
        ShortDraftTrace.breveE (cuspFrequency h*p.2))‖+
      ‖coeff.term h p*horizontalPhaseCLM (cuspFrequency h) direction.2‖ := norm_add_le _ _
    _ = ‖direction.1‖*‖coeff.amplitudeDeriv p.1 h‖+
        ‖coeff.term h p‖*‖horizontalPhaseMultiplier (cuspFrequency h) direction.2‖ := by
      rw [norm_mul,norm_mul,Complex.norm_real,breveE_norm,mul_one,norm_mul,
        horizontalPhaseCLM_apply]
    _ ≤ ‖direction‖*‖coeff.amplitudeDeriv p.1 h‖+
        ‖coeff.term h p‖*((4*Real.pi*‖cuspFrequency h‖)*‖direction‖) := by
      gcongr
      · exact norm_fst_le direction
      · exact (horizontalPhaseMultiplier_norm _ _).trans (by
          gcongr
          exact norm_snd_le direction)
    _ = _ := by ring

lemma termFDeriv_slab_bound (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    ∃C : ℝ,0≤C ∧ ∀(h : ActualEisensteinCubic.O)(p : ℝ × ℂ),p.1∈Set.Icc a b →
      ‖coeff.termFDeriv h p‖≤C*((1+‖cuspFrequency h‖)*
        Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)) := by
  obtain ⟨A,B,hA,hB,hweighted⟩ := coeff.weighted_bessel_bounds a ha
  obtain ⟨T,hT,hterm⟩ := coeff.slab_bound a b ha hab
  let D := B*b*(4*Real.pi)+T*(4*Real.pi)
  have hb : 0<b := ha.trans_le hab
  have hD : 0≤D := by dsimp [D];positivity
  refine ⟨A+D,add_nonneg hA hD,?_⟩
  intro h p hp
  by_cases hh : h=0
  · simp only [termFDeriv,ite_eq_left hh,norm_zero]
    positivity
  have hv : 0<p.1 := ha.trans_le hp.1
  obtain ⟨hKu,hKd⟩ := hweighted h hh p.1 hp.1
  have hamp : ‖coeff.amplitudeDeriv p.1 h‖≤
      A*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)+
      (b*(4*Real.pi*‖cuspFrequency h‖))*
        (B*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)) := by
    apply (coeff.amplitudeDeriv_norm_le p.1 hv h hh).trans
    gcongr
    exact hp.2
  calc
    _ ≤ ‖coeff.amplitudeDeriv p.1 h‖+
        ‖coeff.term h p‖*(4*Real.pi*‖cuspFrequency h‖) := coeff.termFDeriv_norm_le h p
    _ ≤ (A*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)+
        (b*(4*Real.pi*‖cuspFrequency h‖))*(B*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)))+
        (T*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖))*(4*Real.pi*‖cuspFrequency h‖) := by
      gcongr
      exact hterm h p hp
    _ = (A+D*‖cuspFrequency h‖)*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖) := by
      dsimp [D]
      ring
    _ ≤ _ := by
      rw [←mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      nlinarith [mul_nonneg hA (norm_nonneg (cuspFrequency h))]

end SubexponentialBesselCoefficients
end

local notation "O" => ActualEisensteinCubic.O

lemma summable_one_add_norm_exp_neg_cuspFrequency (a : ℝ) (ha : 0<a) :
    Summable (fun h : ActualEisensteinCubic.O => (1+‖cuspFrequency h‖)*Real.exp (-a*‖cuspFrequency h‖)) := by
  simpa only [add_mul,one_mul] using
    (summable_exp_neg_cuspFrequency_norm a ha).add (summable_norm_mul_exp_neg_cuspFrequency a ha)

namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

lemma termFDeriv_summable (p : ℝ × ℂ) (hp : 0<p.1) :
    Summable (fun h : ActualEisensteinCubic.O => coeff.termFDeriv h p) := by
  obtain ⟨C,hC,hbound⟩ := coeff.termFDeriv_slab_bound p.1 p.1 hp le_rfl
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun h => norm_nonneg _)
    (fun h => hbound h p ⟨le_rfl,le_rfl⟩)
    ((summable_one_add_norm_exp_neg_cuspFrequency (Real.pi*p.1) (mul_pos Real.pi_pos hp)).mul_left C)

lemma series_hasFDerivAt (p : ℝ × ℂ) (hp : 0<p.1) :
    HasFDerivAt coeff.series (∑'h : ActualEisensteinCubic.O,coeff.termFDeriv h p) p := by
  let a := p.1/2
  let b := 2*p.1
  have ha : 0<a := by dsimp [a];linarith
  have hab : a≤b := by dsimp [a,b];linarith
  have hap : a<p.1 := by dsimp [a];linarith
  have hpb : p.1<b := by dsimp [b];linarith
  obtain ⟨C,hC,hbound⟩ := coeff.termFDeriv_slab_bound a b ha hab
  have hsum := (summable_one_add_norm_exp_neg_cuspFrequency (Real.pi*a)
    (mul_pos Real.pi_pos ha)).mul_left C
  let slab : Set (ℝ × ℂ) := Set.Ioo a b ×ˢ Set.univ
  have hslab : IsOpen slab := isOpen_Ioo.prod isOpen_univ
  have hconn : IsPreconnected slab := isPreconnected_Ioo.prod isPreconnected_univ
  have hpSlab : p∈slab := ⟨⟨hap,hpb⟩,Set.mem_univ _⟩
  exact hasFDerivAt_tsum_of_isPreconnected hsum hslab hconn
    (fun h q hq => coeff.term_hasFDerivAt h q (ha.trans hq.1.1))
    (fun h q hq => hbound h q ⟨hq.1.1.le,hq.1.2.le⟩)
    hpSlab (coeff.summable p hp) hpSlab

lemma series_differentiableAt (p : ℝ × ℂ) (hp : 0<p.1) :
    DifferentiableAt ℝ coeff.series p := (coeff.series_hasFDerivAt p hp).differentiableAt

lemma fullFunction_cusp_eq (constant : ℂ) (p : ℝ × ℂ) (hp : 0<p.1) :
    coeff.fullFunction constant (cuspCoordinateLift p)=
      constant*(p.1:ℂ)^(2/3:ℂ)+coeff.series p := by
  rw [show p=(p.1,p.2) from rfl,cuspCoordinateLift_positive p.1 p.2 hp]
  simp only [fullFunction,function,hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint]

lemma fullFunction_cusp_differentiableAt (constant : ℂ) (p : ℝ × ℂ) (hp : 0<p.1) :
    DifferentiableAt ℝ (fun q : ℝ × ℂ => coeff.fullFunction constant (cuspCoordinateLift q)) p := by
  have hc := ((hasDerivAt_ofReal_cpow_const hp.ne' (r:=(2/3:ℂ))
    (by norm_num)).const_mul constant).differentiableAt.comp p
      (differentiableAt_fst (𝕜:=ℝ) (p:=p))
  have ht : DifferentiableAt ℝ (fun q : ℝ × ℂ =>
      constant*(q.1:ℂ)^(2/3:ℂ)+coeff.series q) p := by
    convert! hc.add (coeff.series_differentiableAt p hp) using 1
  apply ht.congr_of_eventuallyEq
  filter_upwards [continuousAt_fst.tendsto.eventually (Ioi_mem_nhds hp)] with q hq
  exact coeff.fullFunction_cusp_eq constant q hq

lemma fullFunction_split_differentiableAt (constant : ℂ) (p : ℂ × ℝ) (hp : 0<p.2) :
    DifferentiableAt ℝ
      (fun q : ℂ × ℝ => coeff.fullFunction constant (cuspCoordinateLift (q.2,q.1))) p := by
  have hswap : DifferentiableAt ℝ (fun q : ℂ × ℝ => (q.2,q.1)) p :=
    differentiableAt_snd.prodMk differentiableAt_fst
  exact (coeff.fullFunction_cusp_differentiableAt constant (p.2,p.1) hp).comp p hswap

end SubexponentialBesselCoefficients
end

open Filter MeasureTheory Asymptotics
open scoped BigOperators Classical Topology

def truncatedCuspProfile (c : ℝ) (f : ℝ→ℂ) (x : ℝ) : ℂ :=
  if c<x then f x else 0

lemma truncatedCuspProfile_eventually_top (c : ℝ) (f : ℝ→ℂ) :
    truncatedCuspProfile c f =ᶠ[atTop] f := by
  filter_upwards [eventually_gt_atTop c] with x hx
  simp only [truncatedCuspProfile,ite_eq_left hx]

lemma truncatedCuspProfile_eventually_zero (c : ℝ) (hc : 0<c) (f : ℝ→ℂ) :
    truncatedCuspProfile c f =ᶠ[𝓝[>] 0] 0 := by
  have he : ∀ᶠx : ℝ in 𝓝[>] 0,x<c := (eventually_lt_nhds hc).filter_mono nhdsWithin_le_nhds
  filter_upwards [he] with x hx
  simp only [truncatedCuspProfile,ite_eq_right (not_lt_of_ge hx.le),Pi.zero_apply]

lemma truncatedCuspProfile_locallyIntegrable (c : ℝ) (hc : 0<c) (f : ℝ→ℂ)
    (hf : ContinuousOn f (Set.Ioi 0)) :
    LocallyIntegrable (truncatedCuspProfile c f) volume := by
  have hcont : Continuous (fun x : ℝ=>f (max (c/2) x)) :=
    hf.comp_continuous (continuous_const.max continuous_id)
      (fun x=>lt_of_lt_of_le (by linarith : 0<c/2) (le_max_left _ _))
  have he : truncatedCuspProfile c f=
      (Set.Ioi c).indicator (fun x : ℝ=>f (max (c/2) x)) := by
    funext x
    by_cases hx : c<x
    · have hm : max (c/2) x=x := max_eq_right (by linarith)
      simp [truncatedCuspProfile,Set.indicator,hx,hm]
    · simp [truncatedCuspProfile,Set.indicator,hx]
  rw [he]
  exact hcont.locallyIntegrable.indicator measurableSet_Ioi

theorem truncatedCuspProfile_mellin_entire (c decay : ℝ) (hc : 0<c) (hdecay : 0<decay)
    (f : ℝ→ℂ) (hf : ContinuousOn f (Set.Ioi 0))
    (hbound : f =O[atTop] (fun x : ℝ=>Real.exp (-decay*x))) :
    (∀s : ℂ,MellinConvergent (truncatedCuspProfile c f) s) ∧
      Differentiable ℂ (mellin (truncatedCuspProfile c f)) := by
  have hlocal := (truncatedCuspProfile_locallyIntegrable c hc f hf).locallyIntegrableOn (Set.Ioi 0)
  have htop : truncatedCuspProfile c f =O[atTop] (fun x : ℝ=>Real.exp (-decay*x)) :=
    hbound.congr' (truncatedCuspProfile_eventually_top c f).symm Filter.EventuallyEq.rfl
  have hzero (b : ℝ) : truncatedCuspProfile c f =O[𝓝[>] 0] (fun x : ℝ=>x^(-b)) :=
    (Asymptotics.isBigO_zero (fun x : ℝ=>x^(-b)) (𝓝[>] 0)).congr'
      (truncatedCuspProfile_eventually_zero c hc f).symm Filter.EventuallyEq.rfl
  constructor
  · intro s
    exact mellinConvergent_of_isBigO_rpow_exp hdecay hlocal htop (hzero (s.re-1)) (by linarith)
  · intro s
    exact mellin_differentiableAt_of_isBigO_rpow_exp hdecay hlocal htop (hzero (s.re-1)) (by linarith)

end CubicEisenstein

end

end OAI
