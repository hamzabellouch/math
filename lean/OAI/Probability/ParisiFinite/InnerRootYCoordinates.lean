import Mathlib
import OAI.Probability.ParisiFinite.OrdinaryInverseSpecial
import OAI.Probability.ParisiFinite.RestrictLeft

namespace OAI

/-! Inner Root Y Coordinates. -/

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace Topology ComplexOrder
open Filter
open scoped BigOperators
open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate
open scoped InnerProductSpace ComplexConjugate
open Filter Topology
open Filter Set Topology
open scoped InnerProductSpace ComplexConjugate Topology
open scoped InnerProductSpace
namespace CoherentFock
open PointedTree RootSpin Complex
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

 

theorem inner_rootY_coordinates (x y : SpinSpace E) :
    ⟪SpinOperators.act Y x,y⟫_ℂ=I*⟪x 1,y 0⟫_ℂ-I*⟪x 0,y 1⟫_ℂ := by
  simp [PiLp.inner_apply,SpinOperators.act_apply,Fin.sum_univ_two,Y,
    inner_smul_left,sub_eq_add_neg]

theorem inner_rootY_spinW_same_plus (d e : E) (x y : PreSpin E) (hx : x 1=0) (hy : y 1=0) :
    ⟪SpinOperators.act Y (spinW d (spinCoe x)),spinW e (spinCoe y)⟫_ℂ=0 := by
  rw [inner_rootY_coordinates]
  simp [hx,hy]

theorem inner_rootY_spinW_same_minus (d e : E) (x y : PreSpin E) (hx : x 0=0) (hy : y 0=0) :
    ⟪SpinOperators.act Y (spinW d (spinCoe x)),spinW e (spinCoe y)⟫_ℂ=0 := by
  rw [inner_rootY_coordinates]
  simp [hx,hy]

 

def hugePacket (R : ℝ) (d e : E) (xp xm : PreSpin E) : SpinSpace E :=
  spinW (R • d) (spinCoe xp)+spinW (R • e) (spinCoe xm)

theorem norm_hugePacket_le (R : ℝ) (d e : E) (xp xm : PreSpin E) :
    ‖hugePacket R d e xp xm‖≤ spinMass xp+spinMass xm := by
  apply (norm_add_le _ _).trans
  exact add_le_add ((norm_spinW _ _).trans_le (norm_spinCoe_le_mass _))
    ((norm_spinW _ _).trans_le (norm_spinCoe_le_mass _))

theorem inner_rootY_hugePacket (R : ℝ) (d e : E) (xp xm yp ym : PreSpin E)
    (hxp : xp 1=0) (hxm : xm 0=0) (hyp : yp 1=0) (hym : ym 0=0) :
    ⟪SpinOperators.act Y (hugePacket R d e xp xm),hugePacket R d e yp ym⟫_ℂ=
      ⟪SpinOperators.act Y (spinW (R • d) (spinCoe xp)),spinW (R • e) (spinCoe ym)⟫_ℂ+
      ⟪SpinOperators.act Y (spinW (R • e) (spinCoe xm)),spinW (R • d) (spinCoe yp)⟫_ℂ := by
  simp only [hugePacket,map_add,inner_add_left,inner_add_right,
    inner_rootY_spinW_same_plus _ _ _ _ hxp hyp,inner_rootY_spinW_same_minus _ _ _ _ hxm hym,
    zero_add,add_zero]
  exact add_comm _ _

 

theorem tendsto_inner_rootY_hugePacket {α : Type*} {l : Filter α}
    (R : α → ℝ) (d e : α → E) (xp xm yp ym : α → PreSpin E)
    (hR : Tendsto R l atTop) (B A δ : ℝ) (hA : 0≤ A) (hδ : 0<δ)
    (hxp : ∀ᶠ a in l, SpinRadiusLE (xp a) B ∧ spinMass (xp a)≤ A)
    (hxm : ∀ᶠ a in l, SpinRadiusLE (xm a) B ∧ spinMass (xm a)≤ A)
    (hyp : ∀ᶠ a in l, SpinRadiusLE (yp a) B ∧ spinMass (yp a)≤ A)
    (hym : ∀ᶠ a in l, SpinRadiusLE (ym a) B ∧ spinMass (ym a)≤ A)
    (hs : ∀ᶠ a in l, xp a 1=0 ∧ xm a 0=0 ∧ yp a 1=0 ∧ ym a 0=0)
    (hsep : ∀ᶠ a in l, δ≤ ‖d a-e a‖) :
    Tendsto (fun a => ⟪SpinOperators.act Y (hugePacket (R a) (d a) (e a) (xp a) (xm a)),
      hugePacket (R a) (d a) (e a) (yp a) (ym a)⟫_ℂ) l (𝓝 0) := by
  have hP : ∀ᶠ a : α in l, matrixMass Y≤ matrixMass Y := Filter.Eventually.of_forall (fun _ => le_rfl)
  have h1 := rapid_decay_spin_matrix R d e xp ym (fun _ => Y) hR B A (matrixMass Y) δ hA
    (matrixMass_nonneg _) hδ hxp hym hP hsep 0
  have hsep' : ∀ᶠ a in l, δ≤ ‖e a-d a‖ := hsep.mono (fun a ha => by rwa [norm_sub_rev])
  have h2 := rapid_decay_spin_matrix R e d xm yp (fun _ => Y) hR B A (matrixMass Y) δ hA
    (matrixMass_nonneg _) hδ hxm hyp hP hsep' 0
  simp only [pow_zero,one_mul] at h1 h2
  have h1' := tendsto_zero_iff_norm_tendsto_zero.mpr h1
  have h2' := tendsto_zero_iff_norm_tendsto_zero.mpr h2
  have hh := h1'.add h2'
  simp only [add_zero] at hh
  apply hh.congr'
  filter_upwards [hs] with a ha
  exact (inner_rootY_hugePacket (R a) (d a) (e a) (xp a) (xm a) (yp a) (ym a)
    ha.1 ha.2.1 ha.2.2.1 ha.2.2.2).symm

 

theorem inner_rootY_error_bound (x y u v : SpinSpace E) :
    ‖⟪SpinOperators.act Y x,y⟫_ℂ-⟪SpinOperators.act Y u,v⟫_ℂ‖≤ 
      ‖x-u‖*‖y‖+‖u‖*‖y-v‖ := by
  have hY (w : SpinSpace E) : ‖SpinOperators.act Y w‖=‖w‖ :=
    (SpinOperators.actEquiv Y Y_unitary).norm_map w
  have he : ⟪SpinOperators.act Y x,y⟫_ℂ-⟪SpinOperators.act Y u,v⟫_ℂ=
      ⟪SpinOperators.act Y (x-u),y⟫_ℂ+⟪SpinOperators.act Y u,y-v⟫_ℂ := by
    simp only [map_sub,inner_sub_left,inner_sub_right]
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  simpa only [hY] using add_le_add (norm_inner_le_norm (𝕜 := ℂ) (SpinOperators.act Y (x-u)) y)
    (norm_inner_le_norm (𝕜 := ℂ) (SpinOperators.act Y u) (y-v))

 

theorem huge_transverse_actual {α : Type*} {l : Filter α}
    (U : α → SpinSpace E ≃ₗᵢ[ℂ] SpinSpace E) (Ω : SpinSpace E) (η : α → SpinSpace E)
    (R : α → ℝ) (d e : α → E) (xp xm yp ym : α → PreSpin E)
    (hR : Tendsto R l atTop) (B A δ C : ℝ) (hA : 0≤ A) (hδ : 0<δ)
    (hxp : ∀ᶠ a in l, SpinRadiusLE (xp a) B ∧ spinMass (xp a)≤ A)
    (hxm : ∀ᶠ a in l, SpinRadiusLE (xm a) B ∧ spinMass (xm a)≤ A)
    (hyp : ∀ᶠ a in l, SpinRadiusLE (yp a) B ∧ spinMass (yp a)≤ A)
    (hym : ∀ᶠ a in l, SpinRadiusLE (ym a) B ∧ spinMass (ym a)≤ A)
    (hs : ∀ᶠ a in l, xp a 1=0 ∧ xm a 0=0 ∧ yp a 1=0 ∧ ym a 0=0)
    (hsep : ∀ᶠ a in l, δ≤ ‖d a-e a‖) (hη : ∀ᶠ a in l, ‖η a‖≤ C)
    (herrΩ : Tendsto (fun a => ‖U a Ω-hugePacket (R a) (d a) (e a) (xp a) (xm a)‖) l (𝓝 0))
    (herrη : Tendsto (fun a => ‖U a (η a)-hugePacket (R a) (d a) (e a) (yp a) (ym a)‖) l (𝓝 0)) :
    Tendsto (fun a => ⟪(U a).symm (SpinOperators.act Y (U a Ω)),η a⟫_ℂ) l (𝓝 0) := by
  let P a := hugePacket (R a) (d a) (e a) (xp a) (xm a)
  let Q a := hugePacket (R a) (d a) (e a) (yp a) (ym a)
  have hp := tendsto_inner_rootY_hugePacket R d e xp xm yp ym hR B A δ hA hδ hxp hxm hyp hym hs hsep
  have he : Tendsto (fun a =>
      ⟪SpinOperators.act Y (U a Ω),U a (η a)⟫_ℂ-⟪SpinOperators.act Y (P a),Q a⟫_ℂ) l (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hb := (herrΩ.mul_const C).add (herrη.const_mul (2*A))
    simp only [zero_mul,mul_zero,add_zero] at hb
    apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) _ hb
    filter_upwards [hxp,hxm,hη] with a hpa hma hηa
    apply (inner_rootY_error_bound (U a Ω) (U a (η a)) (P a) (Q a)).trans
    have hpn : ‖P a‖≤ 2*A := (norm_hugePacket_le _ _ _ _ _).trans (by linarith [hpa.2,hma.2])
    rw [(U a).norm_map]
    exact add_le_add (mul_le_mul_of_nonneg_left hηa (norm_nonneg _))
      (mul_le_mul_of_nonneg_right hpn (norm_nonneg _))
  have hh := he.add hp
  simp only [P,Q,sub_add_cancel,add_zero] at hh
  convert hh using 1
  ext a
  have hv := (U a).inner_map_map ((U a).symm (SpinOperators.act Y (U a Ω))) (η a)
  simpa only [LinearIsometryEquiv.apply_symm_apply] using hv.symm

end CoherentFock

namespace GaussianCoherent
open MeasureTheory ProbabilityTheory Complex CoherentFock
open scoped BigOperators InnerProductSpace ComplexConjugate
variable {κ : Type*} [Fintype κ]

abbrev Mode (κ : Type*) [Fintype κ] := EuclideanSpace ℂ κ
abbrev Hilbert (κ : Type*) [Fintype κ] := Lp ℂ 2 (GaussianFourier.law κ)

 

def offset (d : Mode κ) : ℂ := (∑k, (d k)^2)/2-((‖d‖^2:ℝ):ℂ)/2

def wave (d : Mode κ) (g : κ → ℝ) : ℂ :=
  Complex.exp (offset d)*Complex.exp (∑k, I*d k*(g k:ℂ))

theorem continuous_wave (d : Mode κ) : Continuous (wave d) := by
  unfold wave
  fun_prop

theorem wave_pair (d e : Mode κ) (g : κ → ℝ) :
    conj (wave d g)*wave e g=
      Complex.exp (conj (offset d)+offset e)*
        Complex.exp (∑k, (I*(e k-conj (d k)))*(g k:ℂ)) := by
  simp only [wave,map_mul,←Complex.exp_conj,map_sum,Complex.conj_I,Complex.conj_ofReal]
  rw [←Complex.exp_add,←Complex.exp_add,←Complex.exp_add,←Complex.exp_add]
  congr 1
  have hh : (∑k, -I*conj (d k)*(g k:ℂ))+(∑k, I*e k*(g k:ℂ))=
      ∑k, I*(e k-conj (d k))*(g k:ℂ) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  linear_combination hh

theorem integrable_wave_pair (d e : Mode κ) :
    Integrable (fun g => conj (wave d g)*wave e g) (GaussianFourier.law κ) := by
  simp_rw [wave_pair]
  exact (GaussianFourier.integrable_exp_sum (fun k => I*(e k-conj (d k)))).const_mul _

theorem exponent_pair (d e : Mode κ) :
    conj (offset d)+offset e+(∑k, (I*(e k-conj (d k)))^2/2)=
      -((‖d‖^2+‖e‖^2:ℝ):ℂ)/2+⟪d,e⟫_ℂ := by
  simp only [offset,map_sub,map_div₀,map_sum,map_pow,Complex.conj_ofReal,
    map_ofNat,PiLp.inner_apply,RCLike.inner_apply']
  push_cast
  simp_rw [←Finset.sum_div]
  have hs : (∑k, (conj (d k))^2)+(∑k, (e k)^2)+
      (∑k, (I*(e k-conj (d k)))^2)=2*∑k, conj (d k)*e k := by
    rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring_nf
    rw [Complex.I_sq]
    ring
  linear_combination hs/2

 

theorem integral_wave_pair (d e : Mode κ) :
    (∫g, conj (wave d g)*wave e g ∂GaussianFourier.law κ)=kernel d e := by
  simp_rw [wave_pair]
  rw [integral_const_mul,GaussianFourier.integral_exp_sum,←Complex.exp_add,exponent_pair]
  unfold kernel
  congr 1
  push_cast
  ring

theorem memLp_wave (d : Mode κ) : MemLp (wave d) 2 (GaussianFourier.law κ) := by
  apply (memLp_two_iff_integrable_sq_norm (continuous_wave d).aestronglyMeasurable).mpr
  have h := (integrable_wave_pair d d).re
  convert h using 1
  funext g
  rw [Complex.conj_mul']
  change ‖wave d g‖^2 = ((‖wave d g‖:ℂ)^2).re
  rw [←Complex.ofReal_pow,Complex.ofReal_re]

def vector (d : Mode κ) : Hilbert κ := (memLp_wave d).toLp (wave d)

theorem vector_ae (d : Mode κ) : (vector d : (κ → ℝ) → ℂ)=ᵐ[GaussianFourier.law κ] wave d :=
  (memLp_wave d).coeFn_toLp

@[simp] theorem inner_vector (d e : Mode κ) : ⟪vector d,vector e⟫_ℂ=kernel d e := by
  rw [L2.inner_def]
  rw [←integral_wave_pair d e]
  apply integral_congr_ae
  filter_upwards [vector_ae d,vector_ae e] with g hd he
  rw [hd,he]
  exact RCLike.inner_apply' _ _

 

def preMap : PreSpace (Mode κ) →ₗᵢ[ℂ] Hilbert κ :=
  LinearMap.isometryOfInner
    ((Finsupp.linearCombination ℂ vector).comp toFinsupp.toLinearMap) (by
      intro x y
      change ⟪(toFinsupp x).sum (fun d a => a • vector d),
        (toFinsupp y).sum (fun e b => b • vector e)⟫_ℂ=_
      rw [Finsupp.sum_inner]
      change (toFinsupp x).sum (fun d a => ⟪a • vector d,
        (toFinsupp y).sum (fun e b => b • vector e)⟫_ℂ)=
          (toFinsupp x).sum (fun d a => (toFinsupp y).sum (fun e b => conj a*kernel d e*b))
      apply Finsupp.sum_congr
      intro d hd
      rw [Finsupp.inner_sum]
      apply Finsupp.sum_congr
      intro e he
      simp only [inner_smul_left,inner_smul_right,inner_vector]
      ring)

 
def representation : Space (Mode κ) →ₗᵢ[ℂ] Hilbert κ where
  toLinearMap := preMap.toContinuousLinearMap.fromCompletion.toLinearMap
  norm_map' x := by
    refine UniformSpace.Completion.induction_on x
      (isClosed_eq (preMap.toContinuousLinearMap.fromCompletion.continuous.norm) continuous_norm)
      fun y => ?_
    change ‖preMap.toContinuousLinearMap.fromCompletion (y:Space (Mode κ))‖=‖(y:Space (Mode κ))‖
    rw [ContinuousLinearMap.fromCompletion_apply_coe,UniformSpace.Completion.norm_coe]
    exact preMap.norm_map y

@[simp] theorem representation_coherent (d : Mode κ) : representation (coherent d)=vector d := by
  change preMap.toContinuousLinearMap.fromCompletion
    ((toFinsupp.symm (Finsupp.single d 1):PreSpace (Mode κ)):Space (Mode κ))=vector d
  rw [ContinuousLinearMap.fromCompletion_apply_coe]
  change Finsupp.linearCombination ℂ vector (Finsupp.single d 1)=vector d
  simp

end GaussianCoherent

namespace GaussianCoherent
open MeasureTheory ProbabilityTheory Complex CoherentFock
open scoped BigOperators InnerProductSpace ComplexConjugate
variable {κ : Type*} [Fintype κ]

def realMode (a : κ → ℝ) : Mode κ := WithLp.toLp 2 (fun k => (a k:ℂ))

@[simp] theorem realMode_apply (a : κ → ℝ) (k : κ) : realMode a k=(a k:ℂ) := rfl

@[simp] theorem norm_realMode_sq (a : κ → ℝ) : ‖realMode a‖^2=∑k, (a k)^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Real.norm_eq_abs,sq_abs]

@[simp] theorem offset_realMode (a : κ → ℝ) : offset (realMode a)=0 := by
  simp [offset,norm_realMode_sq,Complex.ofReal_sum]

@[simp] theorem wave_realMode (a : κ → ℝ) (g : κ → ℝ) :
    wave (realMode a) g=Complex.exp ((∑k, a k*g k:ℝ)*I) := by
  simp only [wave,offset_realMode,Complex.exp_zero,one_mul,realMode_apply]
  congr 1
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  ring

@[simp] theorem norm_wave_realMode (a : κ → ℝ) (g : κ → ℝ) : ‖wave (realMode a) g‖=1 := by
  rw [wave_realMode,Complex.norm_exp]
  simp

theorem memLp_seedPhase (a : κ → ℝ) (f : Hilbert κ) :
    MemLp (fun g => wave (realMode a) g*f g) 2 (GaussianFourier.law κ) := by
  apply (Lp.memLp f).congr_norm
    ((continuous_wave (realMode a)).aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
  exact Filter.Eventually.of_forall fun g => by
    change ‖f g‖=‖wave (realMode a) g*f g‖
    rw [norm_mul,norm_wave_realMode,one_mul]

 
def seedPhase (a : κ → ℝ) (f : Hilbert κ) : Hilbert κ :=
  (memLp_seedPhase a f).toLp (fun g => wave (realMode a) g*f g)

theorem seedPhase_ae (a : κ → ℝ) (f : Hilbert κ) :
    (seedPhase a f : (κ → ℝ) → ℂ)=ᵐ[GaussianFourier.law κ] fun g => wave (realMode a) g*f g :=
  MemLp.coeFn_toLp _

 

def seedPhaseIsometry (a : κ → ℝ) : Hilbert κ →ₗᵢ[ℂ] Hilbert κ where
  toFun := seedPhase a
  map_add' f h := by
    apply Lp.ext
    filter_upwards [seedPhase_ae a (f+h),Lp.coeFn_add f h,
      Lp.coeFn_add (seedPhase a f) (seedPhase a h),seedPhase_ae a f,seedPhase_ae a h] with g h1 h2 h3 h4 h5
    rw [h1,h2,h3]
    simp only [Pi.add_apply,h4,h5]
    exact mul_add _ _ _
  map_smul' c f := by
    change seedPhase a (c • f)=c • seedPhase a f
    apply Lp.ext
    filter_upwards [seedPhase_ae a (c • f),Lp.coeFn_smul c f,
      Lp.coeFn_smul c (seedPhase a f),seedPhase_ae a f] with g h1 h2 h3 h4
    rw [h1,h2,h3]
    simp only [Pi.smul_apply,h4]
    simp only [smul_eq_mul]
    ring
  norm_map' f := by
    have hh : ∀ᵐ g ∂GaussianFourier.law κ, ‖seedPhase a f g‖=‖f g‖ := by
      filter_upwards [seedPhase_ae a f] with g hg
      rw [hg,norm_mul,norm_wave_realMode,one_mul]
    exact le_antisymm (Lp.norm_le_norm_of_ae_le (hh.mono fun _ h => h.le))
      (Lp.norm_le_norm_of_ae_le (hh.mono fun _ h => h.ge))

theorem offset_real_add (a : κ → ℝ) (d : Mode κ) :
    offset (realMode a+d)=offset d+((⟪realMode a,d⟫_ℂ).im:ℂ)*I := by
  have hs : (∑k, (realMode a k+d k)^2)=
      (∑k, (realMode a k)^2)+2*⟪realMode a,d⟫_ℂ+(∑k, (d k)^2) := by
    simp only [PiLp.inner_apply,RCLike.inner_apply',realMode_apply,Complex.conj_ofReal]
    rw [Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have ho := offset_realMode a
  unfold offset at ho ⊢
  simp only [PiLp.add_apply]
  rw [_root_.norm_add_sq (𝕜 := ℂ)]
  rw [hs]
  have hc := Complex.re_add_im ⟪realMode a,d⟫_ℂ
  push_cast at ho ⊢
  linear_combination ho - hc

 

theorem phase_wave_real_add (a : κ → ℝ) (d : Mode κ) (g : κ → ℝ) :
    phase (realMode a) d*wave (realMode a+d) g=wave (realMode a) g*wave d g := by
  simp only [phase,wave,offset_realMode,Complex.exp_zero,one_mul,offset_real_add]
  simp only [←Complex.exp_add]
  congr 1
  simp only [PiLp.add_apply,mul_add,add_mul,Finset.sum_add_distrib]
  push_cast
  ring

theorem seedPhase_vector (a : κ → ℝ) (d : Mode κ) :
    seedPhaseIsometry a (vector d)=phase (realMode a) d • vector (realMode a+d) := by
  apply Lp.ext
  filter_upwards [seedPhase_ae a (vector d),vector_ae d,vector_ae (realMode a+d),
    Lp.coeFn_smul (phase (realMode a) d) (vector (realMode a+d))] with g h1 h2 h3 h4
  change seedPhase a (vector d) g = _
  rw [h1,h2,h4]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [h3]
  exact (phase_wave_real_add a d g).symm

 
theorem representation_W_real (a : κ → ℝ) (x : Space (Mode κ)) :
    representation (W (realMode a) x)=seedPhaseIsometry a (representation x) := by
  have he : representation.toContinuousLinearMap.comp (W (realMode a))=
      (seedPhaseIsometry a).toContinuousLinearMap.comp representation.toContinuousLinearMap := by
    apply CoherentFock.ext_coherent
    intro d
    simp only [ContinuousLinearMap.comp_apply,LinearIsometry.coe_toContinuousLinearMap,
      W_coherent,map_smul,representation_coherent,seedPhase_vector]
  exact DFunLike.congr_fun he x

end GaussianCoherent
namespace FourierDensity
open MeasureTheory ProbabilityTheory Complex
open scoped BigOperators ComplexConjugate InnerProductSpace
variable {κ : Type*} [Fintype κ]

def character (a g : κ → ℝ) : ℂ := Complex.exp ((∑k, a k*g k:ℝ)*I)

theorem continuous_character (a : κ → ℝ) : Continuous (character a) := by
  unfold character
  fun_prop

@[simp] theorem norm_character (a g : κ → ℝ) : ‖character a g‖=1 := by
  simp [character,Complex.norm_exp]

@[simp] theorem character_neg (a g : κ → ℝ) : character (-a) g=conj (character a g) := by
  simp [character,←Complex.exp_conj,Finset.sum_neg_distrib]

variable {μ : Measure (κ → ℝ)}

theorem integrable_character_mul {f : (κ → ℝ) → ℂ}
    (hf : Integrable f μ) (a : κ → ℝ) : Integrable (fun g => character a g*f g) μ :=
  hf.bdd_mul (continuous_character a).aestronglyMeasurable
    (Filter.Eventually.of_forall fun g => (norm_character a g).le)

theorem dual_eq_sum [DecidableEq κ] (L : StrongDual ℝ (κ → ℝ)) (g : κ → ℝ) :
    L g=∑k, L (Pi.single k 1)*g k := by
  classical
  have hg : g=∑k, g k • Pi.single k 1 := by
    ext j
    simp [Finset.sum_apply,Pi.smul_apply,Pi.single_apply]
  conv_lhs => rw [hg]
  simp only [map_sum,map_smul,smul_eq_mul,mul_comm]

 

theorem ae_zero_of_real_fourier_zero [IsFiniteMeasure μ]
    {f : (κ → ℝ) → ℝ} (hf : Integrable f μ)
    (hF : ∀a, (∫g, character a g*(f g:ℂ) ∂μ)=0) : f=ᵐ[μ] 0 := by
  classical
  let fpos := fun g => max (f g) 0
  let fneg := fun g => max (-f g) 0
  have hp : Integrable fpos μ := hf.pos_part
  have hn : Integrable fneg μ := hf.neg_part
  let μp := μ.withDensity (fun g => ENNReal.ofReal (fpos g))
  let μn := μ.withDensity (fun g => ENNReal.ofReal (fneg g))
  have : IsFiniteMeasure μp := isFiniteMeasure_withDensity_ofReal hp.2
  have : IsFiniteMeasure μn := isFiniteMeasure_withDensity_ofReal hn.2
  have heq : μp=μn := by
    apply Measure.ext_of_charFunDual
    funext L
    simp only [charFunDual_apply]
    have hl : (fun g => Complex.exp ((L g : ℝ)*I))=
        character (fun k => L (Pi.single k 1)) := by
      funext g
      rw [dual_eq_sum L g]
      rfl
    rw [hl]
    change (∫g, character (fun k => L (Pi.single k 1)) g ∂μp)=
      (∫g, character (fun k => L (Pi.single k 1)) g ∂μn)
    dsimp only [μp,μn]
    rw [integral_withDensity_eq_integral_toReal_smul₀ hp.1.aemeasurable.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
      integral_withDensity_eq_integral_toReal_smul₀ hn.1.aemeasurable.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (le_max_right _ _),fpos,fneg,real_smul]
    apply sub_eq_zero.mp
    change (∫g, (fpos g:ℂ)*character (fun k => L (Pi.single k 1)) g ∂μ)-
      (∫g, (fneg g:ℂ)*character (fun k => L (Pi.single k 1)) g ∂μ)=0
    have hpC : Integrable (fun g => (fpos g:ℂ)*character
        (fun k => L (Pi.single k 1)) g) μ :=
      (integrable_character_mul hp.ofReal (fun k => L (Pi.single k 1))).congr
        (Filter.Eventually.of_forall fun g => mul_comm _ _)
    have hnC : Integrable (fun g => (fneg g:ℂ)*character
        (fun k => L (Pi.single k 1)) g) μ :=
      (integrable_character_mul hn.ofReal (fun k => L (Pi.single k 1))).congr
        (Filter.Eventually.of_forall fun g => mul_comm _ _)
    rw [←integral_sub hpC hnC]
    convert hF (fun k => L (Pi.single k 1)) using 1
    congr 1
    funext g
    have hm : max (f g) 0-max (-f g) 0=f g := max_zero_sub_max_neg_zero_eq_self _
    dsimp only [fpos,fneg]
    rw [←sub_mul,←Complex.ofReal_sub,hm,mul_comm]
  have hd := (withDensity_eq_iff_of_sigmaFinite hp.1.aemeasurable.ennreal_ofReal
    hn.1.aemeasurable.ennreal_ofReal).mp heq
  filter_upwards [hd] with g hg
  have hh := congrArg ENNReal.toReal hg
  simp only [ENNReal.toReal_ofReal (le_max_right _ _),fpos,fneg] at hh
  change f g=0
  have hm : max (f g) 0-max (-f g) 0=f g := max_zero_sub_max_neg_zero_eq_self _
  linarith

 
theorem ae_re_zero_of_fourier_zero [IsFiniteMeasure μ]
    {f : (κ → ℝ) → ℂ} (hf : Integrable f μ)
    (hF : ∀a, (∫g, character a g*f g ∂μ)=0) :
    (fun g => (f g).re)=ᵐ[μ] 0 := by
  have hc : ∀a, (∫g, character a g*conj (f g) ∂μ)=0 := by
    intro a
    have hh := congrArg conj (hF (-a))
    rw [map_zero,←integral_conj] at hh
    simpa only [map_mul,character_neg,Complex.conj_conj] using hh
  have hfc : Integrable (fun g => conj (f g)) μ :=
    (@RCLike.conjLIE ℂ _).toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp hf
  apply ae_zero_of_real_fourier_zero hf.re
  intro a
  calc
    (∫g, character a g*((f g).re:ℂ) ∂μ)=
        (1/2:ℂ)*(∫g, character a g*f g+character a g*conj (f g) ∂μ) := by
      rw [←integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun g => by
        have hadd := Complex.add_conj (f g)
        push_cast at hadd
        linear_combination -(character a g)*hadd/2
    _=0 := by
      rw [integral_add (integrable_character_mul hf a) (integrable_character_mul hfc a),
        hF a,hc a]
      simp

 

theorem ae_zero_of_fourier_zero [IsFiniteMeasure μ]
    {f : (κ → ℝ) → ℂ} (hf : Integrable f μ)
    (hF : ∀a, (∫g, character a g*f g ∂μ)=0) : f=ᵐ[μ] 0 := by
  have hr := ae_re_zero_of_fourier_zero hf hF
  have hi := ae_re_zero_of_fourier_zero (hf.const_mul I) (fun a => by
    calc
      (∫g, character a g*(I*f g) ∂μ)=I*(∫g, character a g*f g ∂μ) := by
        rw [←integral_const_mul]
        congr 1
        funext g
        ring
      _=0 := by rw [hF a,mul_zero])
  filter_upwards [hr,hi] with g hrg hig
  apply Complex.ext
  · exact hrg
  · simpa using hig

end FourierDensity

namespace GaussianCoherent
open MeasureTheory ProbabilityTheory Complex CoherentFock
open scoped BigOperators InnerProductSpace ComplexConjugate
variable {κ : Type*} [Fintype κ]

 

theorem representation_surjective : Function.Surjective (representation (κ := κ)) := by
  let K := (representation (κ := κ)).toLinearMap.range
  have hK : IsClosed (K : Set (Hilbert κ)) :=
    (representation (κ := κ)).isometry.isClosedEmbedding.isClosed_range
  have hbot : Kᗮ=⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro f hf
    apply Lp.ext
    have hi : Integrable (fun g => f g) (GaussianFourier.law κ) :=
      memLp_one_iff_integrable.mp ((Lp.memLp f).mono_exponent (by norm_num))
    have hF : ∀a, (∫g, FourierDensity.character a g*f g ∂GaussianFourier.law κ)=0 := by
      intro a
      have hh := (Submodule.mem_orthogonal K f).mp hf (vector (realMode (-a)))
        ⟨coherent (realMode (-a)),representation_coherent _⟩
      rw [L2.inner_def] at hh
      convert hh using 1
      apply integral_congr_ae
      filter_upwards [vector_ae (realMode (-a))] with g hg
      rw [RCLike.inner_apply',hg,wave_realMode]
      change FourierDensity.character a g*f g=
        conj (FourierDensity.character (-a) g)*f g
      rw [FourierDensity.character_neg,Complex.conj_conj]
    have hz := FourierDensity.ae_zero_of_fourier_zero hi hF
    exact hz.trans (Lp.coeFn_zero ℂ 2 (GaussianFourier.law κ)).symm
  apply LinearMap.range_eq_top.mp
  change K=⊤
  calc
    K=K.topologicalClosure := hK.submodule_topologicalClosure_eq.symm
    _=Kᗮᗮ := (Submodule.orthogonal_orthogonal_eq_closure K).symm
    _=⊤ := by rw [hbot,Submodule.bot_orthogonal_eq_top]

 
def gaussianUnitary : Space (Mode κ) ≃ₗᵢ[ℂ] Hilbert κ :=
  LinearIsometryEquiv.ofSurjective representation representation_surjective

@[simp] theorem gaussianUnitary_coherent (d : Mode κ) :
    gaussianUnitary (coherent d)=vector d := representation_coherent d

theorem gaussianUnitary_W_real (a : κ → ℝ) (x : Space (Mode κ)) :
    gaussianUnitary (W (realMode a) x)=seedPhaseIsometry a (gaussianUnitary x) :=
  representation_W_real a x

end GaussianCoherent

namespace CoherentFock
open scoped InnerProductSpace ComplexConjugate
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem eq_zero_of_inner_coherent (x : Space E) (hx : ∀d, ⟪coherent d,x⟫_ℂ=0) : x=0 := by
  have hh : innerSL ℂ x=0 := by
    apply ext_coherent
    intro d
    exact inner_eq_zero_symm.mp (hx d)
  have hhx := DFunLike.congr_fun hh x
  exact inner_self_eq_zero.mp hhx
end CoherentFock

end

end OAI
