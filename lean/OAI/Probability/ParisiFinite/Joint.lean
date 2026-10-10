import Mathlib
import OAI.Probability.ParisiFinite.InnerRootYCoordinates
import OAI.Probability.ParisiFinite.Space

namespace OAI

/-! Joint. -/

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
namespace GaussianFactorization
open MeasureTheory ProbabilityTheory Complex CoherentFock GaussianCoherent
open scoped BigOperators InnerProductSpace ComplexConjugate
variable {κ E : Type*} [Fintype κ] [NormedAddCommGroup E] [InnerProductSpace ℂ E]

abbrev Joint (κ E : Type*) [Fintype κ] := HilbertPair.Space (Mode κ) E
abbrev Hilbert (κ E : Type*) [Fintype κ] [NormedAddCommGroup E] [InnerProductSpace ℂ E] :=
  Lp (Space E) 2 (GaussianFourier.law κ)

def wave (d : Joint κ E) (g : κ → ℝ) : Space E :=
  GaussianCoherent.wave d.fst g • coherent d.snd

theorem continuous_wave (d : Joint κ E) : Continuous (wave d) :=
  (GaussianCoherent.continuous_wave d.fst).smul continuous_const

@[simp] theorem norm_wave (d : Joint κ E) (g : κ → ℝ) :
    ‖wave d g‖=‖GaussianCoherent.wave d.fst g‖ := by
  simp [wave,norm_smul]

theorem memLp_wave (d : Joint κ E) : MemLp (wave d) 2 (GaussianFourier.law κ) :=
  (GaussianCoherent.memLp_wave d.fst).congr_norm (continuous_wave d).aestronglyMeasurable
    (Filter.Eventually.of_forall fun g => (norm_wave d g).symm)

def vector (d : Joint κ E) : Hilbert κ E := (memLp_wave d).toLp (wave d)

theorem vector_ae (d : Joint κ E) :
    (vector d : (κ → ℝ) → Space E)=ᵐ[GaussianFourier.law κ] wave d := MemLp.coeFn_toLp _

theorem kernel_joint (d e : Joint κ E) : kernel d e=kernel d.fst e.fst*kernel d.snd e.snd := by
  unfold kernel
  rw [←Complex.exp_add]
  congr 1
  rw [WithLp.prod_norm_sq_eq_of_L2,WithLp.prod_norm_sq_eq_of_L2]
  simp only [WithLp.prod_inner_apply]
  change Complex.ofReal (-(‖d.fst‖^2+‖d.snd‖^2)/2)+
      (⟪d.fst,e.fst⟫_ℂ+⟪d.snd,e.snd⟫_ℂ)+Complex.ofReal (-(‖e.fst‖^2+‖e.snd‖^2)/2)=_
  push_cast
  ring

@[simp] theorem inner_vector (d e : Joint κ E) : ⟪vector d,vector e⟫_ℂ=kernel d e := by
  rw [L2.inner_def,kernel_joint,←GaussianCoherent.integral_wave_pair,←integral_mul_const]
  apply integral_congr_ae
  filter_upwards [vector_ae d,vector_ae e] with g hd he
  rw [hd,he]
  simp only [wave,inner_smul_left,inner_smul_right,inner_coherent]
  ring

 

def preMap : PreSpace (Joint κ E) →ₗᵢ[ℂ] Hilbert κ E :=
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

def representation : Space (Joint κ E) →ₗᵢ[ℂ] Hilbert κ E where
  toLinearMap := preMap.toContinuousLinearMap.fromCompletion.toLinearMap
  norm_map' x := by
    refine UniformSpace.Completion.induction_on x
      (isClosed_eq (preMap.toContinuousLinearMap.fromCompletion.continuous.norm) continuous_norm)
      fun y => ?_
    change ‖preMap.toContinuousLinearMap.fromCompletion (y:Space (Joint κ E))‖=
      ‖(y:Space (Joint κ E))‖
    rw [ContinuousLinearMap.fromCompletion_apply_coe,UniformSpace.Completion.norm_coe]
    exact preMap.norm_map y

@[simp] theorem representation_coherent (d : Joint κ E) : representation (coherent d)=vector d := by
  change preMap.toContinuousLinearMap.fromCompletion
    ((toFinsupp.symm (Finsupp.single d 1):PreSpace (Joint κ E)):Space (Joint κ E))=vector d
  rw [ContinuousLinearMap.fromCompletion_apply_coe]
  change Finsupp.linearCombination ℂ vector (Finsupp.single d 1)=vector d
  simp

 

theorem representation_surjective : Function.Surjective (representation (κ := κ) (E := E)) := by
  let K := (representation (κ := κ) (E := E)).toLinearMap.range
  have hK : IsClosed (K : Set (Hilbert κ E)) :=
    (representation (κ := κ) (E := E)).isometry.isClosedEmbedding.isClosed_range
  have hbot : Kᗮ=⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro f hf
    apply Lp.ext
    have hi : Integrable (fun g => f g) (GaussianFourier.law κ) :=
      memLp_one_iff_integrable.mp ((Lp.memLp f).mono_exponent (by norm_num))
    have hcoef (x : E) : (fun g => ⟪coherent x,f g⟫_ℂ)=ᵐ[GaussianFourier.law κ] 0 := by
      apply FourierDensity.ae_zero_of_fourier_zero (hi.const_inner (coherent x))
      intro a
      let d : Joint κ E := WithLp.toLp 2 (realMode (-a),x)
      have hh := (Submodule.mem_orthogonal K f).mp hf (vector d)
        ⟨coherent d,representation_coherent _⟩
      rw [L2.inner_def] at hh
      convert hh using 1
      apply integral_congr_ae
      filter_upwards [vector_ae d] with g hg
      rw [hg]
      simp only [wave,inner_smul_left]
      change FourierDensity.character a g*⟪coherent x,f g⟫_ℂ=
        conj (GaussianCoherent.wave (realMode (-a)) g)*⟪coherent x,f g⟫_ℂ
      rw [wave_realMode]
      change FourierDensity.character a g*⟪coherent x,f g⟫_ℂ=
        conj (FourierDensity.character (-a) g)*⟪coherent x,f g⟫_ℂ
      rw [FourierDensity.character_neg,Complex.conj_conj]
    have hz : (fun g => f g)=ᵐ[GaussianFourier.law κ] 0 := by
      apply hi.ae_eq_zero_of_forall_setIntegral_eq_zero
      intro s hs hsm
      apply CoherentFock.eq_zero_of_inner_coherent
      intro x
      change (innerSL ℂ (coherent x)) (∫g in s, f g ∂GaussianFourier.law κ)=0
      rw [←(innerSL ℂ (coherent x)).integral_comp_comm (hi.integrableOn (s := s))]
      change (∫g in s, ⟪coherent x,f g⟫_ℂ ∂GaussianFourier.law κ)=0
      rw [integral_congr_ae (ae_restrict_of_ae (hcoef x))]
      simp
    exact hz.trans (Lp.coeFn_zero (Space E) 2 (GaussianFourier.law κ)).symm
  apply LinearMap.range_eq_top.mp
  change K=⊤
  calc
    K=K.topologicalClosure := hK.submodule_topologicalClosure_eq.symm
    _=Kᗮᗮ := (Submodule.orthogonal_orthogonal_eq_closure K).symm
    _=⊤ := by rw [hbot,Submodule.bot_orthogonal_eq_top]

def jointGaussianUnitary : Space (Joint κ E) ≃ₗᵢ[ℂ] Hilbert κ E :=
  LinearIsometryEquiv.ofSurjective representation representation_surjective

@[simp] theorem jointGaussianUnitary_coherent (d : Joint κ E) :
    jointGaussianUnitary (coherent d)=vector d := representation_coherent d

end GaussianFactorization

namespace GaussianFactorization
open MeasureTheory ProbabilityTheory Complex CoherentFock GaussianCoherent
open scoped BigOperators InnerProductSpace ComplexConjugate
variable {κ E : Type*} [Fintype κ] [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem memLp_seedPhase (a : κ → ℝ) (f : Hilbert κ E) :
    MemLp (fun g => GaussianCoherent.wave (realMode a) g • f g) 2 (GaussianFourier.law κ) := by
  apply (Lp.memLp f).congr_norm
    ((GaussianCoherent.continuous_wave (realMode a)).aestronglyMeasurable.smul
      (Lp.aestronglyMeasurable f))
  exact Filter.Eventually.of_forall fun g => by
    change ‖f g‖=‖GaussianCoherent.wave (realMode a) g • f g‖
    rw [norm_smul,norm_wave_realMode,one_mul]

def seedPhase (a : κ → ℝ) (f : Hilbert κ E) : Hilbert κ E :=
  (memLp_seedPhase a f).toLp (fun g => GaussianCoherent.wave (realMode a) g • f g)

theorem seedPhase_ae (a : κ → ℝ) (f : Hilbert κ E) :
    (seedPhase a f : (κ → ℝ) → Space E)=ᵐ[GaussianFourier.law κ]
      fun g => GaussianCoherent.wave (realMode a) g • f g := MemLp.coeFn_toLp _

def seedPhaseIsometry (a : κ → ℝ) : Hilbert κ E →ₗᵢ[ℂ] Hilbert κ E where
  toFun := seedPhase a
  map_add' f h := by
    apply Lp.ext
    filter_upwards [seedPhase_ae a (f+h),Lp.coeFn_add f h,
      Lp.coeFn_add (seedPhase a f) (seedPhase a h),seedPhase_ae a f,seedPhase_ae a h]
      with g h1 h2 h3 h4 h5
    rw [h1,h2,h3]
    simp only [Pi.add_apply,h4,h5,smul_add]
  map_smul' c f := by
    change seedPhase a (c • f)=c • seedPhase a f
    apply Lp.ext
    filter_upwards [seedPhase_ae a (c • f),Lp.coeFn_smul c f,
      Lp.coeFn_smul c (seedPhase a f),seedPhase_ae a f] with g h1 h2 h3 h4
    rw [h1,h2,h3]
    simp only [Pi.smul_apply,h4]
    exact smul_comm _ _ _
  norm_map' f := by
    have hh : ∀ᵐ g ∂GaussianFourier.law κ, ‖seedPhase a f g‖=‖f g‖ := by
      filter_upwards [seedPhase_ae a f] with g hg
      rw [hg,norm_smul,norm_wave_realMode,one_mul]
    exact le_antisymm (Lp.norm_le_norm_of_ae_le (hh.mono fun _ h => h.le))
      (Lp.norm_le_norm_of_ae_le (hh.mono fun _ h => h.ge))

@[simp] theorem phase_inl (a : Mode κ) (d : Joint κ E) :
    phase (HilbertPair.inl a) d=phase a d.fst := by
  simp [phase,HilbertPair.inl_apply,WithLp.prod_inner_apply]

@[simp] theorem phase_inr (e : E) (d : Joint κ E) :
    phase (HilbertPair.inr e) d=phase e d.snd := by
  simp [phase,HilbertPair.inr_apply,WithLp.prod_inner_apply]

theorem seedPhase_vector (a : κ → ℝ) (d : Joint κ E) :
    seedPhaseIsometry a (vector d)=
      phase (HilbertPair.inl (realMode a)) d • vector (HilbertPair.inl (realMode a)+d) := by
  apply Lp.ext
  filter_upwards [seedPhase_ae a (vector d),vector_ae d,vector_ae (HilbertPair.inl (realMode a)+d),
    Lp.coeFn_smul (phase (HilbertPair.inl (realMode a)) d)
      (vector (HilbertPair.inl (realMode a)+d))] with g h1 h2 h3 h4
  change seedPhase a (vector d) g = _
  rw [h1,h2,h4]
  change GaussianCoherent.wave (realMode a) g • wave d g =
    phase (HilbertPair.inl (realMode a)) d • vector (HilbertPair.inl (realMode a)+d) g
  rw [h3,phase_inl]
  change GaussianCoherent.wave (realMode a) g • (GaussianCoherent.wave d.fst g • coherent d.snd)=
    phase (realMode a) d.fst • (GaussianCoherent.wave (realMode a+d.fst) g • coherent (0+d.snd))
  rw [zero_add,smul_smul,smul_smul,phase_wave_real_add]

 
theorem representation_W_external (a : κ → ℝ) (x : Space (Joint κ E)) :
    representation (W (HilbertPair.inl (realMode a)) x)=
      seedPhaseIsometry a (representation x) := by
  have he : (representation (E:=E)).toContinuousLinearMap.comp (W (HilbertPair.inl (realMode a)))=
      (seedPhaseIsometry a).toContinuousLinearMap.comp representation.toContinuousLinearMap := by
    apply CoherentFock.ext_coherent
    intro d
    simp only [ContinuousLinearMap.comp_apply,LinearIsometry.coe_toContinuousLinearMap,
      W_coherent,map_smul,representation_coherent,seedPhase_vector]
  exact DFunLike.congr_fun he x

theorem endogenous_vector (e : E) (d : Joint κ E) :
    (W e).compLpL 2 (GaussianFourier.law κ) (vector d)=
      phase (HilbertPair.inr e) d • vector (HilbertPair.inr e+d) := by
  apply Lp.ext
  filter_upwards [(W e).coeFn_compLpL (vector d),vector_ae d,
    vector_ae (HilbertPair.inr e+d),Lp.coeFn_smul (phase (HilbertPair.inr e) d)
      (vector (HilbertPair.inr e+d))] with g h1 h2 h3 h4
  rw [h1,h2,h4]
  change W e (wave d g)=phase (HilbertPair.inr e) d • vector (HilbertPair.inr e+d) g
  rw [h3,phase_inr]
  change W e (GaussianCoherent.wave d.fst g • coherent d.snd)=
    phase e d.snd • (GaussianCoherent.wave (0+d.fst) g • coherent (e+d.snd))
  rw [zero_add,map_smul,W_coherent]
  exact smul_comm _ _ _

 

theorem representation_W_endogenous (e : E) (x : Space (Joint κ E)) :
    representation (W (HilbertPair.inr e) x)=
      (W e).compLpL 2 (GaussianFourier.law κ) (representation x) := by
  have he : representation.toContinuousLinearMap.comp (W (HilbertPair.inr e : Joint κ E))=
      ((W e).compLpL 2 (GaussianFourier.law κ)).comp representation.toContinuousLinearMap := by
    apply CoherentFock.ext_coherent
    intro d
    simp only [ContinuousLinearMap.comp_apply,LinearIsometry.coe_toContinuousLinearMap,
      W_coherent,map_smul,representation_coherent,endogenous_vector]
  exact DFunLike.congr_fun he x

end GaussianFactorization

 

open scoped BigOperators Topology InnerProductSpace
open Filter
namespace QuantumCLT
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [NormOneClass A] [CompleteSpace A]

 
theorem exp_remainder_bound (x : A) (n : ℕ) :
    ‖NormedSpace.exp x-∑ k ∈ Finset.range n, ((k.factorial:ℂ)⁻¹) • x^k‖ ≤
      ‖x‖^n * Real.exp ‖x‖ := by
  have hs := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) x
  have hn := NormedSpace.norm_expSeries_summable' (𝕂 := ℂ) x
  have ht : NormedSpace.exp x-∑ k ∈ Finset.range n, ((k.factorial:ℂ)⁻¹) • x^k=
      ∑' k : ℕ, (((k+n).factorial:ℂ)⁻¹) • x^(k+n) := by
    rw [← hs.tsum_eq,← hs.summable.sum_add_tsum_nat_add n]
    abel
  rw [ht]
  have hb : HasSum (fun k : ℕ => ‖x‖^n * (‖x‖^k/(k.factorial:ℝ)))
      (‖x‖^n*Real.exp ‖x‖) := by
    simpa [smul_eq_mul,div_eq_mul_inv,mul_comm,← Real.exp_eq_exp_ℝ] using
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ‖x‖).mul_left (‖x‖^n)
  calc
    _ ≤ ∑' k : ℕ, ‖(((k+n).factorial:ℂ)⁻¹) • x^(k+n)‖ :=
      norm_tsum_le_tsum_norm ((summable_nat_add_iff n).mpr hn)
    _ ≤ ∑' k : ℕ, ‖x‖^n * (‖x‖^k/(k.factorial:ℝ)) := by
      apply Summable.tsum_le_tsum _ ((summable_nat_add_iff n).mpr hn) hb.summable
      intro k
      rw [norm_smul, norm_inv,Complex.norm_natCast]
      calc
        _ ≤ ((k+n).factorial:ℝ)⁻¹*(‖x‖^(k+n)) := by
          gcongr
          exact norm_pow_le x (k+n)
        _ ≤ (k.factorial:ℝ)⁻¹*(‖x‖^(k+n)) := by
          gcongr
          exact Nat.le_add_right k n
        _ = _ := by rw [pow_add]; ring
    _ = _ := hb.tsum_eq

theorem norm_exp_le (x : A) : ‖NormedSpace.exp x‖ ≤ Real.exp ‖x‖ := by
  simpa using exp_remainder_bound x 0

 
theorem exp_second_bound (X : A) (r L : ℝ) (hL : 0 ≤ L) (hX : ‖X‖ ≤ L)
    (hr : |r| ≤ 1) :
    ‖NormedSpace.exp ((r:ℂ) • X)-1-(r:ℂ) • X-((r^2/2:ℝ):ℂ) • X^2‖ ≤
       (L^3*Real.exp L)*|r|^3 := by
  have h := exp_remainder_bound ((r:ℂ) • X) 3
  have he : (∑ k ∈ Finset.range 3, ((k.factorial:ℂ)⁻¹) • ((r:ℂ) • X)^k)=
      1+(r:ℂ) • X+((r^2/2:ℝ):ℂ) • X^2 := by
    simp [Finset.sum_range_succ,smul_pow]
    module
  rw [he] at h
  have hn : ‖(r:ℂ) • X‖ ≤ L := by
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left hX (abs_nonneg r)).trans (by nlinarith)
  calc
    _ = ‖NormedSpace.exp ((r:ℂ) • X)-(1+(r:ℂ) • X+((r^2/2:ℝ):ℂ) • X^2)‖ := by congr 1; abel
    _ ≤ ‖(r:ℂ) • X‖^3*Real.exp ‖(r:ℂ) • X‖ := h
    _ ≤ (|r| * L)^3*Real.exp L := by
      gcongr
      · simpa only [norm_smul,Complex.norm_real,Real.norm_eq_abs] using mul_le_mul_of_nonneg_left hX (abs_nonneg r)
    _ = _ := by ring

omit [NormOneClass A] [CompleteSpace A] in
 
theorem product_second_bound (f g a b c d : A) (r C D K : ℝ)
    (hC : 0 ≤ C) (_hD : 0 ≤ D) (hK : 0 ≤ K) (hr : |r| ≤ 1)
    (hf : ‖f-1-(r:ℂ) • a-((r:ℂ)^2) • b‖ ≤ C*|r|^3)
    (hg : ‖g-1-(r:ℂ) • c-((r:ℂ)^2) • d‖ ≤ D*|r|^3)
    (hnf : ‖f‖ ≤ K) :
    ‖f*g-1-(r:ℂ) • (a+c)-((r:ℂ)^2) • (b+d+a*c)‖ ≤
      (C+(‖b‖+C)*‖c‖+(‖a‖+‖b‖+C)*‖d‖+K*D)*|r|^3 := by
  have hp : |r|^3 ≤ |r|^2 := by nlinarith [sq_nonneg |r|]
  have h2 : ‖f-1-(r:ℂ) • a‖ ≤ (‖b‖+C)*|r|^2 := by
    calc
      _ = ‖(f-1-(r:ℂ) • a-((r:ℂ)^2) • b)+((r:ℂ)^2) • b‖ := by congr 1; abel
      _ ≤ ‖f-1-(r:ℂ) • a-((r:ℂ)^2) • b‖+‖((r:ℂ)^2) • b‖ := norm_add_le _ _
      _ ≤ C*|r|^3+|r|^2*‖b‖ := by
        rw [norm_smul,Complex.norm_pow,Complex.norm_real,Real.norm_eq_abs]
        exact add_le_add hf le_rfl
      _ ≤ C*|r|^2+|r|^2*‖b‖ := by gcongr
      _ = _ := by ring
  have hp' : |r|^2 ≤ |r| := by nlinarith [abs_nonneg r]
  have h1 : ‖f-1‖ ≤ (‖a‖+‖b‖+C)*|r| := by
    calc
      _ = ‖(f-1-(r:ℂ) • a)+(r:ℂ) • a‖ := by congr 1; abel
      _ ≤ ‖f-1-(r:ℂ) • a‖+‖(r:ℂ) • a‖ := norm_add_le _ _
      _ ≤ (‖b‖+C)*|r|^2+|r| *‖a‖ := by
        simpa only [norm_smul,Complex.norm_real,Real.norm_eq_abs] using add_le_add h2 (le_refl ‖(r:ℂ) • a‖)
      _ ≤ (‖b‖+C)*|r|+|r| *‖a‖ := by gcongr
      _ = _ := by ring
  have he : f*g-1-(r:ℂ) • (a+c)-((r:ℂ)^2) • (b+d+a*c)=
      (f-1-(r:ℂ) • a-((r:ℂ)^2) • b)+
      (r:ℂ) • ((f-1-(r:ℂ) • a)*c)+
      ((r:ℂ)^2) • ((f-1)*d)+
      f*(g-1-(r:ℂ) • c-((r:ℂ)^2) • d) := by
    simp only [mul_sub,sub_mul,one_mul,mul_one,mul_smul_comm,smul_mul_assoc]
    module
  rw [he]
  calc
    _ ≤ ‖f-1-(r:ℂ) • a-((r:ℂ)^2) • b‖+
      ‖(r:ℂ) • ((f-1-(r:ℂ) • a)*c)‖+
      ‖((r:ℂ)^2) • ((f-1)*d)‖+
      ‖f*(g-1-(r:ℂ) • c-((r:ℂ)^2) • d)‖ :=
        (norm_add_le _ _).trans (add_le_add
          ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ C*|r|^3+|r| *((‖b‖+C)*|r|^2*‖c‖)+
      |r|^2*((‖a‖+‖b‖+C)*|r| *‖d‖)+K*(D*|r|^3) := by
      simp only [norm_smul,Complex.norm_pow,Complex.norm_real,Real.norm_eq_abs]
      exact add_le_add (add_le_add (add_le_add hf
        (mul_le_mul_of_nonneg_left ((norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))) (abs_nonneg r)))
        (mul_le_mul_of_nonneg_left ((norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))) (sq_nonneg |r|)))
        ((norm_mul_le _ _).trans (mul_le_mul hnf hg (norm_nonneg _) hK))
    _ = _ := by ring

 
def HasSecond (f : ℝ → A) (a b : A) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, |r| ≤ 1 →
    ‖f r-1-(r:ℂ) • a-((r:ℂ)^2) • b‖ ≤ C*|r|^3

omit [CompleteSpace A] in
theorem jet_norm_bound {f : ℝ → A} {a b : A} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ r : ℝ, |r| ≤ 1 → ‖f r-1-(r:ℂ) • a-((r:ℂ)^2) • b‖ ≤ C*|r|^3)
    {r : ℝ} (hr : |r| ≤ 1) : ‖f r‖ ≤ 1+‖a‖+‖b‖+C := by
  have he : f r=1+(r:ℂ) • a+((r:ℂ)^2) • b+
      (f r-1-(r:ℂ) • a-((r:ℂ)^2) • b) := by abel
  calc
    ‖f r‖ ≤ ‖1+(r:ℂ) • a+((r:ℂ)^2) • b‖+
      ‖f r-1-(r:ℂ) • a-((r:ℂ)^2) • b‖ := by nth_rw 1 [he]; exact norm_add_le _ _
    _ ≤ ‖1+(r:ℂ) • a+((r:ℂ)^2) • b‖+C*|r|^3 := add_le_add le_rfl (hf r hr)
    _ ≤ (‖(1:A)‖+‖(r:ℂ) • a‖+‖((r:ℂ)^2) • b‖)+C*|r|^3 := by
      exact add_le_add ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl
    _ ≤ _ := by
      simp only [norm_one,norm_smul,Complex.norm_pow,Complex.norm_real,Real.norm_eq_abs]
      have h2 : |r|^2 ≤ 1 := by nlinarith [abs_nonneg r]
      have h3 : |r|^3 ≤ 1 := (pow_le_pow_left₀ (abs_nonneg r) hr 3).trans (by norm_num)
      nlinarith [norm_nonneg a,norm_nonneg b,mul_le_mul_of_nonneg_right hr (norm_nonneg a),
        mul_le_mul_of_nonneg_right h2 (norm_nonneg b),mul_le_mul_of_nonneg_left h3 hC]

omit [CompleteSpace A] in
theorem HasSecond.mul {f g : ℝ → A} {a b c d : A}
    (hf : HasSecond f a b) (hg : HasSecond g c d) :
    HasSecond (fun r => f r*g r) (a+c) (b+d+a*c) := by
  obtain ⟨C,hC,hf⟩ := hf
  obtain ⟨D,hD,hg⟩ := hg
  let K := 1+‖a‖+‖b‖+C
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨C+(‖b‖+C)*‖c‖+(‖a‖+‖b‖+C)*‖d‖+K*D,by positivity,fun r hr => ?_⟩
  exact product_second_bound _ _ _ _ _ _ r C D K hC hD hK hr (hf r hr) (hg r hr)
    (jet_norm_bound hC hf hr)

theorem exp_hasSecond (X : A) :
    HasSecond (fun r : ℝ => NormedSpace.exp ((r:ℂ) • X)) X ((2:ℂ)⁻¹ • X^2) := by
  refine ⟨‖X‖^3*Real.exp ‖X‖,by positivity,fun r hr => ?_⟩
  have he : ((r:ℂ)^2) • ((2:ℂ)⁻¹ • X^2)=((r^2/2:ℝ):ℂ) • X^2 := by
    rw [smul_smul]
    congr 1
    push_cast
    ring
  rw [he]
  exact exp_second_bound X r ‖X‖ (norm_nonneg _) le_rfl hr

 
def generators (xs : List A) (r : ℝ) : A := (xs.map fun X => NormedSpace.exp ((r:ℂ) • X)).prod

def second : List A → A
  | [] => 0
  | X::xs => (2:ℂ)⁻¹ • X^2+second xs+X*xs.sum

theorem generators_hasSecond (xs : List A) : HasSecond (generators xs) xs.sum (second xs) := by
  induction xs with
  | nil => refine ⟨0,le_rfl,?_⟩; intro r hr; simp [generators,second]
  | cons X xs ih =>
    change HasSecond (fun r => NormedSpace.exp ((r:ℂ) • X)*generators xs r)
      (X+xs.sum) ((2:ℂ)⁻¹ • X^2+second xs+X*xs.sum)
    exact HasSecond.mul (exp_hasSecond X) ih

omit [NormOneClass A] [CompleteSpace A] in
 
theorem HasSecond.matrixElement {f : ℝ → A} {a b : A} (hf : HasSecond f a b)
    (φ : A →L[ℂ] ℂ) (hφ : φ 1=1) (hc : φ a=0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, |r| ≤ 1 →
      ‖φ (f r)-1-(r:ℂ)^2*φ b‖ ≤ C*|r|^3 := by
  obtain ⟨C,hC,hf⟩ := hf
  refine ⟨‖φ‖*C,by positivity,fun r hr => ?_⟩
  calc
    _ = ‖φ (f r-1-(r:ℂ) • a-((r:ℂ)^2) • b)‖ := by simp [hφ,hc]
    _ ≤ ‖φ‖*‖f r-1-(r:ℂ) • a-((r:ℂ)^2) • b‖ := φ.le_opNorm _
    _ ≤ _ := by simpa [mul_assoc] using mul_le_mul_of_nonneg_left (hf r hr) (norm_nonneg φ)

 
theorem scalar_scaled_limit (f : ℕ → ℂ) (b : ℕ → ℂ) (c : ℂ)
    (hb : Tendsto b atTop (𝓝 c)) (C : ℝ) (_hC : 0 ≤ C)
    (hf : ∀ n : ℕ, 0 < n → ‖f n-1-(n:ℂ)⁻¹*b n‖ ≤ C*(Real.sqrt (n:ℝ))⁻¹^3) :
    Tendsto (fun n : ℕ => (n:ℂ)*(f n-1)) atTop (𝓝 c) := by
  have hs : Tendsto (fun n : ℕ => (Real.sqrt (n:ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have herror : Tendsto (fun n : ℕ => (n:ℂ)*(f n-1)-b n) atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [sub_zero]
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
      (by simpa using hs.const_mul C)
    filter_upwards [Filter.eventually_gt_atTop (0:ℕ)] with n hn
    have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
    have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have hsq := Real.sq_sqrt hnR.le
    have hsn : Real.sqrt (n:ℝ) ≠ 0 := (Real.sqrt_pos.mpr hnR).ne'
    calc
      _ = ‖(n:ℂ)*(f n-1-(n:ℂ)⁻¹*b n)‖ := by congr 1; field_simp
      _ = (n:ℝ)*‖f n-1-(n:ℂ)⁻¹*b n‖ := by rw [norm_mul,Complex.norm_natCast]
      _ ≤ (n:ℝ)*(C*(Real.sqrt (n:ℝ))⁻¹^3) := mul_le_mul_of_nonneg_left (hf n hn) hnR.le
      _ = C*(Real.sqrt (n:ℝ))⁻¹ := by nth_rw 1 [← hsq]; field_simp [hsn]
  have ht : Tendsto (fun n : ℕ => (n:ℂ)*(f n-1)) atTop (𝓝 c) := by
    convert herror.add hb using 1 <;> simp
  exact ht

 
theorem scalar_power_limit (f : ℕ → ℂ) (b : ℕ → ℂ) (c : ℂ)
    (hb : Tendsto b atTop (𝓝 c)) (C : ℝ) (_hC : 0 ≤ C)
    (hf : ∀ n : ℕ, 0 < n → ‖f n-1-(n:ℂ)⁻¹*b n‖ ≤ C*(Real.sqrt (n:ℝ))⁻¹^3) :
    Tendsto (fun n => f n^n) atTop (𝓝 (Complex.exp c)) := by
  have ht := scalar_scaled_limit f b c hb C _hC hf
  simpa using Complex.tendsto_one_add_pow_exp_of_tendsto ht

 

theorem generators_vacuum_limit (xs : List A) (φ : A →L[ℂ] ℂ)
    (hφ : φ 1=1) (hc : φ xs.sum=0) :
    Tendsto (fun n : ℕ => (φ (generators xs (Real.sqrt (n:ℝ))⁻¹))^n)
      atTop (𝓝 (Complex.exp (φ (second xs)))) := by
  obtain ⟨C,hC,hf⟩ := (generators_hasSecond xs).matrixElement φ hφ hc
  apply scalar_power_limit _ (fun _ => φ (second xs)) _ tendsto_const_nhds C hC
  intro n hn
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hr : |(Real.sqrt (n:ℝ))⁻¹| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    exact inv_le_one_of_one_le₀ ((Real.le_sqrt (by norm_num) (by positivity)).mpr (by simpa using hnR))
  have hsq : (((Real.sqrt (n:ℝ))⁻¹:ℝ):ℂ)^2=(n:ℂ)⁻¹ := by
    rw [← Complex.ofReal_pow,inv_pow,Real.sq_sqrt (by positivity),Complex.ofReal_inv,Complex.ofReal_natCast]
  simpa only [hsq,abs_of_nonneg (by positivity : 0 ≤ (Real.sqrt (n:ℝ))⁻¹)] using hf _ hr

end QuantumCLT

namespace QuantumCLT
open scoped BigOperators Topology
open Filter
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [NormOneClass A] [CompleteSpace A]

 

def JetBound (L : ℝ) (f : ℝ → A) (a b : A) : Prop :=
  ‖a‖ ≤ L ∧ ‖b‖ ≤ L ∧ ∀r : ℝ, |r| ≤ 1 →
    ‖f r-1-(r:ℂ) • a-((r:ℂ)^2) • b‖ ≤ L*|r|^3

omit [CompleteSpace A] in
theorem JetBound.mul {L K : ℝ} (hL : 0 ≤ L) (hK : 0 ≤ K)
    {f g : ℝ → A} {a b c d : A} (hf : JetBound L f a b) (hg : JetBound K g c d) :
    JetBound (L+K+8*L*K) (fun r => f r*g r) (a+c) (b+d+a*c) := by
  refine ⟨?_,?_,?_⟩
  · calc
      ‖a+c‖ ≤ ‖a‖+‖c‖ := norm_add_le _ _
      _ ≤ L+K := add_le_add hf.1 hg.1
      _ ≤ L+K+8*L*K := le_add_of_nonneg_right (by positivity)
  · calc
      ‖b+d+a*c‖ ≤ ‖b‖+‖d‖+‖a‖*‖c‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_mul_le _ _))
      _ ≤ L+K+L*K := by gcongr; exact hf.2.1; exact hg.2.1; exact hf.1; exact hg.1
      _ ≤ L+K+8*L*K := by nlinarith [mul_nonneg hL hK]
  · intro r hr
    have hnorm : ‖f r‖ ≤ 1+3*L := by
      exact (jet_norm_bound hL hf.2.2 hr).trans (by linarith [hf.1,hf.2.1])
    have hh := product_second_bound (f r) (g r) a b c d r L K (1+3*L)
      hL hK (by positivity) hr (hf.2.2 r hr) (hg.2.2 r hr) hnorm
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    calc
      L+(‖b‖+L)*‖c‖+(‖a‖+‖b‖+L)*‖d‖+(1+3*L)*K
          ≤ L+(L+L)*K+(L+L+L)*K+(1+3*L)*K := by
            gcongr <;> first | exact hf.1 | exact hf.2.1 | exact hg.1 | exact hg.2.1
      _ = L+K+8*L*K := by ring

def exponentialBound (L : ℝ) : ℝ := L+L^2+L^3*Real.exp L

theorem exponentialBound_nonneg {L : ℝ} (hL : 0 ≤ L) : 0 ≤ exponentialBound L := by
  unfold exponentialBound
  positivity

theorem exp_jetBound (X : A) {L : ℝ} (hL : 0 ≤ L) (hX : ‖X‖ ≤ L) :
    JetBound (exponentialBound L) (fun r : ℝ => NormedSpace.exp ((r:ℂ) • X)) X
      ((2:ℂ)⁻¹ • X^2) := by
  refine ⟨?_,?_,?_⟩
  · exact hX.trans (by unfold exponentialBound; nlinarith [sq_nonneg L,mul_nonneg (pow_nonneg hL 3) (Real.exp_pos L).le])
  · calc
      ‖(2:ℂ)⁻¹ • X^2‖ = (2:ℝ)⁻¹*‖X^2‖ := by simp [norm_smul]
      _ ≤ (2:ℝ)⁻¹*L^2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (norm_pow_le _ _).trans (pow_le_pow_left₀ (norm_nonneg _) hX _)
      _ ≤ exponentialBound L := by
        unfold exponentialBound
        nlinarith [mul_nonneg (pow_nonneg hL 3) (Real.exp_pos L).le]
  · intro r hr
    have he : ((r:ℂ)^2) • ((2:ℂ)⁻¹ • X^2)=((r^2/2:ℝ):ℂ) • X^2 := by
      rw [smul_smul]
      congr 1
      push_cast
      ring
    rw [he]
    exact (exp_second_bound X r L hL hX hr).trans
      (mul_le_mul_of_nonneg_right (by unfold exponentialBound; nlinarith [sq_nonneg L]) (by positivity))

def orderedBound (L : ℝ) : ℕ → ℝ
  | 0 => 0
  | n+1 => exponentialBound L+orderedBound L n+8*exponentialBound L*orderedBound L n

theorem orderedBound_nonneg {L : ℝ} (hL : 0 ≤ L) (n : ℕ) : 0 ≤ orderedBound L n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp [orderedBound]
    have := exponentialBound_nonneg hL
    positivity

 

theorem generators_jetBound (xs : List A) {L : ℝ} (hL : 0 ≤ L)
    (hxs : ∀ X ∈ xs, ‖X‖ ≤ L) :
    JetBound (orderedBound L xs.length) (generators xs) xs.sum (second xs) := by
  induction xs with
  | nil => refine ⟨by simp [orderedBound],by simp [second,orderedBound],?_⟩; intro r hr; simp [generators,second,orderedBound]
  | cons X xs ih =>
    apply (exp_jetBound X hL (hxs X (by simp))).mul (exponentialBound_nonneg hL)
      (orderedBound_nonneg hL xs.length) (ih (fun Y hY => hxs Y (by simp [hY])))

 

theorem moving_generators_vacuum_limit
    {ι : Type*} (A : ℕ → Type*) [∀n, NormedRing (A n)] [∀n, NormedAlgebra ℂ (A n)]
    [∀n, NormOneClass (A n)] [∀n, CompleteSpace (A n)]
    (l : List ι) (X : ∀n, ι → A n) (φ : ∀n, A n →L[ℂ] ℂ)
    (L K : ℝ) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hX : ∀n i, i ∈ l → ‖X n i‖ ≤ L) (hφ : ∀n, ‖φ n‖ ≤ K)
    (h1 : ∀n, φ n 1=1) (hc : ∀n, φ n (l.map (X n)).sum=0)
    {z : ℂ} (hz : Tendsto (fun n => φ n (second (l.map (X n)))) atTop (𝓝 z)) :
    Tendsto (fun n : ℕ => (φ n (generators (l.map (X n)) (Real.sqrt (n:ℝ))⁻¹))^n)
      atTop (𝓝 (Complex.exp z)) := by
  apply scalar_power_limit _ (fun n => φ n (second (l.map (X n)))) z hz
    (K*orderedBound L l.length) (mul_nonneg hK (orderedBound_nonneg hL _))
  intro n hn
  have hj := generators_jetBound (l.map (X n)) hL (by
    intro Y hY
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hY
    exact hX n i hi)
  simp only [List.length_map] at hj
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hr : |(Real.sqrt (n:ℝ))⁻¹| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    exact inv_le_one_of_one_le₀ ((Real.le_sqrt (by norm_num) (by positivity)).mpr (by simpa using hnR))
  have hsq : (((Real.sqrt (n:ℝ))⁻¹:ℝ):ℂ)^2=(n:ℂ)⁻¹ := by
    rw [←Complex.ofReal_pow,inv_pow,Real.sq_sqrt (by positivity),Complex.ofReal_inv,Complex.ofReal_natCast]
  let r := (Real.sqrt (n:ℝ))⁻¹
  calc
    _ = ‖φ n (generators (l.map (X n)) r-1-(r:ℂ) • (l.map (X n)).sum-
        ((r:ℂ)^2) • second (l.map (X n)))‖ := by
      simp only [map_sub,map_smul,h1,hc,smul_eq_mul,mul_zero,sub_zero]
      dsimp only [r]
      rw [hsq]
    _ ≤ ‖φ n‖*‖generators (l.map (X n)) r-1-(r:ℂ) • (l.map (X n)).sum-
        ((r:ℂ)^2) • second (l.map (X n))‖ := (φ n).le_opNorm _
    _ ≤ K*(orderedBound L l.length*|r|^3) :=
      mul_le_mul (hφ n) (hj.2.2 r hr) (norm_nonneg _) hK
    _ = K*orderedBound L l.length*(Real.sqrt (n:ℝ))⁻¹^3 := by
      dsimp [r]
      rw [abs_of_nonneg (by positivity)]
      ring
end QuantumCLT

end

end OAI
