import OAI.MathematicalPhysics.Elasticity.BoundaryEnergy

namespace OAI

section
/-! Strictly positive Gaussian-normal moments, without relying on a numerical
constant or an unproved nondegeneracy of the boundary limit. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundaryWeights

lemma weight_zero_of_nonpos (b : ℝ) {y : Y} (hy : y 2≤0) : weight b y=0 := by
  simp [weight,Fin.prod_univ_three,factor,not_lt.mpr hy]

lemma weight_pos (b : ℝ) {y : Y} (hy : 0<y 2) : 0<weight b y := by
  simp [weight,Fin.prod_univ_three,factor,hy,Real.exp_pos]

def normalMoment (n : ℕ) : ℝ := ∫ y : Y, (y 2)^n*weight 2 y

lemma normal_moment_integrable (n : ℕ) : Integrable (fun y : Y => (y 2)^n*weight 2 y) := by
  apply (integrable_coordinate_moment (by norm_num : (0:ℝ)<2) 2 n).congr
  exact Filter.Eventually.of_forall (fun y => by
    dsimp only
    by_cases hy : 0<y 2
    · rw [abs_of_pos hy]
    · rw [weight_zero_of_nonpos 2 (le_of_not_gt hy),mul_zero,mul_zero])

lemma normalMoment_pos (n : ℕ) : 0<normalMoment n := by
  have hn (y : Y) : 0≤(y 2)^n*weight 2 y := by
    by_cases hy : 0<y 2
    · exact mul_nonneg (pow_nonneg hy.le n) (weight_nonneg 2 y)
    · rw [weight_zero_of_nonpos 2 (le_of_not_gt hy),mul_zero]
  apply (integral_pos_iff_support_of_nonneg hn (normal_moment_integrable n)).mpr
  have ho : IsOpen ({y : Y | 0<y 2}) := isOpen_lt continuous_const (continuous_apply 2)
  have hne : ({y : Y | 0<y 2}).Nonempty := ⟨fun _ => 1,by norm_num⟩
  exact (ho.measure_pos volume hne).trans_le (measure_mono (fun y hy =>
    (mul_pos (pow_pos hy _) (weight_pos 2 hy)).ne'))

lemma normalMoment_complex (n : ℕ) :
    (∫ y : Y, weight 2 y • (y 2:ℂ)^n)=(normalMoment n:ℂ) := by
  simp only [Complex.real_smul,← Complex.ofReal_pow,← Complex.ofReal_mul]
  rw [integral_complex_ofReal]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => mul_comm _ _)

end ElasticityBoundaryWeights

end
end
section
/-! The finite leading packet pairing is precisely the integrated Hermitian
isotropic density, against a strictly positive normal Gaussian moment. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace ElasticityBoundaryPacket
open Elasticity ElasticityBoundaryMVNormal ElasticityBoundaryMVCalculus
  ElasticityBoundaryWeights ElasticityBoundaryOrderBound ElasticityBoundaryProfileBounds
  ElasticityBoundaryLimit ElasticityBoundaryParameter ElasticityBoundaryEnergyLimit
  ElasticityBoundaryCutoffBound

lemma polynomial_bound (p : MP) : OrderBound (fun _ y => value p y) 0 := by
  obtain ⟨A,hA,n,h⟩ := polynomialGrowth p
  exact ⟨A,hA,n,fun _ _ _ y => by simpa using h y⟩

lemma weighted_integrable {f : Y → ℂ} (hf : Continuous f)
    (hF : OrderBound (fun _ => f) 0) {b : ℝ} (hb : 0<b) :
    Integrable (fun y => weight b y • f y) := by
  obtain ⟨A,hA,n,hB⟩ := hF
  let g : Y → ℝ := fun y => (A*2^n)*(weight b y+‖y‖^n*weight b y)
  have hg : Integrable g := ((integrable_weight hb).add (integrable_norm_moment hb n)).const_mul _
  apply hg.mono' ((measurable_weight b).aestronglyMeasurable.smul hf.aestronglyMeasurable)
  exact Eventually.of_forall (fun y => by
    change ‖weight b y • f y‖≤g y
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (weight_nonneg b y)]
    have h := hB 1 (by norm_num) le_rfl y
    simp only [pow_zero,mul_one] at h
    calc
      _ ≤ weight b y*(A*(1+‖y‖)^n) := mul_le_mul_of_nonneg_left h (weight_nonneg b y)
      _ ≤ weight b y*(A*(2^n*(1+‖y‖^n))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (one_add_pow_le (norm_nonneg y) n) hA)
          (weight_nonneg b y)
      _ = g y := by dsimp [g]; ring)

lemma frozen_integrable (n : ℕ) (c : ℂ) (p q : MP) :
    Integrable (fun y : Y => weight 2 y • ((y 2:ℂ)^n*c*value p y*star (value q y))) := by
  apply weighted_integrable
  · exact ((((Complex.continuous_ofReal.comp (continuous_apply 2)).pow n).mul continuous_const).mul
      (smooth_value p).continuous).mul (smooth_value q).continuous.star
  · have hc : OrderBound (fun (_ : ℝ) (_ : Y) => c) 0 := by
      exact ⟨‖c‖,norm_nonneg _,0,fun _ _ _ _ => by simp⟩
    exact (((normal_power_bound n).mul hc).mul (polynomial_bound p)).mul (OrderBound.conj (polynomial_bound q))
  · norm_num

lemma frozenPair_integral (n : ℕ) (a : I → I → I → I → ℂ) (p q : W) :
    frozenPair n a p q=∫ y : Y, weight 2 y • ((y 2:ℂ)^n*
      tensorDensity a (fun i α => value (E₀ α (p i)) y) (fun j β => value (E₀ β (q j)) y)) := by
  have hi (i α j β : I) := frozen_integrable n (a i α j β) (E₀ α (p i)) (E₀ β (q j))
  have hfun (y : Y) : weight 2 y • ((y 2:ℂ)^n*
      tensorDensity a (fun i α => value (E₀ α (p i)) y) (fun j β => value (E₀ β (q j)) y))=
      ∑ i, ∑ α, ∑ j, ∑ β, weight 2 y • ((y 2:ℂ)^n*a i α j β*
        value (E₀ α (p i)) y*star (value (E₀ β (q j)) y)) := by
    simp only [tensorDensity,Finset.mul_sum,Finset.smul_sum,mul_assoc]
  simp_rw [hfun]
  unfold frozenPair
  symm
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun α _ =>
    integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun β _ => hi i α j β))))]
  apply Finset.sum_congr rfl; intro i _
  rw [integral_finsetSum _ (fun α _ => integrable_finsetSum _ (fun j _ =>
    integrable_finsetSum _ (fun β _ => hi i α j β)))]
  apply Finset.sum_congr rfl; intro α _
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun β _ => hi i α j β))]
  apply Finset.sum_congr rfl; intro j _
  exact integral_finsetSum _ (fun β _ => hi i α j β)

lemma frozenPair_constant (n : ℕ) (a : I → I → I → I → ℂ) (p q : W) (c : ℂ)
    (h : ∀ y : Y, tensorDensity a (fun i α => value (E₀ α (p i)) y)
      (fun j β => value (E₀ β (q j)) y)=c) :
    frozenPair n a p q=(normalMoment n:ℂ)*c := by
  rw [frozenPair_integral]
  simp only [h,Complex.real_smul,← mul_assoc]
  rw [integral_mul_const]
  congr 1
  exact normalMoment_complex n

end ElasticityBoundaryPacket

end
end
section
/-! Exact transverse and longitudinal frozen physical tests. Both are genuine
solutions of the normal isotropic elasticity equation. -/
noncomputable section
open scoped BigOperators Matrix
namespace ElasticityBoundaryLeading
open Elasticity ElasticityBoundarySymbol ElasticityBoundaryMVNormal
  ElasticityBoundaryMVCalculus ElasticityBoundaryParameter ElasticityBoundaryLayerOperator
abbrev I := Fin 3
abbrev Y := I → ℝ

def leading (l m : ℂ) (f : F) : W := fun i => lift (homogeneousPolynomial l m f i)

def grad (p : W) (y : Y) : CMatrix := fun i α => value (E₀ α (p i)) y

lemma leading_normal (l m : ℂ) (hp : l+3*m≠0) (f : F) : normal l m (leading l m f)=0 := by
  change normal l m (fun i => lift (homogeneousPolynomial l m f i))=0
  rw [normal_lift,homogeneousPolynomial_physical l m hp]
  ext i
  simp

lemma leading_apply (l m : ℂ) (f : F) (i : I) :
    leading l m f i=MvPolynomial.C (f i)+MvPolynomial.X 2*MvPolynomial.C (ElasticityBoundarySymbol.slope l m f i) := by
  simp only [leading,homogeneousPolynomial,map_add,map_mul,lift_C,lift_X]

lemma grad_leading (l m : ℂ) (f : F) (y : Y) (i α : I) :
    grad (leading l m f) y i α=
      if α=0 then Complex.I*(f i+(y 2:ℂ)*ElasticityBoundarySymbol.slope l m f i)
      else if α=1 then 0 else ElasticityBoundarySymbol.slope l m f i-f i-(y 2:ℂ)*ElasticityBoundarySymbol.slope l m f i := by
  rw [grad,leading_apply]
  fin_cases α <;> simp [E₀,value_smul] <;> ring

lemma tensorDensity_factor (D : ℂ) (a : I → I → I → I → ℂ) (P Q : CMatrix) :
    tensorDensity (fun i α j β => D*a i α j β) P Q=D*tensorDensity a P Q := by
  simp only [tensorDensity,Finset.mul_sum,mul_assoc]

lemma transverse_density (l₁ m₁ l₂ m₂ L M : ℂ) (y : Y) :
    tensorDensity (elasticityTensor L M)
      (grad (leading l₁ m₁ ![0,1,0]) y) (grad (leading l₂ m₂ ![0,1,0]) y)=2*M := by
  rw [tensorDensity_isotropic]
  simp only [sesquiDensity,Fin.sum_univ_three,grad_leading]
  simp [ElasticityBoundarySymbol.slope]
  ring

lemma longitudinal_trace (l m : ℂ) (hp : l+3*m≠0) (y : Y) :
    (∑ i, grad (leading l m ![1,0,0]) y i i)=Complex.I*(2*m/(l+3*m)) := by
  simp [Fin.sum_univ_three,grad_leading,ElasticityBoundarySymbol.slope]
  have hp' : l+m*3≠0 := by simpa only [mul_comm] using hp
  field_simp [hp,hp']
  ring

lemma longitudinal_density (l₁ m₁ l₂ m₂ : ℂ) (hp₁ : l₁+3*m₁≠0) (hp₂ : l₂+3*m₂≠0)
    (L : ℂ) (y : Y) :
    tensorDensity (elasticityTensor L 0)
      (grad (leading l₁ m₁ ![1,0,0]) y) (grad (leading l₂ m₂ ![1,0,0]) y)=
      L*(Complex.I*(2*m₁/(l₁+3*m₁)))*star (Complex.I*(2*m₂/(l₂+3*m₂))) := by
  rw [tensorDensity_isotropic]
  simp only [sesquiDensity,zero_div,zero_mul,add_zero,longitudinal_trace l₁ m₁ hp₁,
    longitudinal_trace l₂ m₂ hp₂]

lemma longitudinal_trace_ne (l m : ℂ) (hm : m≠0) (hp : l+3*m≠0) :
    Complex.I*(2*m/(l+3*m))≠0 :=
  mul_ne_zero Complex.I_ne_zero (div_ne_zero (mul_ne_zero (by norm_num) hm) hp)

end ElasticityBoundaryLeading

end
end
section
/-! Nondegenerate extraction of the two genuine isotropic scalar coefficients.
Tests are the actual frozen normal solutions, not arbitrary symbol data. -/
noncomputable section
open scoped Matrix BigOperators
namespace ElasticityBoundaryPacket
open Elasticity ElasticityBoundaryLeading ElasticityBoundaryWeights
  ElasticityBoundarySymbol ElasticityBoundaryMVNormal ElasticityBoundaryParameter ElasticityBoundaryLayerOperator

lemma pair_separates (n : ℕ) (l₁ m₁ l₂ m₂ D L M : ℂ)
    (hm₁ : m₁≠0) (hm₂ : m₂≠0) (hp₁ : l₁+3*m₁≠0) (hp₂ : l₂+3*m₂≠0)
    (hD : D≠0)
    (h : ∀ p q : W, normal l₁ m₁ p=0 → normal l₂ m₂ q=0 →
      frozenPair n (fun i α j β => D*elasticityTensor L M i α j β) p q=0) : L=0 ∧ M=0 := by
  have hmoment : (normalMoment n:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (normalMoment_pos n).ne'
  have hM : M=0 := by
    have hh := h (leading l₁ m₁ ![0,1,0]) (leading l₂ m₂ ![0,1,0])
      (leading_normal l₁ m₁ hp₁ _) (leading_normal l₂ m₂ hp₂ _)
    have he := frozenPair_constant n (fun i α j β => D*elasticityTensor L M i α j β)
      (leading l₁ m₁ ![0,1,0]) (leading l₂ m₂ ![0,1,0]) (D*(2*M)) (fun y => by
        change tensorDensity _ (grad _ y) (grad _ y)=_
        rw [tensorDensity_factor,transverse_density])
    rw [he] at hh
    exact (mul_eq_zero.mp ((mul_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hmoment)).resolve_left hD)).resolve_left
      (by norm_num)
  refine ⟨?_,hM⟩
  have hh := h (leading l₁ m₁ ![1,0,0]) (leading l₂ m₂ ![1,0,0])
    (leading_normal l₁ m₁ hp₁ _) (leading_normal l₂ m₂ hp₂ _)
  have he := frozenPair_constant n (fun i α j β => D*elasticityTensor L M i α j β)
    (leading l₁ m₁ ![1,0,0]) (leading l₂ m₂ ![1,0,0])
    (D*(L*(Complex.I*(2*m₁/(l₁+3*m₁)))*star (Complex.I*(2*m₂/(l₂+3*m₂))))) (fun y => by
      change tensorDensity _ (grad _ y) (grad _ y)=_
      rw [hM,tensorDensity_factor,longitudinal_density l₁ m₁ l₂ m₂ hp₁ hp₂])
  rw [he] at hh
  have ht₁ := longitudinal_trace_ne l₁ m₁ hm₁ hp₁
  have ht₂ : star (Complex.I*(2*m₂/(l₂+3*m₂)))≠0 := star_ne_zero.mpr
    (longitudinal_trace_ne l₂ m₂ hm₂ hp₂)
  exact (mul_eq_zero.mp ((mul_eq_zero.mp ((mul_eq_zero.mp
    ((mul_eq_zero.mp hh).resolve_left hmoment)).resolve_left hD)).resolve_right ht₂)).resolve_right ht₁

end ElasticityBoundaryPacket

end
end
section
/-! Boundary values of BOTH Lamé parameters from the literal physical DN map
on an arbitrary honest smooth domain. This is not a near-boundary assumption. -/
noncomputable section
open Set
open scoped Topology BigOperators
namespace ElasticityBoundaryPacket
open Elasticity ElasticityBoundaryLayerOperator
variable {Ω : Set X} {x : X}

lemma elasticityTensor_sub (l₁ m₁ l₂ m₂ : ℂ) (i α j β : I) :
    elasticityTensor l₁ m₁ i α j β-elasticityTensor l₂ m₂ i α j β=
      elasticityTensor (l₁-l₂) (m₁-m₂) i α j β := by
  unfold elasticityTensor
  ring

lemma admissible_frozen_ne {l m : X → ℝ} (ha : Admissible Ω l m) (hx : x∈closure Ω) :
    (m x:ℂ)≠0 ∧ (l x:ℂ)+3*(m x:ℂ)≠0 := by
  obtain ⟨hm,he⟩ := ha.2.2 x hx
  constructor
  · exact Complex.ofReal_ne_zero.mpr hm.ne'
  · have hp : 0<l x+3*m x := by linarith
    exact_mod_cast hp.ne'

lemma Setup.boundary_values (s : Setup Ω x) {l₁ m₁ l₂ m₂ : X → ℝ}
    (hl₁ : ContDiff ℝ (⊤ : ℕ∞) l₁) (hm₁ : ContDiff ℝ (⊤ : ℕ∞) m₁)
    (hl₂ : ContDiff ℝ (⊤ : ℕ∞) l₂) (hm₂ : ContDiff ℝ (⊤ : ℕ∞) m₂)
    (ha₁ : Admissible Ω l₁ m₁) (ha₂ : Admissible Ω l₂ m₂)
    (hO : IsOpen Ω) (hB : Bornology.IsBounded Ω) (hx : x∈closure Ω)
    (hDN : DN Ω l₁ m₁=DN Ω l₂ m₂) : l₁ x=l₂ x ∧ m₁ x=m₂ x := by
  obtain ⟨H₁,hH₁c,hH₁s,hH₁⟩ := s.compact_energy_coefficients
    (Complex.ofRealCLM.contDiff.comp hl₁) (Complex.ofRealCLM.contDiff.comp hm₁)
  obtain ⟨H₂,hH₂c,hH₂s,hH₂⟩ := s.compact_energy_coefficients
    (Complex.ofRealCLM.contDiff.comp hl₂) (Complex.ofRealCLM.contDiff.comp hm₂)
  let H := fun i α j β y => H₁ i α j β y-H₂ i α j β y
  have hHc : ∀ i α j β, Continuous (H i α j β) := fun i α j β =>
    (hH₁c i α j β).sub (hH₂c i α j β)
  have hHs : ∀ i α j β, HasCompactSupport (H i α j β) := fun i α j β =>
    (hH₁s i α j β).sub (hH₂s i α j β)
  have hH (i α j β : I) (y : Y) (hy : WithLp.toLp 2 y∈s.K) :
      s.rawCoeff (fun z => (l₁ z:ℂ)) (fun z => (m₁ z:ℂ)) i α j β y-
      s.rawCoeff (fun z => (l₂ z:ℂ)) (fun z => (m₂ z:ℂ)) i α j β y=(y 2:ℂ)^0*H i α j β y := by
    simp only [pow_zero,one_mul,H,hH₁ i α j β y hy,hH₂ i α j β y hy]
    rfl
  have hH0 : (fun i α j β => H i α j β 0)=
      (fun i α j β => (s.jacobian 0:ℂ)*elasticityTensor
        ((l₁ x:ℂ)-(l₂ x:ℂ)) ((m₁ x:ℂ)-(m₂ x:ℂ)) i α j β) := by
    funext i α j β
    have h0 := hH i α j β 0 (by simpa using s.zero_mem)
    simp only [pow_zero,one_mul] at h0
    rw [← h0]
    rw [s.rawCoeff_zero,s.rawCoeff_zero,← mul_sub,elasticityTensor_sub]
  have hpair := pair_separates 0 (l₁ x) (m₁ x) (l₂ x) (m₂ x) (s.jacobian 0)
    ((l₁ x:ℂ)-(l₂ x:ℂ)) ((m₁ x:ℂ)-(m₂ x:ℂ))
    (admissible_frozen_ne ha₁ hx).1 (admissible_frozen_ne ha₂ hx).1
    (admissible_frozen_ne ha₁ hx).2 (admissible_frozen_ne ha₂ hx).2
    (Complex.ofReal_ne_zero.mpr s.jacobian_pos.ne') (by
      intro p q hp hq
      rw [← hH0]
      exact s.extract_normal hl₁ hm₁ hl₂ hm₂ ha₁ ha₂ hO hB hx hDN 0 H hHc hHs hH p q hp hq)
  exact ⟨Complex.ofReal_injective (sub_eq_zero.mp hpair.1),
    Complex.ofReal_injective (sub_eq_zero.mp hpair.2)⟩

lemma boundary_values_global {l₁ m₁ l₂ m₂ : X → ℝ}
    (hS : SourceSmoothBoundary Ω) (hO : IsOpen Ω) (hB : Bornology.IsBounded Ω)
    (hl₁ : ContDiff ℝ (⊤ : ℕ∞) l₁) (hm₁ : ContDiff ℝ (⊤ : ℕ∞) m₁)
    (hl₂ : ContDiff ℝ (⊤ : ℕ∞) l₂) (hm₂ : ContDiff ℝ (⊤ : ℕ∞) m₂)
    (ha₁ : Admissible Ω l₁ m₁) (ha₂ : Admissible Ω l₂ m₂)
    (hDN : DN Ω l₁ m₁=DN Ω l₂ m₂) (hx : x∈frontier Ω) : l₁ x=l₂ x ∧ m₁ x=m₂ x := by
  obtain ⟨s⟩ := setup_exists hS hx
  exact s.boundary_values hl₁ hm₁ hl₂ hm₂ ha₁ ha₂ hO hB (frontier_subset_closure hx) hDN

end ElasticityBoundaryPacket

end
end
section
/-! Honest continuous normal Taylor quotients, obtained from the integral
remainder. These are actual functions of the coefficients, not assumed jets. -/
noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators
namespace ElasticityBoundaryNormalTaylor
abbrev Y := Fin 3 → ℝ

def en : Y := Pi.single 2 1

def projection (y : Y) : Y := y-(y 2) • en

def travel (y : Y) (t : ℝ) : Y := projection y+t • ((y 2) • en)

@[simp] lemma en_apply_two : en 2=1 := by simp [en]
@[simp] lemma projection_two (y : Y) : projection y 2=0 := by simp [projection]
@[simp] lemma projection_zero : projection 0=0 := by simp [projection]
@[simp] lemma travel_zero (t : ℝ) : travel 0 t=0 := by simp [travel]
@[simp] lemma travel_one (y : Y) : travel y 1=y := by simp [travel,projection]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def normalJet (n : ℕ) (f : Y → F) (y : Y) : F :=
  iteratedFDeriv ℝ n f y (fun _ => en)

def quotient (n : ℕ) (f : Y → F) (y : Y) : F :=
  (n.factorial:ℝ)⁻¹ • ∫ t in (0:ℝ)..1, (1-t)^n • normalJet (n+1) f (travel y t)

omit [CompleteSpace F] in
lemma normalJet_continuous {f : Y → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) :
    Continuous (normalJet n f) :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Y) F (fun _ => en)).continuous.comp
    (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top))

lemma travel_continuous : Continuous (fun z : Y × ℝ => travel z.1 z.2) := by
  unfold travel projection
  fun_prop

omit [CompleteSpace F] in
lemma quotient_continuous {f : Y → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) :
    Continuous (quotient n f) := by
  have hc : Continuous (Function.uncurry (fun y (t:ℝ) => (1-t)^n • normalJet (n+1) f (travel y t))) :=
    ((continuous_const.sub continuous_snd).pow n).smul
      ((normalJet_continuous hf (n+1)).comp travel_continuous)
  have h := continuous_parametric_integral_of_continuous (μ := volume) hc (isCompact_Icc (a := (0:ℝ)) (b := 1))
  have he (y : Y) : (∫ t in (0:ℝ)..1, (1-t)^n • normalJet (n+1) f (travel y t))=
      ∫ t in Icc (0:ℝ) 1, (1-t)^n • normalJet (n+1) f (travel y t) := by
    rw [intervalIntegral.integral_of_le (by norm_num),integral_Icc_eq_integral_Ioc]
  change Continuous (fun y : Y => (n.factorial:ℝ)⁻¹ • ∫ t in (0:ℝ)..1, (1-t)^n • normalJet (n+1) f (travel y t))
  simp_rw [he]
  exact (continuous_const : Continuous (fun _ : Y => (n.factorial:ℝ)⁻¹)).smul h

lemma normal_factor {f : Y → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) (y : Y)
    (hz : ∀ k≤n, normalJet k f (projection y)=0) :
    f y=(y 2)^(n+1) • quotient n f y := by
  have h := map_add_eq_sum_add_integral_iteratedFDeriv
    (f := f) (x := projection y) (y := (y 2) • en) (n := n)
    (fun _ _ => hf.contDiffAt.of_le (by exact_mod_cast le_top))
  have hv (k : ℕ) (z : Y) :
      iteratedFDeriv ℝ k f z (fun _ => (y 2) • en)=(y 2)^k • normalJet k f z := by
    rw [ContinuousMultilinearMap.map_smul_univ]
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,normalJet]
  rw [show projection y+y 2 • en=y by simp [projection]] at h
  rw [Finset.sum_eq_zero (fun k hk => by
    have hk' : k<n+1 := Finset.mem_range.mp hk
    rw [hv,hz k (by omega),smul_zero,smul_zero]),zero_add] at h
  simp_rw [hv] at h
  rw [show (fun t => (1-t)^n • ((y 2)^(n+1) • normalJet (n+1) f
    (projection y+t • (y 2 • en))))=
      (fun t => (y 2)^(n+1) • ((1-t)^n • normalJet (n+1) f (travel y t))) from by
        funext t; rw [smul_comm]; rfl] at h
  rw [intervalIntegral.integral_smul] at h
  simpa only [quotient,smul_comm (n.factorial:ℝ)⁻¹] using h

lemma quotient_zero (n : ℕ) (f : Y → F) :
    quotient n f 0=((n+1).factorial:ℝ)⁻¹ • normalJet (n+1) f 0 := by
  simp only [quotient,travel_zero]
  rw [intervalIntegral.integral_smul_const]
  have hi : (∫ t in (0:ℝ)..1, (1-t)^n)=(n+1:ℝ)⁻¹ := by
    rw [intervalIntegral.integral_comp_sub_left (fun t : ℝ => t^n) 1]
    simp [integral_pow]
  rw [hi,smul_smul]
  congr 1
  simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,mul_inv_rev]

end ElasticityBoundaryNormalTaylor

end
end

end OAI
