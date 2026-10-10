import OAI.MathematicalPhysics.Elasticity.WeakSolutions
import OAI.MathematicalPhysics.Elasticity.CGO

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped BigOperators SchwartzMap
namespace ElasticityCGO
open ElasticityAugmented
open ElasticityPhysicalAlgebra (toSmooth toSmooth_apply toSmooth_physical physical phase)
open ElasticityDistribution (finiteResidual)
abbrev S := SchwartzMap X ℂ

/-- A compact cutoff acts on every smooth amplitude, without any temperate
assumption on the amplitude itself. -/
def cut (χ : Smooth) (hc : HasCompactSupport (χ : X → ℂ)) : Smooth →ₗ[ℂ] S where
  toFun f := (hc.mul_right : HasCompactSupport ((χ : X → ℂ)*(f : X → ℂ))).toSchwartzMap
    ((smooth_coe χ).mul (smooth_coe f))
  map_add' f g := by
    ext x
    change (χ : X → ℂ) x*((f : X → ℂ) x+(g : X → ℂ) x)=_
    exact mul_add _ _ _
  map_smul' c f := by
    ext x
    change (χ : X → ℂ) x*(c*(f : X → ℂ) x)=c*((χ : X → ℂ) x*(f : X → ℂ) x)
    ring
@[simp] lemma cut_apply (χ : Smooth) (hc : HasCompactSupport (χ : X → ℂ)) (f : Smooth) (x : X) :
    cut χ hc f x=(χ : X → ℂ) x*(f : X → ℂ) x := rfl
lemma cut_local {U : Set X} (χ : Smooth) (hc : HasCompactSupport (χ : X → ℂ))
    (hχ : EqOn (χ : X → ℂ) 1 U) (f : Smooth) :
    restrictSmooth U (toSmooth (cut χ hc f))=restrictSmooth U f := by
  apply (restrictSmooth_eq_iff U _ _).mpr
  intro x hx
  simp only [toSmooth_apply,cut_apply,hχ hx,Pi.one_apply,one_mul]
lemma physical_cut_local {U : Set X} (hU : IsOpen U)
    (z : Fin 3 → ℂ) (lam m χ : Smooth)
    (hl : (lam : X → ℂ).HasTemperateGrowth) (hm : (m : X → ℂ).HasTemperateGrowth)
    (hc : HasCompactSupport (χ : X → ℂ)) (hχ : EqOn (χ : X → ℂ) 1 U)
    (u : Fin 3 → Smooth) (i : Fin 3) :
    EqOn (physical z lam m (fun j => cut χ hc (u j)) i : X → ℂ)
      ((LT (shifted coord z) lam m u i : Smooth) : X → ℂ) U := by
  change EqOn ((toSmooth (physical z lam m (fun j => cut χ hc (u j)) i) : Smooth) : X → ℂ) _ U
  apply (restrictSmooth_eq_iff U _ _).mp
  rw [toSmooth_physical z lam m hl hm,restrict_LT hU,restrict_LT hU]
  congr 1
  funext j
  exact cut_local χ hc hχ (u j)

def residual0 (lam m : Smooth) (a : Amplitude Smooth) (i : Fin 3) : Smooth :=
  R coord lam m a.1 a.2 i+(lam+m)*coord i (div coord a.1-a.2)+
    coord i lam*(div coord a.1-a.2)
def residual1 (θ : Fin 3 → ℂ) (lam m : Smooth) (a : Amplitude Smooth) (i : Fin 3) : Smooth :=
  θ i • ((lam+m)*(div coord a.1-a.2))

/-- The actual Schwartz residual has precisely the two powers h^8 and h^7.
The amplitude recursions are only required on the indicated open region. -/
theorem cut_truncation_residual {U : Set X} (hU : IsOpen U)
    (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (lam m χ : Smooth)
    (hl : (lam : X → ℂ).HasTemperateGrowth) (hm : (m : X → ℂ).HasTemperateGrowth)
    (hc : HasCompactSupport (χ : X → ℂ)) (hχ : EqOn (χ : X → ℂ) 1 U)
    (h : ℝ) (hh : h≠0) (a : ℕ → Amplitude Smooth)
    (hR₀ : leadingR (localCoord hU) θ (restrictSmooth U lam) (restrictSmooth U m)
      (localAmp U (a 0)).1 (localAmp U (a 0)).2=0)
    (hn₀ : normal θ (a 0).1=0)
    (hrec : ∀ j<8,RecursOn hU θ lam m (a j) (a (j+1))) (i : Fin 3) :
    EqOn (physical ((h : ℂ)⁻¹ • θ) lam m
      (fun j => cut χ hc ((truncation (h : ℂ) 8 a).1 j)) i : X → ℂ)
      (finiteResidual h (fun j => cut χ hc (residual0 lam m (a 8) j))
        (fun j => cut χ hc (residual1 θ lam m (a 8) j)) i : X → ℂ) U := by
  intro x hx
  rw [physical_cut_local hU _ lam m χ hl hm hc hχ _ i hx]
  have hh' : (h : ℂ)≠0 := by exact_mod_cast hh
  rw [physical_truncation_residual_on hU θ hθ lam m (h : ℂ) hh' 8 a hR₀ hn₀ hrec i hx]
  change (h : ℂ)^8 * ( _ + ((h : ℂ)⁻¹*θ i) * _) =
    (h : ℂ)^8 * ((χ : X → ℂ) x * (residual0 lam m (a 8) i : X → ℂ) x) +
    (h : ℂ)^7 * ((χ : X → ℂ) x * (residual1 θ lam m (a 8) i : X → ℂ) x)
  rw [hχ hx]
  change (h : ℂ)^8 * ( _ + ((h : ℂ)⁻¹*θ i) * _) =
    (h : ℂ)^8 * (1 * _) + (h : ℂ)^7 * (1 * (θ i * _))
  simp only [one_mul,residual0]
  field_simp

lemma phase_eq (h : ℝ) (α β : X) :
    phase h α β=(h : ℂ)⁻¹ • (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) := by
  funext i
  simp only [phase,Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm]
end ElasticityCGO

end
end
section
noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators SchwartzMap
namespace ElasticityPhysicalAlgebra
open ElasticityAugmented

lemma physical_eqOn_of_eqOn {U : Set X} (hU : IsOpen U)
    (z : Fin 3 → ℂ) (lam m : Smooth)
    (hl : (lam : X → ℂ).HasTemperateGrowth) (hm : (m : X → ℂ).HasTemperateGrowth)
    (f g : Fin 3 → SchwartzMap X ℂ) (hfg : ∀ j,EqOn (f j : X → ℂ) (g j) U) (i : Fin 3) :
    EqOn (physical z lam m f i : X → ℂ) (physical z lam m g i) U := by
  change EqOn ((toSmooth (physical z lam m f i) : Smooth) : X → ℂ)
    ((toSmooth (physical z lam m g i) : Smooth) : X → ℂ) U
  apply (restrictSmooth_eq_iff U _ _).mp
  rw [toSmooth_physical z lam m hl hm,toSmooth_physical z lam m hl hm,
    restrict_LT hU,restrict_LT hU]
  congr 1
  funext j
  exact (restrictSmooth_eq_iff U _ _).mpr (hfg j)

/-- A local physical transfer that agrees off a compact set gives a genuinely
compact supported global difference, without changing the physical equation
on its open domain. -/
theorem compactify_physical_transfer {K U : Set X} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K⊆U) (lam m : Smooth)
    (hl : (lam : X → ℂ).HasTemperateGrowth) (hm : (m : X → ℂ).HasTemperateGrowth)
    (F G : Fin 3 → SchwartzMap X ℂ) (hG : ∀ i,EqOn (physical 0 lam m G i : X → ℂ) 0 U)
    (he : ∀ i,EqOn (G i : X → ℂ) (F i) (U\K)) :
    ∃ H : Fin 3 → SchwartzMap X ℂ,(∀ i,tsupport (H i)⊆K) ∧
      (∀ i,EqOn (physical 0 lam m (F+H) i : X → ℂ) 0 U) ∧
      (∀ i,EqOn ((F+H) i : X → ℂ) (G i) U) := by
  obtain ⟨χ,hχ,hc,hs,h1,_⟩ := ElasticityBoundary.compact_smooth_cutoff hK hU hKU
  let c : Smooth := ⟨fun x => (χ x : ℂ),Complex.ofRealCLM.contDiff.comp hχ⟩
  have hc' : HasCompactSupport (c : X → ℂ) := hc.comp_left Complex.ofReal_zero
  let H : Fin 3 → SchwartzMap X ℂ := fun i => ElasticityCGO.cut c hc' (toSmooth (G i-F i))
  have hH (i) (x) : H i x=(χ x : ℂ)*(G i x-F i x) := rfl
  have heq : ∀ i,EqOn ((F+H) i : X → ℂ) (G i) U := by
    intro i x hx
    change F i x+H i x=G i x
    rw [hH]
    by_cases hxK : x∈K
    · have hx1 : χ x=1 := mem_of_mem_nhds (s := {y : X | χ y=1}) (x := x) (h1.filter_mono (nhds_le_nhdsSet hxK))
      rw [hx1,Complex.ofReal_one,one_mul]
      ring
    · rw [he i ⟨hx,hxK⟩,sub_self,mul_zero,add_zero]
  refine ⟨H,?_,?_,heq⟩
  · intro i
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hnot
    apply hx
    rw [hH]
    by_cases hxU : x∈U
    · rw [he i ⟨hxU,hnot⟩,sub_self,mul_zero]
    · have hz : χ x=0 := image_eq_zero_of_notMem_tsupport (fun hh => hxU (hs hh))
      rw [hz,Complex.ofReal_zero,zero_mul]
  · intro i x hx
    exact (physical_eqOn_of_eqOn hU 0 lam m hl hm (F+H) G heq i hx).trans (hG i hx)
end ElasticityPhysicalAlgebra

namespace Elasticity
open ElasticityDistribution
open ElasticityPhysicalAlgebra (physical)
variable {Ω B B' : Set X} {lam₁ mu₁ lam₂ mu₂ : X → ℝ}

/-- A supported smooth physical difference derived from the actual DN equality.
This is the literal compact support needed for the augmented Carleman estimate. -/
theorem physical_supported_transfer
    (ha₁ : Admissible Ω lam₁ mu₁) (ha₂ : Admissible Ω lam₂ mu₂)
    (hΩ : IsOpen Ω) (hOB : Bornology.IsBounded Ω) (hΩB : Ω⊆B)
    (hB : IsOpen B) (hB' : IsOpen B') (hsub : B'⊆B) (hcl : closure Ω⊆B')
    (hl₁ : BoundedCoefficient B lam₁) (hm₁ : BoundedCoefficient B mu₁)
    (hl₂ : BoundedCoefficient B lam₂) (hm₂ : BoundedCoefficient B mu₂)
    (he : ∀ x∉Ω, lam₁ x=lam₂ x ∧ mu₁ x=mu₂ x)
    (hDN : DN Ω lam₁ mu₁=DN Ω lam₂ mu₂)
    (L₁ M₁ L₂ M₂ N₂ O₂ : Coeff) (hN : N₂*M₂=1) (hO : O₂*(L₂+M₂+M₂)=1)
    (hL₁ : ∀ᵐ x ∂(volume.restrict B), eval L₁ x=(lam₁ x : ℂ))
    (hM₁ : ∀ᵐ x ∂(volume.restrict B), eval M₁ x=(mu₁ x : ℂ))
    (hL₂ : ∀ᵐ x ∂(volume.restrict B), eval L₂ x=(lam₂ x : ℂ))
    (hM₂ : ∀ᵐ x ∂(volume.restrict B), eval M₂ x=(mu₂ x : ℂ))
    {g : X → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    (hs : tsupport g⊆B) (h1 : Set.EqOn g 1 B') (F : Fin 3 → SchwartzMap X ℂ)
    (hF : ∀ i, Set.EqOn (physical 0 (eval L₁) (eval M₁) F i : X → ℂ) 0 B) :
    ∃ H : Fin 3 → SchwartzMap X ℂ,(∀ i,tsupport (H i)⊆closure Ω) ∧
      (∀ i,EqOn (physical 0 (eval L₂) (eval M₂) (F+H) i : X → ℂ) 0 B') ∧
      (∀ i,EqOn ((F+H) i : X → ℂ) (F i) (closure Ω)ᶜ) := by
  obtain ⟨G,hG,heG⟩ := physical_classical_transfer ha₁ ha₂ hΩ hOB hΩB hB hB' hsub
    hl₁ hm₁ hl₂ hm₂ he hDN L₁ M₁ L₂ M₂ N₂ O₂ hN hO hL₁ hM₁ hL₂ hM₂ hg hc hs h1 F hF
  obtain ⟨H,hH,hp,_⟩ := ElasticityPhysicalAlgebra.compactify_physical_transfer
    hOB.isCompact_closure hB' hcl L₂.val M₂.val (growth L₂) (growth M₂) F G hG heG
  refine ⟨H,hH,hp,?_⟩
  intro i x hx
  have hz : H i x=0 := image_eq_zero_of_notMem_tsupport (fun hh => hx (hH i hh))
  change F i x+H i x=F i x
  rw [hz,add_zero]
end Elasticity

end
end
section
noncomputable section
open scoped BigOperators
namespace ElasticityAugmented
section Algebra
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable {ι : Type*} [Fintype ι]
variable (D : ι → Derivation ℂ A A) (z : ι → ℂ) (χ : A)
omit [Fintype ι] in
lemma deriv_phase_mul (hχ : ∀ i,D i χ=z i • χ) (i : ι) (f : A) :
    D i (χ*f)=χ*(shifted D z i f) := by
  rw [partial_mul,hχ,shifted_apply]
  simp only [Algebra.smul_def]
  ring

/-- The shifted operator is the literal exponential conjugation of the
physical stress-divergence, not a new PDE declared equivalent by hypothesis. -/
theorem physical_phase_conjugation (hχ : ∀ i,D i χ=z i • χ)
    (lam m : A) (u : ι → A) (i : ι) :
    LT (fun j => (D j).toLinearMap) lam m (fun j => χ*u j) i =
      χ*LT (shifted D z) lam m u i := by
  have hd (j) (f) := deriv_phase_mul D z χ hχ j f
  change D i (lam*(∑ j,D j (χ*u j)))+
    ∑ j,D j (m*(D j (χ*u i)+D i (χ*u j)))=_
  simp only [hd,← Finset.mul_sum,← mul_add]
  have hfirst : lam*(χ*(∑ j,shifted D z j (u j)))=χ*(lam*(∑ j,shifted D z j (u j))) := by ring
  have hsecond (j) : m*(χ*(shifted D z j (u i)+shifted D z i (u j)))=
      χ*(m*(shifted D z j (u i)+shifted D z i (u j))) := by ring
  rw [hfirst,hd]
  simp_rw [hsecond,hd]
  rw [← Finset.mul_sum,← mul_add]
  rfl
end Algebra

/-- An arbitrary complex linear frequency gives a genuine global smooth
exponential on the physical real space. -/
def exponential (L : X →L[ℝ] ℂ) : Smooth := ⟨fun x => Complex.exp (L x),by
  exact (show ContDiff ℝ (⊤ : ℕ∞) (fun x => Complex.exp (L x)) from L.contDiff.cexp)⟩
lemma coord_exponential (L : X →L[ℝ] ℂ) (i : Fin 3) :
    coord i (exponential L)=L (e i) • exponential L := by
  apply Subtype.ext
  funext x
  have hh := congrArg (fun K : X →L[ℝ] ℂ => K (e i)) (L.hasFDerivAt.cexp.fderiv (x := x))
  change fderiv ℝ (fun y => Complex.exp (L y)) x (e i)=L (e i)*Complex.exp (L x)
  simpa only [smul_apply,smul_eq_mul,mul_comm] using hh
lemma exponential_ne_zero (L : X →L[ℝ] ℂ) (x : X) : (exponential L : X → ℂ) x≠0 :=
  Complex.exp_ne_zero _

theorem physical_exponential_conjugation (L : X →L[ℝ] ℂ) (lam m : Smooth)
    (u : Fin 3 → Smooth) (i : Fin 3) :
    LT (fun j => (coord j).toLinearMap) lam m (fun j => exponential L*u j) i=
      exponential L*LT (shifted coord (fun j => L (e j))) lam m u i :=
  physical_phase_conjugation coord (fun j => L (e j)) (exponential L) (coord_exponential L) lam m u i
end ElasticityAugmented

end
end
section
noncomputable section
open MeasureTheory Set
open scoped BigOperators FourierTransform

namespace ElasticityCarleman

abbrev X := EuclideanSpace ℝ (Fin 3)
abbrev Y := EuclideanSpace ℂ (Fin 4)
abbrev Direction := Fin 3 → ℂ

def e (i : Fin 3) : X := EuclideanSpace.single i 1

def deriv (f : X → Y) (i : Fin 3) : X → Y :=
  fun x => fderiv ℝ f x (e i)

def laplacian (f : X → Y) : X → Y :=
  fun x => ∑ i, deriv (deriv f i) i x

def phase (θ : Direction) (x : X) : ℂ := ∑ i, θ i * (x i : ℂ)

def conjugate (θ : Direction) (h : ℝ) (f : X → Y) : X → Y :=
  fun x => Complex.exp (-(h : ℂ)⁻¹ * phase θ x) • f x

/-- The sum-of-component semiclassical Fourier norm, written using the
Euclidean norm on the target; this is exactly that sum under the square root. -/
def sobolevNorm (h s : ℝ) (f : X → Y) : ℝ :=
  Real.sqrt (∫ ξ : X, (1 + h ^ 2 * ‖ξ‖ ^ 2) ^ s * ‖𝓕 f ξ‖ ^ 2)

def normalizedOperator (A : Fin 3 → X → Y →L[ℂ] Y) (A₀ : X → Y →L[ℂ] Y)
    (f : X → Y) : X → Y :=
  fun x => laplacian f x + (∑ i, A i x (deriv f i x)) + A₀ x (f x)

def SupportedCarlemanClaim : Prop :=
  ∀ (A : Fin 3 → X → Y →L[ℂ] Y) (A₀ : X → Y →L[ℂ] Y),
    (∀ i, ContDiff ℝ (⊤ : ℕ∞) (A i)) → ContDiff ℝ (⊤ : ℕ∞) A₀ →
    ∀ (θ : Direction), θ ≠ 0 → (∑ i, θ i * θ i) = 0 →
    ∀ (x₀ : X) (r : ℝ), 0 < r →
    ∃ C : ℝ, 0 < C ∧ ∃ h₀ : ℝ, 0 < h₀ ∧
    ∀ h : ℝ, 0 < h → h < h₀ → ∀ U : X → Y,
      ContDiff ℝ (⊤ : ℕ∞) U → HasCompactSupport U →
      tsupport U ⊆ Metric.ball x₀ r →
      sobolevNorm h 1 (conjugate θ h U) ≤
        C * h * sobolevNorm h (-1) (conjugate θ h (normalizedOperator A A₀ U))

/-- The real-linear complex phase functional. -/
def phaseCLM (θ : Direction) : X →L[ℝ] ℂ :=
  ∑ i, θ i • (Complex.ofRealCLM.comp (EuclideanSpace.proj i))

lemma phaseCLM_apply (θ : Direction) (x : X) : phaseCLM θ x = phase θ x := by
  simp [phaseCLM, phase]

lemma phaseCLM_e (θ : Direction) (i : Fin 3) : phaseCLM θ (e i) = θ i := by
  simp [phaseCLM, e, EuclideanSpace.proj, apply_ite]

def expPhase (θ : Direction) (z : ℂ) (x : X) : ℂ := Complex.exp (z * phase θ x)

lemma contDiff_expPhase (θ : Direction) (z : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (expPhase θ z) := by
  have hp : ContDiff ℝ (⊤ : ℕ∞) (phase θ) := by
    have he : (phaseCLM θ : X → ℂ) = phase θ := funext (phaseCLM_apply θ)
    rw [← he]
    exact (phaseCLM θ).contDiff
  exact (contDiff_const.mul hp).cexp

lemma fderiv_expPhase (θ : Direction) (z : ℂ) (x : X) :
    fderiv ℝ (expPhase θ z) x = (expPhase θ z x * z) • phaseCLM θ := by
  have hd := (((phaseCLM θ).hasFDerivAt (x := x)).const_mul z).cexp
  change fderiv ℝ (fun x => Complex.exp (z * phase θ x)) x = _
  simpa [expPhase, phaseCLM_apply, smul_smul] using hd.fderiv

lemma contDiff_deriv {f : X → Y} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (deriv f i) := by
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const

lemma deriv_add {f g : X → Y} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (i : Fin 3) : deriv (fun x => f x + g x) i = fun x => deriv f i x + deriv g i x := by
  funext x
  simp [deriv, fderiv_fun_add (hf x) (hg x)]

lemma deriv_const_smul {f : X → Y} (hf : Differentiable ℝ f) (a : ℂ) (i : Fin 3) :
    deriv (fun x => a • f x) i = fun x => a • deriv f i x := by
  funext x
  change fderiv ℝ (a • f) x (e i) = a • fderiv ℝ f x (e i)
  rw [fderiv_const_smul (hf x)]
  rfl

lemma deriv_expPhase_smul {f : X → Y} (hf : Differentiable ℝ f)
    (θ : Direction) (z : ℂ) (i : Fin 3) :
    deriv (fun x => expPhase θ z x • f x) i =
      fun x => expPhase θ z x • (deriv f i x + (z * θ i) • f x) := by
  funext x
  rw [deriv, fderiv_fun_smul ((contDiff_expPhase θ z).differentiable (by simp) x) (hf x),
    fderiv_expPhase]
  simp [deriv, phaseCLM_e, smul_add, smul_smul, mul_assoc]

lemma second_deriv_expPhase_smul {f : X → Y} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (θ : Direction) (z : ℂ) (i : Fin 3) :
    deriv (deriv (fun x => expPhase θ z x • f x) i) i =
      fun x => expPhase θ z x • (deriv (deriv f i) i x +
        (2 * (z * θ i)) • deriv f i x + ((z * θ i) ^ 2) • f x) := by
  have hdf := (contDiff_deriv hf i).differentiable (by simp)
  have hfd := hf.differentiable (by simp)
  rw [deriv_expPhase_smul hfd,
    deriv_expPhase_smul (f := fun x => deriv f i x + (z * θ i) • f x)
      (hdf.fun_add (hfd.fun_const_smul (z * θ i))),
    deriv_add hdf (hfd.fun_const_smul (z * θ i)),
    deriv_const_smul hfd]
  funext x
  apply congrArg (fun y : Y => expPhase θ z x • y)
  simp only [smul_add, smul_smul, pow_two]
  module

/-- Exact second-order conjugation before using the characteristic equation. -/
lemma laplacian_expPhase_smul {f : X → Y} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (θ : Direction) (z : ℂ) :
    laplacian (fun x => expPhase θ z x • f x) = fun x =>
      expPhase θ z x • (laplacian f x +
        (2 * z) • (∑ i, θ i • deriv f i x) +
        (z ^ 2 * (∑ i, θ i * θ i)) • f x) := by
  funext x
  simp only [laplacian, second_deriv_expPhase_smul hf, ← Finset.smul_sum,
    Finset.sum_add_distrib]
  apply congrArg (fun y : Y => expPhase θ z x • y)
  have h₁ : (∑ i : Fin 3, (2 * (z * θ i)) • deriv f i x) =
      (2 * z) • ∑ i, θ i • deriv f i x := by
    simp [Finset.smul_sum, smul_smul, mul_assoc]
  have h₂ : (∑ i : Fin 3, ((z * θ i) ^ 2) • f x) =
      (z ^ 2 * (∑ i, θ i * θ i)) • f x := by
    rw [← Finset.sum_smul]
    apply congrArg (fun a : ℂ => a • f x)
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h₁, h₂]

/-- The null phase removes the order-two parameter term, exactly as used in
both the supported estimate and the formal physical recursion. -/
lemma laplacian_expPhase_smul_null {f : X → Y} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (θ : Direction) (hθ : (∑ i, θ i * θ i) = 0) (z : ℂ) :
    laplacian (fun x => expPhase θ z x • f x) = fun x =>
      expPhase θ z x • (laplacian f x + (2 * z) • (∑ i, θ i • deriv f i x)) := by
  simpa [hθ] using laplacian_expPhase_smul hf θ z

/-- Full normalized conjugation identity, retaining the lower-order matrices. -/
lemma normalized_expPhase_smul {f : X → Y} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (A : Fin 3 → X → Y →L[ℂ] Y) (A₀ : X → Y →L[ℂ] Y)
    (θ : Direction) (hθ : (∑ i, θ i * θ i) = 0) (z : ℂ) :
    normalizedOperator A A₀ (fun x => expPhase θ z x • f x) =
      fun x => expPhase θ z x • (normalizedOperator A A₀ f x +
        (2 * z) • (∑ i, θ i • deriv f i x) +
        z • (∑ i, θ i • A i x (f x))) := by
  funext x
  simp only [normalizedOperator, laplacian_expPhase_smul_null hf θ hθ,
    deriv_expPhase_smul (hf.differentiable (by simp)), map_smul, map_add,
    smul_add, smul_smul, Finset.sum_add_distrib, Finset.smul_sum, mul_assoc]
  abel

end ElasticityCarleman

end
end
section
noncomputable section
open Set
open scoped BigOperators SchwartzMap
namespace ElasticityCGO
open ElasticityAugmented
open ElasticityPhysicalAlgebra (toSmooth toSmooth_apply toSmooth_physical physical)
open ElasticityCarleman (phaseCLM phaseCLM_e)

/-- Actual Schwartz representatives of the exponential physical fields on a
bounded region. No temperate behavior of the exponential is assumed. -/
def expCut (χ : Smooth) (hc : HasCompactSupport (χ : X → ℂ))
    (z : Fin 3 → ℂ) (f : S) : S :=
  cut χ hc (exponential (phaseCLM z)*toSmooth f)
@[simp] lemma expCut_apply (χ : Smooth) (hc : HasCompactSupport (χ : X → ℂ))
    (z : Fin 3 → ℂ) (f : S) (x : X) :
    expCut χ hc z f x=(χ : X → ℂ) x*Complex.exp (phaseCLM z x)*f x := by
  change (χ : X → ℂ) x*(Complex.exp (phaseCLM z x)*f x)=_
  ring
lemma shifted_zero : shifted coord (0 : Fin 3 → ℂ)=fun j => (coord j).toLinearMap := by
  funext j
  apply LinearMap.ext
  intro f
  change coord j f+(0 : ℂ) • f=coord j f
  rw [zero_smul,add_zero]
lemma phaseCLM_coords (z : Fin 3 → ℂ) : (fun j => phaseCLM z (e j))=z := by
  funext j
  exact phaseCLM_e z j

/-- The literal unshifted stress-divergence of a cut-off exponential field. -/
theorem expCut_physical {U : Set X} (hU : IsOpen U) (lam m χ : Smooth)
    (hl : (lam : X → ℂ).HasTemperateGrowth) (hm : (m : X → ℂ).HasTemperateGrowth)
    (hc : HasCompactSupport (χ : X → ℂ)) (hχ : EqOn (χ : X → ℂ) 1 U)
    (z : Fin 3 → ℂ) (f : Fin 3 → S) (i : Fin 3) :
    EqOn (physical 0 lam m (fun j => expCut χ hc z (f j)) i : X → ℂ)
      (fun x => Complex.exp (phaseCLM z x)*physical z lam m f i x) U := by
  intro x hx
  change physical 0 lam m (fun j => cut χ hc (exponential (phaseCLM z)*toSmooth (f j))) i x=_
  rw [physical_cut_local hU 0 lam m χ hl hm hc hχ _ i hx,shifted_zero,
    physical_exponential_conjugation,phaseCLM_coords,← toSmooth_physical z lam m hl hm f i]
  rfl

theorem expCut_solution {U : Set X} (hU : IsOpen U) (lam m χ : Smooth)
    (hl : (lam : X → ℂ).HasTemperateGrowth) (hm : (m : X → ℂ).HasTemperateGrowth)
    (hc : HasCompactSupport (χ : X → ℂ)) (hχ : EqOn (χ : X → ℂ) 1 U)
    (z : Fin 3 → ℂ) (f : Fin 3 → S)
    (hf : ∀ i,EqOn (physical z lam m f i : X → ℂ) 0 U) :
    ∀ i,EqOn (physical 0 lam m (fun j => expCut χ hc z (f j)) i : X → ℂ) 0 U := by
  intro i x hx
  rw [expCut_physical hU lam m χ hl hm hc hχ z f i hx]
  change Complex.exp (phaseCLM z x)*physical z lam m f i x=0
  rw [hf i hx]
  exact mul_zero _

/-- The full actual divergence is the exponential times the shifted divergence. -/
theorem div_exponential (z : Fin 3 → ℂ) (u : Fin 3 → Smooth) :
    div coord (fun j => exponential (phaseCLM z)*u j)=
      exponential (phaseCLM z)*divT (shifted coord z) u := by
  have hh (j) : coord j (exponential (phaseCLM z))=z j • exponential (phaseCLM z) := by
    rw [coord_exponential]
    exact congrArg (fun c : ℂ => c • exponential (phaseCLM z)) (phaseCLM_e z j)
  simp only [div,divT,deriv_phase_mul coord z (exponential (phaseCLM z)) hh,Finset.mul_sum]
end ElasticityCGO

end
end
section
noncomputable section
open Set
open scoped BigOperators SchwartzMap
namespace ElasticityCGO
open ElasticityAugmented
open ElasticityPhysicalAlgebra (physical physical_eqOn_of_eqOn divShift shiftD shiftD_apply)
open ElasticityCarleman (phaseCLM)

lemma phaseCLM_neg (z : Fin 3 → ℂ) : phaseCLM (-z)=-phaseCLM z := by
  ext x
  simp only [ElasticityCarleman.phaseCLM,sum_apply,smul_apply,
    Pi.neg_apply,neg_apply,smul_eq_mul,neg_mul,Finset.sum_neg_distrib]

lemma expCut_support (χ : Smooth) (hc : HasCompactSupport (χ : X → ℂ))
    (z : Fin 3 → ℂ) (f : S) : tsupport (expCut χ hc z f : X → ℂ)⊆tsupport (f : X → ℂ) := by
  have he : (expCut χ hc z f : X → ℂ)=
      (fun x => (χ : X → ℂ) x*Complex.exp (phaseCLM z x))*(f : X → ℂ) := by
    funext x
    exact expCut_apply χ hc z f x
  rw [he]
  exact tsupport_mul_subset_right

/-- Factoring the transferred PHYSICAL solution gives a shifted physical
solution. The compact difference is multiplied by the inverse exponential only
on a compact support, never regarded as a global temperate multiplier. -/
theorem transferred_amplitude {B K : Set X} (hB : IsOpen B)
    (lam m χ : Smooth) (hl : (lam : X → ℂ).HasTemperateGrowth)
    (hm : (m : X → ℂ).HasTemperateGrowth) (hc : HasCompactSupport (χ : X → ℂ))
    (hχ : EqOn (χ : X → ℂ) 1 B) (z : Fin 3 → ℂ) (u F H : Fin 3 → S)
    (hF : ∀ i x,x∈B → F i x=Complex.exp (phaseCLM z x)*u i x)
    (hH : ∀ i,tsupport (H i : X → ℂ)⊆K)
    (hsol : ∀ i,EqOn (physical 0 lam m (F+H) i : X → ℂ) 0 B) :
    ∃ v : Fin 3 → S,
      (∀ i,tsupport (v i-u i : S)⊆K) ∧
      (∀ i,EqOn (physical z lam m v i : X → ℂ) 0 B) ∧
      (∀ i x,x∈B → Complex.exp (phaseCLM z x)*v i x=F i x+H i x) := by
  let w : Fin 3 → S := fun i => expCut χ hc (-z) (H i)
  let v := u+w
  have he : ∀ i x,x∈B → Complex.exp (phaseCLM z x)*v i x=F i x+H i x := by
    intro i x hx
    change Complex.exp (phaseCLM z x)*(u i x+w i x)=F i x+H i x
    dsimp [w]
    rw [expCut_apply,hχ hx,Pi.one_apply,one_mul,phaseCLM_neg]
    change Complex.exp (phaseCLM z x)*(u i x+Complex.exp (-(phaseCLM z x))*H i x)=F i x+H i x
    rw [mul_add,← mul_assoc,← Complex.exp_add,add_neg_cancel,Complex.exp_zero,one_mul,hF i x hx]
  have hex : ∀ i,EqOn (expCut χ hc z (v i) : X → ℂ) ((F+H) i) B := by
    intro i x hx
    rw [expCut_apply,hχ hx,Pi.one_apply,one_mul]
    exact he i x hx
  refine ⟨v,fun i => ?_,fun i x hx => ?_,he⟩
  · have hv : v i-u i=w i := by dsimp [v]; simp only [add_sub_cancel_left]
    rw [hv]
    exact (expCut_support χ hc (-z) (H i)).trans (hH i)
  · have hp := physical_eqOn_of_eqOn hB 0 lam m hl hm
      (fun j => expCut χ hc z (v j)) (F+H) hex i hx
    rw [expCut_physical hB lam m χ hl hm hc hχ z v i hx] at hp
    have hz : Complex.exp (phaseCLM z x)*physical z lam m v i x=0 := hp.trans (hsol i hx)
    exact (mul_eq_zero.mp hz).resolve_left (Complex.exp_ne_zero _)

/-- The actual shifted divergence of the compact physical difference also has
compact support; no separate scalar field is introduced. -/
lemma divShift_supported {K : Set X} (hK : IsClosed K) (z : Fin 3 → ℂ)
    (u : Fin 3 → S) (hu : ∀ i,tsupport (u i : X → ℂ)⊆K) :
    tsupport (divShift z u : X → ℂ)⊆K := by
  apply closure_minimal _ hK
  intro x hx
  by_contra hnot
  apply hx
  have hh (i : Fin 3) : u i x=0 := image_eq_zero_of_notMem_tsupport (fun ht => hnot (hu i ht))
  have hd (i : Fin 3) : ElasticitySchwartzCarleman.d (e i) (u i) x=0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro ht
    exact hnot (hu i ((tsupport_fderiv_apply_subset ℝ (e i)) ht))
  simp only [divShift,sum_apply,shiftD_apply,add_apply,
    smul_apply,hh,smul_zero,add_zero]
  change (∑ i, ElasticitySchwartzCarleman.d (e i) (u i) x)=0
  simp only [hd,Finset.sum_const_zero]
end ElasticityCGO

end
end
section
noncomputable section
open Set
open scoped BigOperators SchwartzMap
namespace ElasticityPhysicalEstimate
open ElasticityBessel ElasticitySchwartzCarleman ElasticityNegativeOrder ElasticityPhysicalAlgebra
open ElasticityAugmented (coord coeffA coeffV)
open ElasticityCoeffBounds

/-- The scalar component is the actual shifted divergence. -/
def physicalAug (z : Fin 3 → ℂ) (u : Fin 3 → S) : Fin 4 → S :=
  Fin.cons (divShift z u) u

lemma physicalAug_sub (z : Fin 3 → ℂ) (u v : Fin 3 → S) :
    physicalAug z (v-u)=physicalAug z v-physicalAug z u := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [physicalAug,Fin.cons_zero,Pi.sub_apply,divShift,map_sub,Finset.sum_sub_distrib]
  · rfl

lemma physicalAug_supported {K : Set X} (hK : IsClosed K) (z : Fin 3 → ℂ)
    (u : Fin 3 → S) (hu : ∀ i,tsupport (u i : X → ℂ)⊆K) :
    ∀ i,tsupport (physicalAug z u i : X → ℂ)⊆K := by
  intro i
  refine Fin.cases ?_ (fun i => hu i) i
  exact ElasticityCGO.divShift_supported hK z u hu

theorem physical_compact_comparison {B K : Set X} (hB : IsOpen B)
    (hK : IsClosed K) (hKB : K⊆B) (R : ℝ) (hR : 1≤R)
    (hKR : K⊆Metric.closedBall 0 R) (α β : X) (hα : α≠0)
    (lam m : Fin 2 → Smooth)
    (hl : ∀ q,ExteriorConstant (lam q)) (hm : ∀ q,ExteriorConstant (m q))
    (hm0 : ∀ q x,(m q : X → ℂ) x≠0)
    (he0 : ∀ q x,((lam q+m q+m q : Smooth) : X → ℂ) x≠0)
    (hel : EqOn (lam 0 : X → ℂ) (lam 1) Kᶜ)
    (hem : EqOn (m 0 : X → ℂ) (m 1) Kᶜ) :
    ∃ C h₀ : ℝ,0<C ∧ 0<h₀ ∧ ∀ h : ℝ,0<h → h≤h₀ →
      ∀ u v : Fin 3 → S,
      (∀ i,tsupport ((v-u) i : X → ℂ)⊆K) →
      (∀ i,EqOn (physical (phase h α β) (lam 0) (m 0) u i : X → ℂ) 0 B) →
      (∀ i,EqOn (physical (phase h α β) (lam 1) (m 1) v i : X → ℂ) 0 B) →
      sobNorm h 1 (physicalAug (phase h α β) (v-u)) ≤
        C*sobNorm h 1 (physicalAug (phase h α β) u) := by
  let n := fun q => reciprocal (m q) (hm0 q)
  let o := fun q => reciprocal (lam q+m q+m q) (he0 q)
  have hn (q) : ExteriorConstant (n q) := (hm q).reciprocal (hm0 q)
  have ho (q) : ExteriorConstant (o q) := (((hl q).add (hm q)).add (hm q)).reciprocal (he0 q)
  have hni (q) : n q*m q=1 := reciprocal_mul _ _
  have hoi (q) : o q*(lam q+m q+m q)=1 := reciprocal_mul _ _
  have ha (q) := exterior_coeffA (hl q) (hm q) (hn q) (ho q)
  have hv (q) := exterior_coeffV (hl q) (hm q) (hn q) (ho q)
  have hc (q) := exterior_cPhys (hm q) (hn q)
  let a := fun q => aPhys (lam q) (m q) (n q) (o q)
  let w := fun q => vPhys (lam q) (m q) (n q) (o q)
  have hag (q k i j) : (a q k i j).HasTemperateGrowth := (ha q k i j).growth.neg
  have hwg (q i j) : (w q i j).HasTemperateGrowth := (hv q i j).growth.neg
  obtain ⟨A,hA,hba⟩ := ExteriorConstant.uniform_bound
    (fun t : Fin 2 × Fin 3 × Fin 4 × Fin 4 =>
      coeffA coord (lam t.1) (m t.1) (n t.1) (o t.1) t.2.1 t.2.2.1 t.2.2.2)
    (fun t => ha t.1 t.2.1 t.2.2.1 t.2.2.2)
  obtain ⟨V,hV,hbv⟩ := ExteriorConstant.uniform_bound
    (fun t : Fin 2 × Fin 4 × Fin 4 =>
      coeffV coord (lam t.1) (m t.1) (n t.1) (o t.1) t.2.1 t.2.2)
    (fun t => hv t.1 t.2.1 t.2.2)
  have hba' (q k i j x) : ‖a q k i j x‖≤A := by
    simpa only [a,aPhys,Pi.neg_apply,norm_neg] using hba (q,k,i,j) x
  have hbw' (q i j x) : ‖w q i j x‖≤V := by
    simpa only [w,vPhys,Pi.neg_apply,norm_neg] using hbv (q,i,j) x
  let Z := ∑ i,‖((α i : ℂ)+Complex.I*(β i : ℂ))‖
  have hZ : 0≤Z := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hz (i : Fin 3) : ‖((α i : ℂ)+Complex.I*(β i : ℂ))‖≤Z :=
    Finset.single_le_sum (fun j _ => norm_nonneg ((α j : ℂ)+Complex.I*(β j : ℂ))) (Finset.mem_univ i)
  obtain ⟨C,h₀,hC,hh₀,hest⟩ := compact_comparison_estimate R hR α β hα
    (a 0) (a 1) (w 0) (w 1) (hag 0) (hag 1) (hwg 0) (hwg 1)
    A V Z hA hV hZ (hba' 0) (hba' 1) (hbw' 0) (hbw' 1) hz
  obtain ⟨hea,hev⟩ := ElasticityAugmented.normalized_coefficients_eqOn hK.isOpen_compl
    (lam 0) (m 0) (n 0) (o 0) (lam 1) (m 1) (n 1) (o 1)
    (hni 0) (hni 1) (hoi 0) (hoi 1) hel hem
  refine ⟨C,h₀,hC,hh₀,fun h hh hsmall u v hs hu hv' => ?_⟩
  have hs' := physicalAug_supported hK (phase h α β) (v-u) hs
  have hlocal (q) (f : Fin 3 → S)
      (hf : ∀ i,EqOn (physical (phase h α β) (lam q) (m q) f i : X → ℂ) 0 B) :=
    physical_dirSystem_on hB h hh.ne' α β (lam q) (m q) (n q) (o q)
      (hni q) (hoi q) (hl q).growth (hm q).growth (hn q).growth (ho q).growth
      (fun k i j => (ha q k i j).growth) (fun i j => (hv q i j).growth)
      (fun i => (hc q i).growth) f hf
  rw [physicalAug_sub] at hs' ⊢
  refine hest h hh hsmall _ _ (fun i => ?_) ?_
  · intro x hx
    have ht := hKR (hs' i (subset_tsupport _ hx))
    simpa only [Metric.mem_closedBall,dist_zero_right] using ht
  · apply compact_forcing_identity hKB h α β (a 0) (a 1) (w 0) (w 1)
      (hag 0) (hag 1) (hwg 0) (hwg 1) _ _ _ _ hs' (hlocal 0 u hu) (hlocal 1 v hv')
    · intro k i j x hx
      exact congrArg Neg.neg (hea k i j hx)
    · intro i j x hx
      exact congrArg Neg.neg (hev i j hx)
end ElasticityPhysicalEstimate

end
end
section
noncomputable section
open Set MeasureTheory
namespace Elasticity
variable {Ω : Set X} {l₁ m₁ l₂ m₂ : X → ℝ}

lemma energy_coeff_congr_ae
    (hl : l₁ =ᵐ[volume.restrict Ω] l₂) (hm : m₁ =ᵐ[volume.restrict Ω] m₂) :
    energy Ω l₁ m₁=energy Ω l₂ m₂ := by
  funext u v
  apply integral_congr_ae
  filter_upwards [hl,hm] with x hxl hxm
  rw [hxl,hxm]

/-- The variational DN definition really depends only on the interior
coefficients, including its choice branch. No exterior identification is presumed. -/
theorem DN_coeff_congr_ae
    (hl : l₁ =ᵐ[volume.restrict Ω] l₂) (hm : m₁ =ᵐ[volume.restrict Ω] m₂) :
    DN Ω l₁ m₁=DN Ω l₂ m₂ := by
  have he := energy_coeff_congr_ae hl hm
  have hws : WeakSolution Ω l₁ m₁=WeakSolution Ω l₂ m₂ := by
    funext u
    apply propext
    unfold WeakSolution
    rw [he]
  have hsol : dirichletSolution Ω l₁ m₁=dirichletSolution Ω l₂ m₂ := by
    funext f
    unfold dirichletSolution
    rw [hws]
  change (fun (f g : BoundaryData Ω) => energy Ω l₁ m₁ (dirichletSolution Ω l₁ m₁ f) g.out) =
    (fun (f g : BoundaryData Ω) => energy Ω l₂ m₂ (dirichletSolution Ω l₂ m₂ f) g.out)
  rw [he,hsol]

theorem DN_coeff_congr (hΩ : MeasurableSet Ω) (hl : EqOn l₁ l₂ Ω) (hm : EqOn m₁ m₂ Ω) :
    DN Ω l₁ m₁=DN Ω l₂ m₂ := by
  apply DN_coeff_congr_ae
  · filter_upwards [ae_restrict_mem hΩ] with x hx
    exact hl hx
  · filter_upwards [ae_restrict_mem hΩ] with x hx
    exact hm hx
end Elasticity

end
end

end OAI
