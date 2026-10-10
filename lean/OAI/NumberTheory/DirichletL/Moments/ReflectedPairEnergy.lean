import OAI.NumberTheory.DirichletL.Moments.ReflectedProfileMeasure

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory
namespace SevenEighths.CenteredMomentReflectedPairEnergy
open HeckeFamily FourierBridge CenteredMomentReflectedProfileMeasure
local notation "O" => HeckeFamily.O

lemma plain_frequency_control (V : ℝ→ℂ) (M X : ℝ) (hX : 0<X)
    (hV : ∀y,V y≠0 → |y|≤M) (η : Character) :
    Continuous (fun v : ℝ=>HeckeDyadic.polynomial η false (logWindow V) X 0 (2*Real.pi*v)) ∧
    ∃K : ℝ,∀v : ℝ,‖HeckeDyadic.polynomial η false (logWindow V) X 0 (2*Real.pi*v)‖≤K := by
  let S := HeckeInverseAmplification.scaleSupport (Real.log X) (Real.exp M)
  have hs : ∀I∈S,I≠0 := by
    intro I hI
    have hi := (ConcretePrimeRowBridge.mem_idealsUpTo.mp hI).1
    intro hz
    subst I
    simp at hi
  have hc : ∀I : Ideal O,I≠0 → logWindow V ((I.absNorm:ℝ)/X)≠0 → I∈S := by
    have hh := HeckeInverseAmplification.scaleSupport_cover (logWindow V)
      (Real.exp (-M)) (Real.exp M) (Real.log X) (Real.log X) (Real.exp_pos M).le
      (logWindow_support V M hV) le_rfl
    simpa only [Real.exp_log hX] using hh
  have he (v : ℝ) : HeckeDyadic.polynomial η false (logWindow V) X 0 (2*Real.pi*v)=
      (X:ℂ)^(-(1/2:ℂ))*∑I∈S,HeckeDyadic.coefficient η false I*
        logWindow V ((I.absNorm:ℝ)/X)*logPhase v (Real.log ((I.absNorm:ℝ)/X)) := by
    rw [HeckeDetectorDyadicBridge.polynomial_eq_finite η false _ X 0 (2*Real.pi*v) S hc]
    congr 1
    apply Finset.sum_congr rfl
    intro I hI
    have hm := HeckeDetectorDyadicBridge.norm_phase (I.absNorm:ℝ) X
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hs I hI))) hX 0 v
    simp only [neg_zero,Complex.cpow_zero,one_mul,Complex.zero_re,Complex.zero_im,sub_zero] at hm
    rw [hm]
  constructor
  · simp_rw [he]
    exact continuous_const.mul (continuous_finsetSum S (fun I _=>
      continuous_const.mul (logPhase_continuous_left _)))
  · refine ⟨‖(X:ℂ)^(-(1/2:ℂ))‖*∑I∈S,
      ‖HeckeDyadic.coefficient η false I*logWindow V ((I.absNorm:ℝ)/X)‖,?_⟩
    intro v
    rw [he,norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro I hI
    rw [norm_mul,logPhase_norm,mul_one]

lemma plain_density_integrable (V : ℝ→ℂ) (M X : ℝ) (hX : 0<X)
    (hV : ∀y,V y≠0 → |y|≤M) (η : Character) (density : 𝓢(ℝ,ℂ)) :
    Integrable (fun v : ℝ=>density v*HeckeDyadic.polynomial η false (logWindow V) X 0 (2*Real.pi*v)) := by
  obtain ⟨hc,K,hK⟩ := plain_frequency_control V M X hX hV η
  exact (density.integrable (μ:=volume)).mul_bdd hc.aestronglyMeasurable
    (Filter.Eventually.of_forall hK)

theorem paired_profile_energy {ι : Type*} [Fintype ι]
    (χ ψ : ι→Character) (P : ι→ℂ) (V₁ V₂ : ℝ→ℂ) (M₁ M₂ : ℝ)
    (hV₁ : ∀y,V₁ y≠0 → |y|≤M₁) (hV₂ : ∀y,V₂ y≠0 → |y|≤M₂)
    (F₁ F₂ : ι→ℝ→ℂ) (s₁ s₂ X₁ X₂ : ι→ℝ)
    (hX₁ : ∀i,0<X₁ i) (hX₂ : ∀i,0<X₂ i)
    (b₁ b₂ : ι→𝓢(ℝ,ℂ))
    (hsep₁ : ∀i y,V₁ y*F₁ i (s₁ i*Real.exp y)=
      ∫v : ℝ,(V₁ y*logPhase v y)*b₁ i v)
    (hsep₂ : ∀i y,V₂ y*F₂ i (s₂ i*Real.exp y)=
      ∫v : ℝ,(V₂ y*logPhase v y)*b₂ i v)
    (rho₁ rho₂ w₁ w₂ : ℝ→ℝ)
    (hr₁ : ∀v,0<rho₁ v) (hr₂ : ∀v,0<rho₂ v)
    (hw₁ : ∀v,0<w₁ v) (hw₂ : ∀v,0<w₂ v)
    (hp₁ : ∀i v,‖b₁ i v‖≤rho₁ v) (hp₂ : ∀i v,‖b₂ i v‖≤rho₂ v)
    (hm₁ : Integrable (fun x=>rho₁ x*w₁ x))
    (hm₂ : Integrable (fun y=>rho₂ y*w₂ y))
    (E : ℝ) (hE : 0≤E)
    (henergy : ∀x y,(∑i,‖HeckeDyadic.polynomial (χ i) false (logWindow V₁) (X₁ i) 0 (2*Real.pi*x)*
      HeckeDyadic.polynomial (ψ i) false (logWindow V₂) (X₂ i) 0 (2*Real.pi*y)*P i‖^2)≤
        E*(w₁ x)^2*(w₂ y)^2) :
    (∑i,‖HeckeDyadic.polynomial (χ i) false (fun x=>logWindow V₁ x*F₁ i (s₁ i*x)) (X₁ i) 0 0 *
      HeckeDyadic.polynomial (ψ i) false (fun x=>logWindow V₂ x*F₂ i (s₂ i*x)) (X₂ i) 0 0 * P i‖^2)≤
      E*(∫x : ℝ,rho₁ x*w₁ x)^2*(∫y : ℝ,rho₂ y*w₂ y)^2 := by
  let T₁ (i : ι) (x : ℝ) := HeckeDyadic.polynomial (χ i) false (logWindow V₁) (X₁ i) 0 (2*Real.pi*x)
  let T₂ (i : ι) (y : ℝ) := HeckeDyadic.polynomial (ψ i) false (logWindow V₂) (X₂ i) 0 (2*Real.pi*y)
  let φ (i : ι) (x y : ℝ) := T₁ i x*T₂ i y*P i
  have hi₂ (i : ι) (x : ℝ) : Integrable (fun y=>b₂ i y*φ i x y) := by
    have hi := (plain_density_integrable V₂ M₂ (X₂ i) (hX₂ i) hV₂ (ψ i) (b₂ i)).const_mul (T₁ i x*P i)
    apply hi.congr
    filter_upwards [] with y
    dsimp [φ,T₂]
    ring
  have he₂ (i : ι) (x : ℝ) : (∫y : ℝ,b₂ i y*φ i x y)=
      T₁ i x*(∫y : ℝ,b₂ i y*T₂ i y)*P i := by
    rw [←integral_const_mul,←integral_mul_const]
    apply integral_congr_ae
    filter_upwards [] with y
    dsimp [φ]
    ring
  have hi₁ (i : ι) : Integrable (fun x=>b₁ i x*(∫y : ℝ,b₂ i y*φ i x y)) := by
    simp_rw [he₂]
    have hi := (plain_density_integrable V₁ M₁ (X₁ i) (hX₁ i) hV₁ (χ i) (b₁ i)).mul_const
      ((∫y : ℝ,b₂ i y*T₂ i y)*P i)
    apply hi.congr
    filter_upwards [] with x
    dsimp [T₁]
    ring
  have hh := row_density_energy_two (fun i=>(b₁ i:ℝ→ℂ)) (fun i=>(b₂ i:ℝ→ℂ)) φ
    rho₁ rho₂ w₁ w₂ hr₁ hr₂ hw₁ hw₂ hp₁ hp₂ hi₁ hi₂ hm₁ hm₂ E hE henergy
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i _
  rw [plain_annular_separation V₁ (F₁ i) M₁ (s₁ i) (X₁ i) (hX₁ i) hV₁ (b₁ i) (hsep₁ i) (χ i),
      plain_annular_separation V₂ (F₂ i) M₂ (s₂ i) (X₂ i) (hX₂ i) hV₂ (b₂ i) (hsep₂ i) (ψ i)]
  simp_rw [he₂]
  congr 1
  rw [←integral_mul_const,←integral_mul_const]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  dsimp [T₁,T₂]
  ring

end SevenEighths.CenteredMomentReflectedPairEnergy

end

end OAI
