import OAI.NumberTheory.DirichletL.Moments.ReflectedPairEnergy

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory
namespace SevenEighths.CenteredMomentReflectedUniformPair
open HeckeFamily FourierBridge EisensteinSchwartzPoisson
open CenteredMomentReflectedProfileMeasure CenteredMomentReflectedPairEnergy

def heightScale (A n : ℕ) (s t : ℝ) : ℝ := (1+s)^A/(1+‖t‖)^n

def normalizedReflected (V W : ℝ→ℂ) (A n : ℕ) (s t x : ℝ) : ℂ :=
  logWindow V x*((heightScale A n s t:ℝ):ℂ)*
    paperRadialFourier (CompletedHeight.normTwistedSource W t) (s*x)

def envelope (C : ℝ) (J : ℕ) (v : ℝ) : ℝ := C/(1+v^2)/(1+‖v‖)^J

lemma heightScale_pos (A n : ℕ) (s t : ℝ) (hs : 0<s) : 0<heightScale A n s t := by
  unfold heightScale
  positivity

lemma envelope_pos (C : ℝ) (hC : 0<C) (J : ℕ) (v : ℝ) : 0<envelope C J v := by
  unfold envelope
  positivity

lemma envelope_weight (C : ℝ) (J : ℕ) (v : ℝ) :
    envelope C J v*(1+‖v‖)^J=C/(1+v^2) := by
  unfold envelope
  field_simp

lemma envelope_integrable (C : ℝ) (J : ℕ) :
    Integrable (fun v : ℝ=>envelope C J v*(1+‖v‖)^J) := by
  simp_rw [envelope_weight,div_eq_mul_inv]
  exact integrable_inv_one_add_sq.const_mul C

lemma envelope_integral (C : ℝ) (J : ℕ) :
    (∫v : ℝ,envelope C J v*(1+‖v‖)^J)=C*Real.pi := by
  simp_rw [envelope_weight,div_eq_mul_inv]
  rw [integral_const_mul,integral_univ_inv_one_add_sq]

lemma normalized_density_bound (A n J : ℕ) (s t C : ℝ) (hs : 0<s)
    (b : 𝓢(ℝ,ℂ))
    (hp : ∀v : ℝ,(1+s)^A*(1+‖v‖)^(J+2)*‖b v‖≤C*(1+‖t‖)^n) :
    ∀v : ℝ,‖(((heightScale A n s t:ℝ):ℂ) • b) v‖≤envelope C J v := by
  intro v
  have ht : 0<(1+‖t‖)^n := by positivity
  have hv : 0<(1+‖v‖)^J := by positivity
  have hh : (1+‖v‖)^2*((1+‖v‖)^J*‖(((heightScale A n s t:ℝ):ℂ) • b) v‖)≤C := by
    rw [smul_apply,norm_smul,Complex.norm_real,
      Real.norm_of_nonneg (heightScale_pos A n s t hs).le]
    unfold heightScale
    have hh := (div_le_iff₀ ht).mpr (hp v)
    convert hh using 1 ; rw [pow_add] ; ring
  have hnorm : 0≤(1+‖v‖)^J*‖(((heightScale A n s t:ℝ):ℂ) • b) v‖ := by positivity
  have hb := CubicReflectionKernel.weighted_two_to_cauchy hnorm v hh
  apply (le_div_iff₀ hv).mpr
  simpa only [envelope,mul_comm] using hb

theorem actual_pair_uniform (V₁ V₂ : ℝ→ℂ) (M₁ M₂ a₁ b₁ a₂ b₂ : ℝ)
    (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hV₁ : ∀y,V₁ y≠0 → |y|≤M₁) (hV₂ : ∀y,V₂ y≠0 → |y|≤M₂)
    (ha₁ : 0<a₁) (ha₂ : 0<a₂) (A J₁ J₂ : ℕ) :
    ∃n₁ n₂ : ℕ,∀W₁ W₂ : ℝ→ℂ,
      Function.support W₁⊆Set.Icc a₁ b₁ → ContDiff ℝ ∞ W₁ →
      Function.support W₂⊆Set.Icc a₂ b₂ → ContDiff ℝ ∞ W₂ →
      ∃C : ℝ,0<C ∧ ∀{ι : Type} [Fintype ι],∀(χ ψ : ι→Character)(P : ι→ℂ)
        (s₁ s₂ t₁ t₂ X₁ X₂ : ι→ℝ),
        (∀i,0<s₁ i) → (∀i,0<s₂ i) → (∀i,0<X₁ i) → (∀i,0<X₂ i) →
      ∀E : ℝ,0≤E →
      (∀x y,(∑i,‖HeckeDyadic.polynomial (χ i) false (logWindow V₁) (X₁ i) 0 (2*Real.pi*x)*
        HeckeDyadic.polynomial (ψ i) false (logWindow V₂) (X₂ i) 0 (2*Real.pi*y)*P i‖^2)≤
          E*((1+‖x‖)^J₁)^2*((1+‖y‖)^J₂)^2) →
      (∑i,‖HeckeDyadic.polynomial (χ i) false (normalizedReflected V₁ W₁ A n₁ (s₁ i) (t₁ i)) (X₁ i) 0 0 *
        HeckeDyadic.polynomial (ψ i) false (normalizedReflected V₂ W₂ A n₂ (s₂ i) (t₂ i)) (X₂ i) 0 0 * P i‖^2)≤C*E := by
  obtain ⟨n₁,h₁⟩ := actual_profile_separation V₁ M₁ a₁ b₁ hM₁ hV₁ ha₁ A (J₁+2)
  obtain ⟨n₂,h₂⟩ := actual_profile_separation V₂ M₂ a₂ b₂ hM₂ hV₂ ha₂ A (J₂+2)
  refine ⟨n₁,n₂,?_⟩
  intro W₁ W₂ hs₁ hW₁ hs₂ hW₂
  obtain ⟨C₁,hC₁,hb₁⟩ := h₁ W₁ hs₁ hW₁
  obtain ⟨C₂,hC₂,hb₂⟩ := h₂ W₂ hs₂ hW₂
  refine ⟨(C₁*Real.pi)^2*(C₂*Real.pi)^2,by positivity,?_⟩
  intro ι _ χ ψ P s₁ s₂ t₁ t₂ X₁ X₂ hs₁ hs₂ hX₁ hX₂ E hE henergy
  choose d₁ hid₁ hi₁ hm₁ hp₁ using fun i=>hb₁ (t₁ i) (s₁ i) (hs₁ i)
  choose d₂ hid₂ hi₂ hm₂ hp₂ using fun i=>hb₂ (t₂ i) (s₂ i) (hs₂ i)
  let e₁ (i : ι) : ℂ := heightScale A n₁ (s₁ i) (t₁ i)
  let e₂ (i : ι) : ℂ := heightScale A n₂ (s₂ i) (t₂ i)
  let F₁ (i : ι) (x : ℝ) := e₁ i*paperRadialFourier (CompletedHeight.normTwistedSource W₁ (t₁ i)) x
  let F₂ (i : ι) (x : ℝ) := e₂ i*paperRadialFourier (CompletedHeight.normTwistedSource W₂ (t₂ i)) x
  have hsep₁ (i : ι) (y : ℝ) : V₁ y*F₁ i (s₁ i*Real.exp y)=
      ∫v : ℝ,(V₁ y*logPhase v y)*(e₁ i • d₁ i) v := by
    simp only [smul_apply,smul_eq_mul]
    have he : (fun v : ℝ=>(V₁ y*logPhase v y)*(e₁ i*d₁ i v))=
        (fun v=>e₁ i*((V₁ y*logPhase v y)*d₁ i v)) := by funext v;ring
    rw [he,integral_const_mul,←hid₁ i y]
    dsimp [F₁]
    ring
  have hsep₂ (i : ι) (y : ℝ) : V₂ y*F₂ i (s₂ i*Real.exp y)=
      ∫v : ℝ,(V₂ y*logPhase v y)*(e₂ i • d₂ i) v := by
    simp only [smul_apply,smul_eq_mul]
    have he : (fun v : ℝ=>(V₂ y*logPhase v y)*(e₂ i*d₂ i v))=
        (fun v=>e₂ i*((V₂ y*logPhase v y)*d₂ i v)) := by funext v;ring
    rw [he,integral_const_mul,←hid₂ i y]
    dsimp [F₂]
    ring
  have hh := paired_profile_energy χ ψ P V₁ V₂ M₁ M₂ hV₁ hV₂ F₁ F₂ s₁ s₂ X₁ X₂ hX₁ hX₂
    (fun i=>e₁ i • d₁ i) (fun i=>e₂ i • d₂ i) hsep₁ hsep₂
    (envelope C₁ J₁) (envelope C₂ J₂) (fun x=>(1+‖x‖)^J₁) (fun y=>(1+‖y‖)^J₂)
    (envelope_pos C₁ hC₁ J₁) (envelope_pos C₂ hC₂ J₂) (by intro x;positivity) (by intro y;positivity)
    (fun i=>normalized_density_bound A n₁ J₁ (s₁ i) (t₁ i) C₁ (hs₁ i) (d₁ i) (hp₁ i))
    (fun i=>normalized_density_bound A n₂ J₂ (s₂ i) (t₂ i) C₂ (hs₂ i) (d₂ i) (hp₂ i))
    (envelope_integrable C₁ J₁) (envelope_integrable C₂ J₂) E hE henergy
  rw [envelope_integral,envelope_integral] at hh
  have heq : E*(C₁*Real.pi)^2*(C₂*Real.pi)^2=((C₁*Real.pi)^2*(C₂*Real.pi)^2)*E := by ring
  rw [heq] at hh
  have hf₁ (i : ι) : normalizedReflected V₁ W₁ A n₁ (s₁ i) (t₁ i)=
      (fun x=>logWindow V₁ x*F₁ i (s₁ i*x)) := by
    funext x
    dsimp [normalizedReflected,F₁,e₁]
    ring
  have hf₂ (i : ι) : normalizedReflected V₂ W₂ A n₂ (s₂ i) (t₂ i)=
      (fun x=>logWindow V₂ x*F₂ i (s₂ i*x)) := by
    funext x
    dsimp [normalizedReflected,F₂,e₂]
    ring
  simp_rw [hf₁,hf₂]
  exact hh

end SevenEighths.CenteredMomentReflectedUniformPair

end

end OAI
