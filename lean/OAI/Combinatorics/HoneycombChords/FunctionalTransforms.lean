import OAI.Combinatorics.HoneycombChords.ControlledTransforms
import OAI.Combinatorics.HoneycombChords.EntireCosine

namespace OAI

/-! Integral transforms and endpoint constraints for the finite strip functional.

The development follows OpenAI, *Uniform marked-polygon estimates and sharp finite bridge moments*
(2026), Sections 6 and 7. -/

section


namespace CriticalHoneycomb.FiniteFunctional
open Real MeasureTheory Filter Topology
open Analytic

def RepresentsDensity (F f : ℝ → ℂ) : Prop := ∀ z, 0 < z → F (z^2) = f z

lemma lift_zDensity {N : ℕ} {f : ℝ → ℂ} (hf : f ∈ zDensity angle N) :
    ∃ F ∈ admissibleDensity N, RepresentsDensity F f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    rcases hf with ((⟨j,rfl⟩ | ⟨j,rfl⟩) | rfl)
    · refine ⟨(fun x : ℝ => (x:ℂ)^j.val),?_,?_⟩
      · exact Submodule.mem_sup_left (Submodule.subset_span (Or.inl ⟨j,rfl⟩))
      · intro z hz
        simp only [zMonomial,Complex.ofReal_pow]
    · refine ⟨(fun x : ℝ => iteratedDeriv j.val (fun t : ℝ => C t x) angle),?_,?_⟩
      · exact Submodule.mem_sup_left (Submodule.subset_span (Or.inr ⟨j,rfl⟩))
      · intro z hz
        exact C_sq_jet j.val angle hz.le
    · refine ⟨g,Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton g)),?_⟩
      intro z hz
      exact g_sq hz
  | zero =>
    refine ⟨0,(admissibleDensity N).zero_mem,?_⟩
    intro z hz
    rfl
  | add f g hf hg hfi hgi =>
    obtain ⟨F,hF,hfF⟩ := hfi
    obtain ⟨G,hG,hgG⟩ := hgi
    refine ⟨F+G,(admissibleDensity N).add_mem hF hG,?_⟩
    intro z hz
    exact congrArg₂ (·+·) (hfF z hz) (hgG z hz)
  | smul a f hf hfi =>
    obtain ⟨F,hF,hfF⟩ := hfi
    refine ⟨a • F,(admissibleDensity N).smul_mem a hF,?_⟩
    intro z hz
    exact congrArg (a • ·) (hfF z hz)

lemma angle_identity : 4*angle = Real.pi/2 := by unfold angle; ring
lemma angle_abs : |angle| = angle := abs_of_pos angle_pos
lemma angle_lt_pi_half : angle < Real.pi/2 := by unfold angle; linarith [Real.pi_pos]

lemma density_transform_surjective (N : ℕ) (P : Polynomial ℂ) (hP : P.natDegree < 2*N+1) :
    ∃ (F f : ℝ → ℂ), F ∈ admissibleDensity N ∧ f ∈ zDensity angle N ∧ RepresentsDensity F f ∧
      ∀ u : ℝ, |u|+angle < Real.pi/2 →
        zTransform f u = P.eval (Real.cos (2*u):ℂ) /
          interpolationDenominator N (Real.cos (2*u):ℂ) := by
  obtain ⟨f,hf,hT⟩ := zTransform_surjective angle_pos angle_lt_pi_half N P hP
  obtain ⟨F,hF,hrep⟩ := lift_zDensity hf
  refine ⟨F,f,hF,hf,hrep,?_⟩
  intro u hu
  exact hT ⟨u,by simpa only [angle_abs] using hu⟩

lemma pairing_eq_zIntegral {F f : ℝ → ℂ} (hrep : RepresentsDensity F f) (H : ℝ → ℂ) :
    pairing H F = ∫ z in Set.Ioi (0:ℝ),
      H (z^2) * f z * (z * zD angle z / (Real.sinh (Real.pi*z/2):ℂ)) := by
  unfold pairing
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  rw [hrep z hz,D_sq hz.le]
  simp only [zD]
  rw [show 4*angle*z = Real.pi*z/2 by rw [angle_identity]; ring]

lemma value_C_eq_fusion {F f : ℝ → ℂ} (hrep : RepresentsDensity F f) (ρ : ℂ) (u : ℝ) :
    value ρ F (C u) = integralFusion angle ρ f u := by
  rw [value,C_neg_four,C_zero,mul_one,pairing_eq_zIntegral hrep]
  unfold integralFusion aStar zTransform
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  rw [C_sq _ hz.le]
  dsimp [zKernel]
  ring

lemma C_parameter_zero (x : ℝ) : C 0 x = 1 := by simp [C]
lemma D_zero : D 0 = 1 := by norm_num [D,C_zero]
lemma D_neg_four : D (-4) = aStar := by unfold D aStar; rw [C_neg_four]
lemma aStar_ne_zero : aStar ≠ 0 := by
  unfold aStar angle
  rw [show 2*(Real.pi/8) = Real.pi/4 by ring,Real.cos_pi_div_four]
  have h : 1 < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),Real.sqrt_nonneg (2:ℝ)]
  have hr : 2*(Real.sqrt 2/2)-1 ≠ 0 := by linarith
  exact_mod_cast hr

lemma value_div_D_eq_interpolant {F f : ℝ → ℂ} (hrep : RepresentsDensity F f) (ρ : ℂ) (u : ℝ) :
    value ρ F (fun x => C u x / D x) = integralInterpolant ρ f u := by
  rw [value,D_neg_four,D_zero,C_zero,C_neg_four,div_one,mul_one,pairing_eq_zIntegral hrep]
  have ha := aStar_ne_zero
  have hdisc : 4*aStar*((Real.cos (2*u):ℂ)/aStar) = 4*(Real.cos (2*u):ℂ) := by field_simp
  rw [hdisc]
  unfold integralInterpolant zTransform
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  have hd := D_sq_ne_zero hz.le
  rw [C_sq _ hz.le]
  change (Real.cosh (u*z):ℂ)/D (z^2) * f z *
    ((z:ℂ)*zD angle z/(Real.sinh (Real.pi*z/2):ℂ)) = _
  have he : D (z^2) = zD angle z := D_sq hz.le
  rw [← he]
  dsimp [zKernel]
  field_simp

lemma value_inv_D_eq_interpolant {F f : ℝ → ℂ} (hrep : RepresentsDensity F f) (ρ : ℂ) :
    value ρ F (fun x => (D x)⁻¹) = integralInterpolant ρ f 0 := by
  convert value_div_D_eq_interpolant hrep ρ 0 using 1
  congr 1
  ext x
  rw [C_parameter_zero,one_div]

end CriticalHoneycomb.FiniteFunctional

end


section


namespace CriticalHoneycomb.FiniteFunctional
open Real Filter Topology
open Analytic

lemma iteratedDeriv_complex_ofReal {f : ℝ → ℝ} (hf : ContDiff ℝ ⊤ f) (j : ℕ) (u : ℝ) :
    iteratedDeriv j (fun t => (f t : ℂ)) u = (iteratedDeriv j f u : ℝ) := by
  induction j generalizing u with
  | zero => rfl
  | succ j ih =>
    rw [iteratedDeriv_succ,show iteratedDeriv j (fun t => (f t : ℂ)) =
      (fun t => ((iteratedDeriv j f t : ℝ) : ℂ)) from funext ih]
    simpa only [iteratedDeriv_succ] using
      (((hf.differentiable_iteratedDeriv j (by simp)) u).hasDerivAt.ofReal_comp).deriv

lemma C_even_jet_zero (j : ℕ) (x : ℝ) :
    iteratedDeriv (2*j) (fun t => C t x) 0 = (x:ℂ)^j := by
  by_cases hx : 0 ≤ x
  · have hs := Real.sq_sqrt hx
    rw [← hs,C_sq_jet _ _ (Real.sqrt_nonneg x)]
    simp only [zero_mul,hypJet_odd,Real.cosh_zero,mul_one,pow_mul,Complex.ofReal_pow]
  · have he (t : ℝ) : C t x = (Real.cos (Real.sqrt (-x)*t):ℂ) := by
      simp only [C,hx,ite_false,mul_comm]
    rw [show (fun t => C t x) = (fun t => (Real.cos (Real.sqrt (-x)*t):ℂ)) from funext he]
    rw [iteratedDeriv_complex_ofReal (by fun_prop)]
    rw [iteratedDeriv_comp_const_mul (n := 2*j) (show ContDiff ℝ (2*j) Real.cos by fun_prop)]
    rw [Real.iteratedDeriv_even_cos]
    simp only [mul_zero,Pi.mul_apply,Pi.pow_apply,Pi.neg_apply,Pi.one_apply,Real.cos_zero,mul_one]
    have hsq := Real.sq_sqrt (by linarith : 0 ≤ -x)
    rw [pow_mul,hsq]
    push_cast
    rw [← mul_pow]
    congr 1
    ring

lemma C_jet_hasDerivAt (j : ℕ) (x u : ℝ) :
    HasDerivAt (iteratedDeriv j (fun t => C t x))
      (iteratedDeriv (j+1) (fun t => C t x) u) u := by
  rw [iteratedDeriv_succ]
  exact ((C_contDiff x).differentiable_iteratedDeriv j (by simp)).differentiableAt.hasDerivAt

end CriticalHoneycomb.FiniteFunctional

end


section


namespace CriticalHoneycomb.FiniteFunctional
open Real Filter Topology MeasureTheory
open Analytic

noncomputable def pairingKernel (H F : ℝ → ℂ) (z : ℝ) : ℂ :=
  H (z^2)*F (z^2)*((z:ℂ)*D (z^2)/(Real.sinh (4*angle*z):ℂ))
def PairingIntegrable (H F : ℝ → ℂ) : Prop :=
  IntegrableOn (pairingKernel H F) (Set.Ioi 0)

lemma pairingKernel_jet_ae {F f : ℝ → ℂ} (hrep : RepresentsDensity F f) (j : ℕ) (u : ℝ) :
    pairingKernel (fun x => iteratedDeriv j (fun t => C t x) u) F =ᵐ[volume.restrict (Set.Ioi 0)]
      weightedJet (fun z => zD angle z*f z) j u := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  dsimp [pairingKernel]
  rw [hrep z hz,C_sq_jet j u hz.le,D_sq hz.le]
  rw [show 4*angle*z = Real.pi*z/2 by rw [angle_identity]; ring]
  dsimp [weightedJet,zD]
  ring

lemma pairingJet_integrable {F f : ℝ → ℂ} {N : ℕ} (hrep : RepresentsDensity F f)
    (hf : f ∈ zDensity angle N) (j : ℕ) (u : ℝ) (hu : 2*angle+|u| < Real.pi/2) :
    PairingIntegrable (fun x => iteratedDeriv j (fun t => C t x) u) F := by
  have hfc := (zDensity_controlled hf).mul_zD angle
  rw [angle_abs] at hfc
  apply (weightedJet_integrable (u := u) hfc (add_nonneg angle_pos.le angle_pos.le) (by linarith) j).congr
  exact (pairingKernel_jet_ae hrep j u).symm

noncomputable def functionalJet (ρ : ℂ) (f : ℝ → ℂ) (j : ℕ) (u : ℝ) : ℂ :=
  4*aStar*iteratedDeriv j (fun t => C t (-4)) u +
    ρ*iteratedDeriv j (fun t => C t 0) u +
    weightedIntegral (fun z => zD angle z*f z) j u

lemma functionalJet_zero (ρ : ℂ) (f : ℝ → ℂ) (u : ℝ) :
    functionalJet ρ f 0 u = integralFusion angle ρ f u := by
  simp only [functionalJet,iteratedDeriv_zero,C_neg_four,C_zero,mul_one,weightedIntegral_zero,
    integralFusion,aStar]

lemma functionalJet_hasDerivAt {f : ℝ → ℂ} {N : ℕ} (hf : f ∈ zDensity angle N)
    (ρ : ℂ) (j : ℕ) (u : ℝ) (hu : 2*angle+|u| < Real.pi/2) :
    HasDerivAt (functionalJet ρ f j) (functionalJet ρ f (j+1) u) u := by
  have hfc := (zDensity_controlled hf).mul_zD angle
  rw [angle_abs] at hfc
  exact (((C_jet_hasDerivAt j (-4) u).const_mul (4*aStar)).add
    ((C_jet_hasDerivAt j 0 u).const_mul ρ)).add
    (weightedIntegral_hasDerivAt (u := u) hfc (add_nonneg angle_pos.le angle_pos.le) (by linarith) j)

lemma iteratedDeriv_integralFusion {f : ℝ → ℂ} {N : ℕ} (hf : f ∈ zDensity angle N)
    (ρ : ℂ) (j : ℕ) (u : ℝ) (hu : 2*angle+|u| < Real.pi/2) :
    iteratedDeriv j (integralFusion angle ρ f) u = functionalJet ρ f j u := by
  induction j generalizing u with
  | zero => exact (functionalJet_zero ρ f u).symm
  | succ j ih =>
    have hn : ∀ᶠ t in 𝓝 u, 2*angle+|t| < Real.pi/2 :=
      (isOpen_lt (continuous_const.add continuous_abs) continuous_const).mem_nhds hu
    have he : iteratedDeriv j (integralFusion angle ρ f) =ᶠ[𝓝 u] functionalJet ρ f j :=
      hn.mono (fun t ht => ih t ht)
    rw [iteratedDeriv_succ,he.deriv_eq]
    exact (functionalJet_hasDerivAt hf ρ j u hu).deriv

lemma value_jet_eq {F f : ℝ → ℂ} (hrep : RepresentsDensity F f) (ρ : ℂ) (j : ℕ) (u : ℝ) :
    value ρ F (fun x => iteratedDeriv j (fun t => C t x) u) = functionalJet ρ f j u := by
  unfold value functionalJet
  congr 1
  exact integral_congr_ae (pairingKernel_jet_ae hrep j u)

lemma pairingKernel_add (H K F : ℝ → ℂ) :
    pairingKernel (H+K) F = pairingKernel H F + pairingKernel K F := by
  ext z
  simp only [pairingKernel,Pi.add_apply]
  ring
lemma pairingKernel_smul (a : ℂ) (H F : ℝ → ℂ) :
    pairingKernel (a • H) F = a • pairingKernel H F := by
  ext z
  simp only [pairingKernel,Pi.smul_apply,smul_eq_mul]
  ring
lemma pairingKernel_zero (F : ℝ → ℂ) : pairingKernel 0 F = 0 := by
  ext z; simp [pairingKernel]

lemma PairingIntegrable.add {H K F : ℝ → ℂ} (hH : PairingIntegrable H F)
    (hK : PairingIntegrable K F) : PairingIntegrable (H+K) F := by
  unfold PairingIntegrable
  rw [pairingKernel_add]
  exact Integrable.add hH hK
lemma PairingIntegrable.smul {H F : ℝ → ℂ} (hH : PairingIntegrable H F) (a : ℂ) :
    PairingIntegrable (a • H) F := by
  unfold PairingIntegrable
  rw [pairingKernel_smul]
  exact Integrable.const_mul hH a
lemma PairingIntegrable.zero (F : ℝ → ℂ) : PairingIntegrable 0 F := by
  unfold PairingIntegrable
  rw [pairingKernel_zero]
  exact integrableOn_zero

lemma value_add {H K F : ℝ → ℂ} (hH : PairingIntegrable H F)
    (hK : PairingIntegrable K F) (ρ : ℂ) :
    value ρ F (H+K) = value ρ F H + value ρ F K := by
  have he : pairing (H+K) F = pairing H F + pairing K F := by
    change (∫ z in Set.Ioi (0:ℝ), pairingKernel (H+K) F z) = _
    rw [pairingKernel_add]
    exact integral_add hH hK
  simp only [value,Pi.add_apply,he]
  ring
lemma value_smul (H F : ℝ → ℂ) (ρ a : ℂ) : value ρ F (a • H) = a * value ρ F H := by
  have he : pairing (a • H) F = a * pairing H F := by
    change (∫ z in Set.Ioi (0:ℝ), pairingKernel (a • H) F z) = _
    rw [pairingKernel_smul]
    exact integral_const_mul a _
  simp only [value,Pi.smul_apply,smul_eq_mul,he]
  ring
lemma value_zero (F : ℝ → ℂ) (ρ : ℂ) : value ρ F 0 = 0 := by
  simp [value,pairing]

lemma M_integrable_and_annihilated {N : ℕ} {F f : ℝ → ℂ} (hrep : RepresentsDensity F f)
    (hf : f ∈ zDensity angle N) (ρ : ℂ)
    (hzero : ∀ j < 2*N, iteratedDeriv j (integralFusion angle ρ f) 0 = 0)
    (hangle : ∀ j < N, iteratedDeriv j (integralFusion angle ρ f) angle = 0) :
    ∀ H ∈ M N, PairingIntegrable H F ∧ value ρ F H = 0 := by
  have hu0 : 2*angle+|(0:ℝ)| < Real.pi/2 := by
    rw [abs_zero]; unfold angle; linarith [Real.pi_pos]
  have huL : 2*angle+|angle| < Real.pi/2 := by
    rw [angle_abs]; unfold angle; linarith [Real.pi_pos]
  intro H hH
  induction hH using Submodule.span_induction with
  | mem H hH =>
    rcases hH with (⟨j,rfl⟩ | ⟨j,rfl⟩)
    · have he : (fun x : ℝ => (x:ℂ)^j.val) =
        (fun x => iteratedDeriv (2*j.val) (fun t => C t x) 0) := funext (fun x => (C_even_jet_zero j.val x).symm)
      change PairingIntegrable (fun x : ℝ => (x:ℂ)^j.val) F ∧ value ρ F (fun x : ℝ => (x:ℂ)^j.val) = 0
      rw [he]
      refine ⟨pairingJet_integrable hrep hf _ _ hu0,?_⟩
      rw [value_jet_eq hrep,← iteratedDeriv_integralFusion hf ρ _ _ hu0]
      exact hzero _ (by have := j.isLt; omega)
    · refine ⟨pairingJet_integrable hrep hf _ _ huL,?_⟩
      rw [value_jet_eq hrep,← iteratedDeriv_integralFusion hf ρ _ _ huL]
      exact hangle _ j.isLt
  | zero => exact ⟨PairingIntegrable.zero F,value_zero F ρ⟩
  | add H K hH hK hiH hiK =>
    refine ⟨hiH.1.add hiK.1,?_⟩
    rw [value_add hiH.1 hiK.1,hiH.2,hiK.2,add_zero]
  | smul a H hH hiH =>
    refine ⟨hiH.1.smul a,?_⟩
    rw [value_smul,hiH.2,mul_zero]

end CriticalHoneycomb.FiniteFunctional

end


section


namespace CriticalHoneycomb.FiniteFunctional
open Real Filter Topology MeasureTheory
open Analytic

lemma integralInterpolant_even (ρ : ℂ) (f : ℝ → ℂ) (u : ℝ) :
    integralInterpolant ρ f (-u) = integralInterpolant ρ f u := by
  unfold integralInterpolant zTransform
  rw [mul_neg,Real.cos_neg]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ (fun z => by simp only [zKernel,neg_mul,Real.cosh_neg])

lemma pairingKernel_div_D_ae {F f : ℝ → ℂ} (hrep : RepresentsDensity F f) (u : ℝ) :
    pairingKernel (fun x => C u x/D x) F =ᵐ[volume.restrict (Set.Ioi 0)] weightedJet f 0 u := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  dsimp [pairingKernel]
  rw [hrep z hz,C_sq _ hz.le,weightedJet_zero]
  rw [show 4*angle*z = Real.pi*z/2 by rw [angle_identity]; ring]
  have hd := D_sq_ne_zero hz.le
  dsimp [zKernel]
  field_simp

lemma pairing_div_D_integrable {F f : ℝ → ℂ} {N : ℕ} (hrep : RepresentsDensity F f)
    (hf : f ∈ zDensity angle N) (u : ℝ) (hu : angle+|u| < Real.pi/2) :
    PairingIntegrable (fun x => C u x/D x) F := by
  have hfc := zDensity_controlled hf
  rw [angle_abs] at hfc
  apply (weightedJet_integrable hfc angle_pos.le hu 0).congr
  exact (pairingKernel_div_D_ae hrep u).symm

lemma value_sub {H K F : ℝ → ℂ} (hH : PairingIntegrable H F)
    (hK : PairingIntegrable K F) (ρ : ℂ) :
    value ρ F (H-K) = value ρ F H - value ρ F K := by
  rw [show H-K = H+(-1:ℂ) • K by ext x; simp [sub_eq_add_neg]]
  rw [value_add hH (hK.smul (-1)),value_smul]
  ring

lemma finite_endpoint_constraints {F f : ℝ → ℂ} {N : ℕ} (hrep : RepresentsDensity F f)
    (hf : f ∈ zDensity angle N) (ρ : ℂ)
    (h₃ : integralInterpolant ρ f (3*angle/2) = 0)
    (h₅ : integralInterpolant ρ f (5*angle/2) = 0) :
    value ρ F (C (angle/2)) = 0 ∧
    value ρ F (fun x => C (3*angle/2) x - C (angle/2) x/D x) = 0 := by
  have hc := zDensity_controlled hf
  have hp := angle_pos
  have hhalf : |angle/2| = angle/2 := abs_of_pos (by positivity)
  have hthree : |3*angle/2| = 3*angle/2 := abs_of_pos (by positivity)
  have hu₁ : |angle|+|angle/2|+|angle| < Real.pi/2 := by
    rw [angle_abs,hhalf]; unfold angle; linarith [Real.pi_pos]
  have hu₃ : |angle|+|3*angle/2|+|angle| < Real.pi/2 := by
    rw [angle_abs,hthree]; unfold angle; linarith [Real.pi_pos]
  have hf₁ := integralInterpolant_fusion hc (abs_nonneg _) angle (angle/2) ρ hu₁
  rw [show angle/2-angle = -(angle/2) by ring,
    show angle/2+angle = 3*angle/2 by ring,integralInterpolant_even,h₃] at hf₁
  have hf₃ := integralInterpolant_fusion hc (abs_nonneg _) angle (3*angle/2) ρ hu₃
  rw [show 3*angle/2-angle = angle/2 by ring,
    show 3*angle/2+angle = 5*angle/2 by ring,h₃,h₅] at hf₃
  constructor
  · rw [value_C_eq_fusion hrep]
    simpa using hf₁.symm
  · have hi₃ : PairingIntegrable (C (3*angle/2)) F := by
      convert pairingJet_integrable hrep hf 0 (3*angle/2) (by
        rw [hthree]; unfold angle; linarith [Real.pi_pos]) using 1
      ext x
      simp
    have hi₁ := pairing_div_D_integrable hrep hf (angle/2) (by
      rw [hhalf]; unfold angle; linarith [Real.pi_pos])
    change value ρ F (C (3*angle/2) - (fun x => C (angle/2) x/D x)) = 0
    rw [value_sub hi₃ hi₁,value_C_eq_fusion hrep,value_div_D_eq_interpolant hrep,← hf₃]
    ring

end CriticalHoneycomb.FiniteFunctional

end


section


namespace CriticalHoneycomb.FiniteFunctional
open Real Filter Topology MeasureTheory
open Analytic

lemma interpolant_eq_integralInterpolant {N : ℕ} {ρ : ℂ} {P : Polynomial ℂ} {f : ℝ → ℂ}
    (hT : ∀ u, |u|+angle < Real.pi/2 → zTransform f u =
      P.eval (Real.cos (2*u):ℂ)/interpolationDenominator N (Real.cos (2*u):ℂ))
    {u : ℝ} (hu : |u|+angle < Real.pi/2) :
    interpolant N ρ P u = integralInterpolant ρ f u := by
  unfold interpolant integralInterpolant
  rw [hT u hu]

lemma interpolant_fusion_eq_integral_eventually {N : ℕ} {ρ : ℂ} {P : Polynomial ℂ} {f : ℝ → ℂ}
    (hf : f ∈ zDensity angle N)
    (hT : ∀ u, |u|+angle < Real.pi/2 → zTransform f u =
      P.eval (Real.cos (2*u):ℂ)/interpolationDenominator N (Real.cos (2*u):ℂ))
    {u : ℝ} (hu : |u|+2*angle < Real.pi/2) :
    (fun t => interpolant N ρ P (t-angle)+interpolant N ρ P (t+angle)-interpolant N ρ P t)
      =ᶠ[𝓝 u] integralFusion angle ρ f := by
  have hn : ∀ᶠ t in 𝓝 u, |t|+2*angle < Real.pi/2 :=
    (isOpen_lt (continuous_abs.add continuous_const) continuous_const).mem_nhds hu
  filter_upwards [hn] with t ht
  have ht₁ : |t-angle|+angle < Real.pi/2 := by
    have hi := abs_sub t angle
    rw [angle_abs] at hi
    linarith
  have ht₂ : |t+angle|+angle < Real.pi/2 := by
    have hi := abs_add_le t angle
    rw [angle_abs] at hi
    linarith
  have ht₀ : |t|+angle < Real.pi/2 := by linarith [angle_pos]
  rw [interpolant_eq_integralInterpolant hT ht₁,interpolant_eq_integralInterpolant hT ht₂,
    interpolant_eq_integralInterpolant hT ht₀]
  apply integralInterpolant_fusion (zDensity_controlled hf) (abs_nonneg _)
  rw [angle_abs]
  linarith


end CriticalHoneycomb.FiniteFunctional

end

end OAI
