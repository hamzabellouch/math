import OAI.NumberTheory.DirichletL.Moments.OneReflectionEnergy
import OAI.NumberTheory.DirichletL.Moments.DetectorDictionaryUniformTests

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open MeasureTheory
namespace SevenEighths.CenteredMomentUniformReflectionProfile
open HeckeFamily FourierBridge EisensteinSchwartzPoisson
open CenteredMomentReflectedProfileMeasure CenteredMomentReflectedPairEnergy
open CenteredMomentReflectedUniformPair CenteredMomentOneReflectionEnergy

theorem source_separation (V : ℝ→ℂ) (M : ℝ) (hM : 0≤M)
    (hV : ∀y,V y≠0 → |y|≤M) (A J : ℕ) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀G : 𝓢(ℝ,ℂ),∀D : ℝ,0<D →
      H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G≤D → ∀s : ℝ,0<s →
      ∃density : 𝓢(ℝ,ℂ),
        (∀y : ℝ,V y*paperRadialFourier G (s*Real.exp y)=
          ∫v : ℝ,(V y*logPhase v y)*density v) ∧
        Integrable (fun v : ℝ=>(1+‖v‖)^J*‖density v‖) ∧
        (1+s)^A*(∫v : ℝ,(1+‖v‖)^J*‖density v‖)≤C*D ∧
        (∀v : ℝ,(1+s)^A*(1+‖v‖)^J*‖density v‖≤C*D) := by
  obtain ⟨C,hC,hsep⟩ := LocalLogFourier.coupled_positive_log_separation_linear_constant
    (fun _ : Unit=>V) (fun _=>1) (fun _=>M) (fun _=>hM) (fun _=>hV) A J
  obtain ⟨H,K,hK,hEuler⟩ := paperRadialFourier_euler_source_weighted_bound
    A (J+(volume : Measure ℝ).integrablePower)
  refine ⟨H,(C+1)*K,by positivity,?_⟩
  intro G D hD hGD s hs
  obtain ⟨density,hid,hi,hm,hp⟩ := hsep (paperRadialFourier G)
    (paperRadialFourier_contDiffOn G) (K*D) (by positivity)
    (fun j hj x hx=>(hEuler G j hj x hx.le).trans
      (mul_le_mul_of_nonneg_left hGD hK.le)) s hs
  have hconst : C*(K*D)≤((C+1)*K)*D := by nlinarith [mul_pos hK hD]
  exact ⟨density,(fun y=>by simpa using hid (fun _ : Unit=>y)),hi,
    hm.trans hconst,fun v=>(hp v).trans hconst⟩

theorem actual_one_uniform (V : ℝ→ℂ) (M : ℝ) (hM : 0≤M)
    (hV : ∀y,V y≠0 → |y|≤M) (A J : ℕ) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀{ι : Type} [Fintype ι],
      ∀(G : ι→𝓢(ℝ,ℂ))(χ : ι→Character)(P : ι→ℂ)(s X : ι→ℝ),
      (∀i,0<s i) → (∀i,0<X i) → ∀D E : ℝ,0<D → 0≤E →
      (∀i,H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i)≤D) →
      (∀v,(∑i,‖HeckeDyadic.polynomial (χ i) false (logWindow V) (X i) 0 (2*Real.pi*v)*P i‖^2)
        ≤E*((1+‖v‖)^J)^2) →
      (∑i,‖HeckeDyadic.polynomial (χ i) false
        (fun x=>logWindow V x*((1+s i)^A:ℂ)*paperRadialFourier (G i) (s i*x))
          (X i) 0 0*P i‖^2)≤C*D^2*E := by
  obtain ⟨H,K,hK,hb⟩ := source_separation V M hM hV A (J+2)
  refine ⟨H,(K*Real.pi)^2,by positivity,?_⟩
  intro ι _ G χ P s X hs hX D E hD hE hGD henergy
  choose d hid hi hm hp using fun i=>hb (G i) D hD (hGD i) (s i) (hs i)
  let e (i : ι) : ℂ := (1+s i)^A
  let F (i : ι) (x : ℝ) := e i*paperRadialFourier (G i) x
  let φ (i : ι) (v : ℝ) := HeckeDyadic.polynomial (χ i) false (logWindow V) (X i) 0 (2*Real.pi*v)*P i
  have hsep (i : ι) (y : ℝ) : V y*F i (s i*Real.exp y)=
      ∫v : ℝ,(V y*logPhase v y)*(e i • d i) v := by
    simp only [smul_apply,smul_eq_mul]
    have he : (fun v : ℝ=>(V y*logPhase v y)*(e i*d i v))=
        (fun v=>e i*((V y*logPhase v y)*d i v)) := by funext v;ring
    rw [he,integral_const_mul,←hid i y]
    dsimp [F]
    ring
  have hsource (i : ι) : HeckeDyadic.polynomial (χ i) false
      (fun x=>logWindow V x*((1+s i)^A:ℂ)*paperRadialFourier (G i) (s i*x))
        (X i) 0 0*P i=∫v : ℝ,(e i • d i) v*φ i v := by
    have hf : (fun x=>logWindow V x*((1+s i)^A:ℂ)*paperRadialFourier (G i) (s i*x))=
        (fun x=>logWindow V x*F i (s i*x)) := by funext x;dsimp [F,e];ring
    rw [hf,plain_annular_separation V (F i) M (s i) (X i) (hX i) hV (e i • d i) (hsep i),
      ←integral_mul_const]
    apply integral_congr_ae
    filter_upwards [] with v
    dsimp [φ]
    ring
  have hint (i : ι) : Integrable (fun v : ℝ=>(e i • d i) v*φ i v) := by
    have hh := (plain_density_integrable V M (X i) (hX i) hV (χ i) (e i • d i)).mul_const (P i)
    apply hh.congr
    filter_upwards [] with v
    dsimp [φ]
    ring
  have hpoint (i : ι) : ∀v,‖(e i • d i) v‖≤envelope (K*D) J v := by
    have hh := normalized_density_bound A 0 J (s i) 0 (K*D) (hs i) (d i)
      (by simpa using hp i)
    simpa [heightScale,e] using hh
  have hh := row_density_energy (fun i=>(e i • d i:𝓢(ℝ,ℂ))) φ (envelope (K*D) J)
    (fun v=>(1+‖v‖)^J) (envelope_pos (K*D) (mul_pos hK hD) J)
    (by intro v;positivity) hpoint hint (envelope_integrable (K*D) J) E hE henergy
  rw [envelope_integral] at hh
  simp_rw [←hsource] at hh
  convert hh using 1
  ring

lemma inverse_annular_frequency (χ : Character) (V : ℝ→ℂ)
    (hreal : ∀y,conj (V y)=V y) (X v : ℝ) (hX : 0<X) :
    HeckeDyadic.polynomial χ.inverse false (logWindow V) X 0 (2*Real.pi*v)=
      conj (HeckeDyadic.polynomial χ false (logWindow V) X 0 (-2*Real.pi*v)) := by
  have hr (x : ℝ) : conj (logWindow V x)=logWindow V x := by
    unfold logWindow
    split_ifs <;> simp [hreal]
  have ht : (fun x=>conj (CompletedHeight.normTwistedSource (logWindow V) v x))=
      CompletedHeight.normTwistedSource (logWindow V) (-v) := by
    funext x
    simp only [CompletedHeight.normTwistedSource,map_mul,hr]
    exact congrArg (fun z=>z*logWindow V x) (SecondPassIntegration.logPhase_conjugate v _)
  rw [CenteredMomentTwistedReflection.polynomial_twisted_source χ.inverse _ X v hX,
    polynomial_inverse_plain χ _ X hX,ht,
    ←CenteredMomentTwistedReflection.polynomial_twisted_source χ _ X (-v) hX]
  congr 2
  ring

theorem actual_inverse_uniform (V : ℝ→ℂ) (M : ℝ) (hM : 0≤M)
    (hV : ∀y,V y≠0 → |y|≤M) (hreal : ∀y,conj (V y)=V y) (A J : ℕ) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀{ι : Type} [Fintype ι],
      ∀(G : ι→𝓢(ℝ,ℂ))(χ : ι→Character)(P : ι→ℂ)(s X : ι→ℝ),
      (∀i,0<s i) → (∀i,0<X i) → ∀D E : ℝ,0<D → 0≤E →
      (∀i,H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i)≤D) →
      (∀v,(∑i,‖HeckeDyadic.polynomial (χ i) false (logWindow V) (X i) 0 (-2*Real.pi*v)*P i‖^2)
        ≤E*((1+‖v‖)^J)^2) →
      (∑i,‖HeckeDyadic.polynomial (χ i).inverse false
        (fun x=>logWindow V x*((1+s i)^A:ℂ)*paperRadialFourier (G i) (s i*x))
          (X i) 0 0*P i‖^2)≤C*D^2*E := by
  obtain ⟨H,C,hC,hbound⟩ := actual_one_uniform V M hM hV A J
  refine ⟨H,C,hC,?_⟩
  intro ι _ G χ P s X hs hX D E hD hE hGD henergy
  apply hbound G (fun i=>(χ i).inverse) P s X hs hX D E hD hE hGD
  intro v
  have he (i : ι) :
      ‖HeckeDyadic.polynomial (χ i).inverse false (logWindow V) (X i) 0 (2*Real.pi*v)*P i‖=
      ‖HeckeDyadic.polynomial (χ i) false (logWindow V) (X i) 0 (-2*Real.pi*v)*P i‖ := by
    rw [inverse_annular_frequency (χ i) V hreal (X i) v (hX i),norm_mul,
      Complex.norm_conj,←norm_mul]
  simpa only [he] using henergy v

lemma paperRadialFourier_real_smul (c : ℝ) (G : 𝓢(ℝ,ℂ)) (x : ℝ) :
    paperRadialFourier (c • G : 𝓢(ℝ,ℂ)) x=(c:ℂ)*paperRadialFourier G x := by
  rw [paperRadialFourier_eq_ray,paperRadialFourier_eq_ray]
  simp only [map_smul,smul_apply,Complex.real_smul]

lemma polynomial_const_mul (χ : Character) (W : ℝ→ℂ) (X σ omega : ℝ) (c : ℂ) :
    HeckeDyadic.polynomial χ false (fun x=>c*W x) X σ omega=
      c*HeckeDyadic.polynomial χ false W X σ omega := by
  unfold HeckeDyadic.polynomial
  have he : (fun I : HeckeDyadic.NonzeroIdeal=>
      HeckeDyadic.summand χ false (fun x=>c*W x) X σ omega I)=
      (fun I=>c*HeckeDyadic.summand χ false W X σ omega I) := by
    funext I
    unfold HeckeDyadic.summand
    ring
  rw [he,tsum_mul_left]
  ring

lemma reflected_polynomial_real_smul (χ : Character) (V : ℝ→ℂ)
    (G : 𝓢(ℝ,ℂ)) (s X c : ℝ) (A : ℕ) :
    HeckeDyadic.polynomial χ false
      (fun x=>logWindow V x*((1+s)^A:ℂ)*paperRadialFourier (c • G : 𝓢(ℝ,ℂ)) (s*x)) X 0 0=
      (c:ℂ)*HeckeDyadic.polynomial χ false
        (fun x=>logWindow V x*((1+s)^A:ℂ)*paperRadialFourier G (s*x)) X 0 0 := by
  simp_rw [paperRadialFourier_real_smul]
  have he : (fun x=>logWindow V x*((1+s)^A:ℂ)*((c:ℂ)*paperRadialFourier G (s*x)))=
      (fun x=>(c:ℂ)*(logWindow V x*((1+s)^A:ℂ)*paperRadialFourier G (s*x))) := by
    funext x
    ring
  rw [he,polynomial_const_mul]

theorem detector_source_control (H : Finset (ℕ×ℕ)) :
    ∃n : ℕ,∃D : ℝ,0<D ∧ ∀reverse : Bool,∀k : ℕ,k≤2→
      ∀σ∈Set.Icc (0:ℝ) 1,∀t : ℝ,
      H.sup (schwartzSeminormFamily ℝ ℝ ℂ)
        (((1+‖t‖)^n)⁻¹ • CenteredMomentDetectorDictionary.detectorSchwartz reverse k σ t)≤D := by
  obtain ⟨n,D,hD,hb⟩ := CenteredMomentDetectorDictionary.detectorSchwartz_uniform H
  refine ⟨n,D,hD,?_⟩
  intro reverse k hk σ hσ t
  rw [map_smul_eq_mul,Real.norm_of_nonneg (by positivity : 0≤((1+‖t‖)^n)⁻¹)]
  exact (inv_mul_le_iff₀ (by positivity : 0<(1+‖t‖)^n)).mpr
    (by simpa only [mul_comm] using hb reverse k hk σ hσ t)

theorem detector_inverse_uniform (V : ℝ→ℂ) (M : ℝ) (hM : 0≤M)
    (hV : ∀y,V y≠0 → |y|≤M) (hreal : ∀y,conj (V y)=V y) (A J : ℕ) :
    ∃n : ℕ,∃C : ℝ,0<C ∧ ∀{ι : Type} [Fintype ι],
      ∀(reverse : ι→Bool)(k : ι→ℕ)(σ t : ι→ℝ),
      (∀i,k i≤2) → (∀i,σ i∈Set.Icc (0:ℝ) 1) →
      ∀(χ : ι→Character)(P : ι→ℂ)(s X : ι→ℝ),
      (∀i,0<s i) → (∀i,0<X i) → ∀E : ℝ,0≤E →
      (∀v,(∑i,‖HeckeDyadic.polynomial (χ i) false (logWindow V) (X i) 0 (-2*Real.pi*v)*
        (((1+‖t i‖)^n:ℝ):ℂ)*P i‖^2)≤E*((1+‖v‖)^J)^2) →
      (∑i,‖HeckeDyadic.polynomial (χ i).inverse false
        (fun x=>logWindow V x*((1+s i)^A:ℂ)*paperRadialFourier
          (CenteredMomentDetectorDictionary.detectorSchwartz (reverse i) (k i) (σ i) (t i)) (s i*x))
        (X i) 0 0*P i‖^2)≤C*E := by
  obtain ⟨H,C,hC,hb⟩ := actual_inverse_uniform V M hM hV hreal A J
  obtain ⟨n,D,hD,hcontrol⟩ := detector_source_control H
  refine ⟨n,C*D^2,by positivity,?_⟩
  intro ι _ reverse k σ t hk hσ χ P s X hs hX E hE henergy
  let G (i : ι) := CenteredMomentDetectorDictionary.detectorSchwartz (reverse i) (k i) (σ i) (t i)
  let w (i : ι) : ℝ := (1+‖t i‖)^n
  have hw (i : ι) : 0<w i := by dsimp [w];positivity
  have hh := hb (fun i=>(w i)⁻¹ • G i) χ (fun i=>(w i:ℂ)*P i) s X hs hX D E hD hE
    (fun i=>hcontrol (reverse i) (k i) (hk i) (σ i) (hσ i) (t i))
    (by intro v;simpa only [w,mul_assoc] using henergy v)
  have he (i : ι) : HeckeDyadic.polynomial (χ i).inverse false
      (fun x=>logWindow V x*((1+s i)^A:ℂ)*paperRadialFourier ((w i)⁻¹ • G i : 𝓢(ℝ,ℂ)) (s i*x))
      (X i) 0 0*((w i:ℂ)*P i)=
      HeckeDyadic.polynomial (χ i).inverse false
      (fun x=>logWindow V x*((1+s i)^A:ℂ)*paperRadialFourier (G i) (s i*x)) (X i) 0 0*P i := by
    rw [reflected_polynomial_real_smul,Complex.ofReal_inv]
    have hne : (w i:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (hw i).ne'
    rw [mul_mul_mul_comm,inv_mul_cancel₀ hne,one_mul]
  simp_rw [he] at hh
  simpa only [G] using hh

end SevenEighths.CenteredMomentUniformReflectionProfile

end

end OAI
