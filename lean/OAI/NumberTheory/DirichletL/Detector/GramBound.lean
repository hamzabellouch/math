import OAI.NumberTheory.DirichletL.Detector.GramScaleLoss

namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentGaussEnergy EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem actual_additive_gram_bound (δ : ℝ) (hδ : 0<δ) (hδ1 : δ<1)
    (a b M₀ : ℝ) (ha : 0<a) (hab : a<b) (hM₀ : 0≤M₀)
    (W : ℝ→ℂ) (hcompact : HasCompactSupport W) (hs : Function.support W⊆Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (hWM : ∀x,‖W x‖≤M₀) :
    ∃J : ℕ,∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal),fixedBadPrimes⊆S→∀U : SchwartzMap ℝ ℂ,
    ∃K : ℝ,0<K ∧ ∀(σ : RayRing)(v Y Q : ℝ)(hY : 1≤Y),0<Q→1≤Y^2/Q→
      ‖gaussEnergy (lowGaussColumns W hcompact Y (lt_of_lt_of_le zero_lt_one hY))
        (fun I=>primaryGenerator I.val) (fun I=>(supported_span_primaryGenerator_iff _).mpr I.property)
        (lowGaussColumn (calibrationForSet S hS) W Y σ v) U Q‖≤
      K*(1+|v|)^J*(Q/Y)*(1+(Y^2/Q)^(1/6:ℝ)+(Y^2/Q)^2/Y)*Y^δ := by
  obtain ⟨J,H₁,H₂,K₁,K₂,hK₁,hK₂,hbound⟩ := original_energy_nonzero_bound δ (1/12) hδ hδ1
    (by norm_num) (by norm_num) a b M₀ ha hab hM₀ W hcompact hs hW hWM
  obtain ⟨K₀,hK₀,hzero⟩ := lowGramZeroMode_source_bound a b M₀ ha hM₀
  refine ⟨J,?_⟩
  intro S hS hbad U
  let M : ℝ := Ideal.absNorm (jointFixedModulus S hS)
  have hM : 1≤M := by dsimp [M];exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (jointFixedModulus_nonzero S hS))
  let A₀ := K₀*‖paperRadialFourier U 0‖
  let A₁ := K₁*H₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*M
  let A₂ := K₂*H₂.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*M^(1/12:ℝ)
  have hA₀ : 0≤A₀ := by dsimp [A₀];positivity
  have hA₁ : 0≤A₁ := by dsimp [A₁];positivity
  have hA₂ : 0≤A₂ := by dsimp [A₂];positivity
  refine ⟨1+A₀+A₁+A₂,by positivity,?_⟩
  intro σ v Y Q hY hQ hP
  have hy : 0<Y := lt_of_lt_of_le zero_lt_one hY
  let P := Y^2/Q
  have hp : 1≤P := hP
  have hp0 : 0<P := lt_of_lt_of_le zero_lt_one hp
  let Z := lowGramZeroMode (calibrationForSet S hS) W hcompact Y hy σ v U Q
  let E := gaussEnergy (lowGaussColumns W hcompact Y hy) (fun I=>primaryGenerator I.val)
    (fun I=>(supported_span_primaryGenerator_iff _).mpr I.property)
    (lowGaussColumn (calibrationForSet S hS) W Y σ v) U Q
  have hn := hbound S hS hbad σ U v Y Q hy hQ
  have hz : ‖Z‖≤A₀*(Q/Y) := by
    have hh := hzero S hS W hcompact hs hWM Y hY σ v U Q hQ.le
    convert hh using 1 ; dsimp [Z,A₀] ; ring
  have hgood : K₁*H₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*(Q/Y)*P*
      (Y/(M*P))^(-1+δ)≤A₁*(1+|v|)^J*(Q/Y)*(P^2/Y)*Y^δ := by
    have hh := mul_le_mul_of_nonneg_left (nonexceptional_scale_loss M P Y δ hM hp hy hδ.le)
      (show 0≤K₁*H₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*(Q/Y) by positivity)
    convert hh using 1 <;> (try dsimp [A₁]) <;> ring
  have henergy : ‖E‖≤A₀*(Q/Y)+A₁*(1+|v|)^J*(Q/Y)*(P^2/Y)*Y^δ+A₂*(Q/Y)*P^(1/6:ℝ) := by
    have hn' : ‖E-Z‖≤A₁*(1+|v|)^J*(Q/Y)*(P^2/Y)*Y^δ+A₂*(Q/Y)*P^(1/6:ℝ) := by
      apply hn.trans
      exact add_le_add hgood (by dsimp [A₂,M,P];ring_nf;exact le_rfl)
    calc
      ‖E‖=‖(E-Z)+Z‖ := by congr 1;ring
      _≤‖E-Z‖+‖Z‖ := norm_add_le _ _
      _≤_ := by linarith
  let B := (1+|v|)^J*(Q/Y)*(1+P^(1/6:ℝ)+P^2/Y)*Y^δ
  have hb : 0≤B := by dsimp [B];positivity
  have hh : 1≤(1+|v|)^J := one_le_pow₀ (by linarith [abs_nonneg v])
  have hyd : 1≤Y^δ := Real.one_le_rpow hY hδ.le
  have hshape : 1≤1+P^(1/6:ℝ)+P^2/Y := by
    have hpow : 0≤P^(1/6:ℝ) := by positivity
    have hratio : 0≤P^2/Y := by positivity
    linarith
  have hb₀ : Q/Y≤B := by
    calc
      Q/Y=(1:ℝ)*(Q/Y)*1*1 := by ring
      _≤B := by dsimp [B];gcongr
  have hb₁ : (1+|v|)^J*(Q/Y)*(P^2/Y)*Y^δ≤B := by
    dsimp [B]
    gcongr
    have hpow : 0≤P^(1/6:ℝ) := by positivity
    linarith
  have hb₂ : (Q/Y)*P^(1/6:ℝ)≤B := by
    calc
      _=(1:ℝ)*(Q/Y)*P^(1/6:ℝ)*1 := by ring
      _≤B := by
        dsimp [B]
        gcongr
        have hratio : 0≤P^2/Y := by positivity
        linarith
  change ‖E‖≤_
  calc
    _≤A₀*(Q/Y)+A₁*((1+|v|)^J*(Q/Y)*(P^2/Y)*Y^δ)+A₂*((Q/Y)*P^(1/6:ℝ)) := by convert henergy using 1 ; ring
    _≤A₀*B+A₁*B+A₂*B := add_le_add (add_le_add (mul_le_mul_of_nonneg_left hb₀ hA₀)
      (mul_le_mul_of_nonneg_left hb₁ hA₁)) (mul_le_mul_of_nonneg_left hb₂ hA₂)
    _≤(1+A₀+A₁+A₂)*B := by nlinarith
    _=_ := by dsimp [B,P];ring

end SevenEighths.ProbeGramCommon
end

end OAI
