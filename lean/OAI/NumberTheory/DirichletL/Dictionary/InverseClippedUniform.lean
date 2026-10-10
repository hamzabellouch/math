import OAI.NumberTheory.DirichletL.Dictionary.InverseUniformSource
import OAI.NumberTheory.DirichletL.Descent.ClippedEnergy
import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerClipping
import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerUniform

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge

namespace SevenEighths.DetectorDictionaryInverseClippedUniform
open DetectorDictionaryInverseUniform HeckeInverseAmplification
open InverseMoment InverseInitialClippedColumns InverseInitialOverlapFourier
open ActualEisensteinCubic CompletedGauss
local notation "O" => ActualEisensteinCubic.O

theorem source_support (scaled reverse : Bool) (n : ℕ) (U tstar r σ t : ℝ) :
    Function.support (inverseSourceSchwartz scaled reverse n U tstar r σ t : ℝ→ℂ) ⊆
      Set.Icc (1/4 : ℝ) (9/4) := by
  let W := inverseDetectorSchwartz reverse n (U^r/U^tstar) σ t
  have hw : Function.support (W : ℝ→ℂ) ⊆ Set.Icc (1/4 : ℝ) (9/4) := by
    have he : (W : ℝ→ℂ) = twistProfile
        (baseProfile reverse n HeckeDetectorProfiles.cutoff
          HeckeDetectorDyadicProfiles.positiveAnnular (U^r/U^tstar)) σ t := by
      funext x
      exact inverseDetectorSchwartz_apply _ _ _ _ _ _
    rw [he]
    exact (twistProfile_support _ _ _).trans
      ((baseProfile_support _ _ _ _ _).trans HeckeDetectorDyadicProfiles.positiveAnnular_support)
  have ht : tsupport (W : ℝ→ℂ) ⊆ Set.Icc (1/4 : ℝ) (9/4) :=
    closure_minimal hw isClosed_Icc
  cases scaled
  · exact hw
  · intro x hx
    by_contra hn
    have hz : W x = 0 := by
      by_contra h
      exact hn (hw h)
    have hd : deriv (W : ℝ→ℂ) x = 0 := by
      by_contra h
      exact hn (ht (support_deriv_subset h))
    apply hx
    change scaleCLM W x = 0
    rw [scaleCLM_apply]
    simp [scaleProfile, hz, hd]

theorem source_zero_of_ratio (scaled reverse : Bool) (n : ℕ) (U tstar r σ t : ℝ)
    (h : 4 ≤ U^r/U^tstar) : inverseSourceSchwartz scaled reverse n U tstar r σ t = 0 :=
  inverseDetectorTest_zero_of_four_le scaled reverse n _ σ t h

theorem exists_reference_window :
    ∃w : 𝓢(ℝ,ℂ), HasCompactSupport (w : ℝ→ℂ) ∧
      tsupport (w : ℝ→ℂ) ⊆ Set.Icc (1/18 : ℝ) (13/4) ∧
      ∀x∈Set.Icc (1/9 : ℝ) (9/4), w x = 1 := by
  obtain ⟨w,hc,hone,hs⟩ := InverseSecondChildWindows.positive_cutoff
    (1/9 : ℝ) (9/4) (by norm_num) (by norm_num)
  refine ⟨w,hc,?_,hone⟩
  convert hs using 1
  norm_num

def referenceWindow : 𝓢(ℝ,ℂ) := Classical.choose exists_reference_window

theorem referenceWindow_compact : HasCompactSupport (referenceWindow : ℝ→ℂ) :=
  (Classical.choose_spec exists_reference_window).1

theorem referenceWindow_support : tsupport (referenceWindow : ℝ→ℂ) ⊆
    Set.Icc (1/18 : ℝ) (13/4) :=
  (Classical.choose_spec exists_reference_window).2.1

theorem referenceWindow_one (x : ℝ) (hx : x∈Set.Icc (1/9 : ℝ) (9/4)) :
    referenceWindow x = 1 :=
  (Classical.choose_spec exists_reference_window).2.2 x hx

theorem referenceWindow_agrees (scaled reverse : Bool) (n : ℕ) (U tstar r σ t c y : ℝ)
    (hc : 1≤c) (hcb : c≤9/4) (hy : 0<y) :
    referenceWindow y * inverseSourceSchwartz scaled reverse n U tstar r σ t (c*y) =
      inverseSourceSchwartz scaled reverse n U tstar r σ t (c*y) := by
  by_cases hz : inverseSourceSchwartz scaled reverse n U tstar r σ t (c*y) = 0
  · simp [hz]
  have hs := source_support scaled reverse n U tstar r σ t hz
  have hh : y∈Set.Icc (1/9 : ℝ) (9/4) := by
    constructor <;> nlinarith [hs.1,hs.2]
  rw [referenceWindow_one y hh,one_mul]

def logSource (scaled reverse : Bool) (n : ℕ) (U tstar r σ t : ℝ) : 𝓢(ℝ,ℂ) :=
  CubicReflectionKernel.logPullbackCLM (1/4) (9/4)
    (inverseSourceSchwartz scaled reverse n U tstar r σ t)

theorem logSource_apply (scaled reverse : Bool) (n : ℕ) (U tstar r σ t x : ℝ) :
    logSource scaled reverse n U tstar r σ t x =
      inverseSourceSchwartz scaled reverse n U tstar r σ t (Real.exp x) :=
  CubicReflectionKernel.logPullbackCLM_eq_actual _ _ (by norm_num) _
    (source_support scaled reverse n U tstar r σ t) x

theorem logSource_eq_logSchwartz (scaled reverse : Bool) (n : ℕ) (U tstar r σ t : ℝ) :
    logSource scaled reverse n U tstar r σ t =
      CubicReflectionKernel.logSchwartz (inverseSourceSchwartz scaled reverse n U tstar r σ t)
        (1/4) (9/4) (by norm_num) (source_support scaled reverse n U tstar r σ t)
        ((inverseSourceSchwartz scaled reverse n U tstar r σ t).smooth ⊤) := by
  ext x
  rw [logSource_apply,CubicReflectionKernel.logSchwartz_apply]

def familyDensity (scaled reverse : Bool) (n : ℕ) (U tstar r σ t c v : ℝ) : ℂ :=
  density (logSource scaled reverse n U tstar r σ t) (Real.log c) v

theorem familyDensity_formula (scaled reverse : Bool) (n : ℕ) (U tstar r σ t c v : ℝ) :
    familyDensity scaled reverse n U tstar r σ t c v =
      (𝓕 (logSource scaled reverse n U tstar r σ t)) v * logPhase v (Real.log c) := rfl

theorem familyDensity_norm (scaled reverse : Bool) (n : ℕ) (U tstar r σ t c v : ℝ) :
    ‖familyDensity scaled reverse n U tstar r σ t c v‖ =
      ‖(𝓕 (logSource scaled reverse n U tstar r σ t)) v‖ := density_norm _ _ _

theorem familyDensity_integrable (J : ℕ) (scaled reverse : Bool) (n : ℕ)
    (U tstar r σ t c : ℝ) :
    Integrable (fun v : ℝ => (1+‖v‖)^J * ‖familyDensity scaled reverse n U tstar r σ t c v‖) := by
  simp only [familyDensity_norm]
  exact AnalyticBridge.schwartz_fourier_one_plus_integrable _ _

theorem familyDensity_moment (J : ℕ) :
    ∃K : ℕ, ∃C : ℝ, 0<C ∧ ∀scaled reverse : Bool, ∀n : ℕ, n≤2 →
      ∀U : ℝ, 0<U → ∀tstar r : ℝ, ∀σ∈Set.Icc (0 : ℝ) 1, ∀t c : ℝ,
      (∫v : ℝ, (1+‖v‖)^J * ‖familyDensity scaled reverse n U tstar r σ t c v‖) ≤
        C*(1+‖t‖)^K := by
  let p := (volume : Measure ℝ).integrablePower
  let S : Finset (ℕ×ℕ) := Finset.Iic (p,J+p)
  obtain ⟨T,A,hA,hop⟩ := EisensteinSchwartzPoisson.schwartzCLM_finite_seminorm_control
    (CubicReflectionKernel.logPullbackCLM (1/4) (9/4)) S
  obtain ⟨K,B,hB,hsource⟩ := inverseSourceSchwartz_uniform T
  let C := 1+(2 : ℝ)^J*(coefficientMomentBound 0 (2*A*B)+coefficientMomentBound J (2*A*B))
  have hC : 0<C := by
    have h₀ := coefficientMomentBound_nonneg 0 (2*A*B) (by positivity)
    have hJ := coefficientMomentBound_nonneg J (2*A*B) (by positivity)
    dsimp [C]
    positivity
  refine ⟨K,C,hC,?_⟩
  intro scaled reverse n hn U hU tstar r σ hσ t c
  let W := inverseSourceSchwartz scaled reverse n U tstar r σ t
  let g := logSource scaled reverse n U tstar r σ t
  have hb : S.sup (schwartzSeminormFamily ℝ ℝ ℂ) g ≤ A*B*(1+‖t‖)^K := by
    exact (hop W).trans ((mul_le_mul_of_nonneg_left
      (hsource scaled reverse n hn U hU tstar r σ hσ t) hA.le).trans_eq (by ring))
  have hs (i : ℕ) (hi : i≤J+p) :
      (SchwartzMap.seminorm ℝ 0 i) g + (SchwartzMap.seminorm ℝ p i) g ≤
        2*A*B*(1+‖t‖)^K := by
    have h₀ : schwartzSeminormFamily ℝ ℝ ℂ (0,i) ≤ S.sup (schwartzSeminormFamily ℝ ℝ ℂ) :=
      Finset.le_sup (f:=schwartzSeminormFamily ℝ ℝ ℂ) (by simp [S,hi])
    have hp : schwartzSeminormFamily ℝ ℝ ℂ (p,i) ≤ S.sup (schwartzSeminormFamily ℝ ℝ ℂ) :=
      Finset.le_sup (f:=schwartzSeminormFamily ℝ ℝ ℂ) (by simp [S,hi])
    have h₁ := (Seminorm.le_def.mp h₀ g).trans hb
    have h₂ := (Seminorm.le_def.mp hp g).trans hb
    change (SchwartzMap.seminorm ℝ 0 i) g ≤ _ at h₁
    change (SchwartzMap.seminorm ℝ p i) g ≤ _ at h₂
    linarith
  have hmoment := uniform_fourier_one_plus_moment g J 1
    (2*A*B*(1+‖t‖)^K) (by norm_num) (by positivity)
    (by intro i hi; simpa only [one_mul] using hs i hi)
  simp only [one_mul] at hmoment
  simp only [familyDensity_norm]
  apply hmoment.trans
  have he : (2 : ℝ)^J*(coefficientMomentBound 0 (2*A*B*(1+‖t‖)^K)+
      coefficientMomentBound J (2*A*B*(1+‖t‖)^K)) =
      ((2 : ℝ)^J*(coefficientMomentBound 0 (2*A*B)+coefficientMomentBound J (2*A*B)))*(1+‖t‖)^K := by
    unfold coefficientMomentBound
    ring
  rw [he]
  dsimp [C]
  exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

section Rows
variable {ι ρ : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem canonical_family_mode_integrable
    (hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool : Finset ι) (Ψ : O→*ℂ) (m f k : O) (slots : Finset ρ)
    (lists : ρ→Finset ι) (a : ρ→ι→ℂ)
    (scaled reverse : Bool) (n : ℕ) (U tstar r σ t c θ X : ℝ) :
    Integrable (fun v : ℝ => familyDensity scaled reverse n U tstar r σ t c v *
      finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a
        (childLogTest referenceWindow (θ+v)) X) :=
  canonical_clipped_mode_integrable p hp hcop hg hpr pool Ψ m f k slots lists a
    (logSource scaled reverse n U tstar r σ t) referenceWindow c θ X

theorem canonical_clipped_family_fourier
    (hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool : Finset ι) (Ψ : O→*ℂ) (m f k : O) (slots : Finset ρ)
    (lists : ρ→Finset ι) (a : ρ→ι→ℂ)
    (scaled reverse : Bool) (n : ℕ) (U tstar r σ t c θ X : ℝ)
    (hc : 1≤c) (hcb : c≤9/4) (hX : 0<X) :
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a
      (clippedTest (inverseSourceSchwartz scaled reverse n U tstar r σ t) c θ) X =
    ∫v : ℝ, familyDensity scaled reverse n U tstar r σ t c v *
      finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a
        (childLogTest referenceWindow (θ+v)) X := by
  simp only [familyDensity,logSource_eq_logSchwartz]
  exact canonical_clipped_fourier p hp hcop hg hpr pool Ψ m f k slots lists a
    (inverseSourceSchwartz scaled reverse n U tstar r σ t) (1/4) (9/4) (by norm_num)
    (source_support scaled reverse n U tstar r σ t)
    ((inverseSourceSchwartz scaled reverse n U tstar r σ t).smooth ⊤)
    referenceWindow c θ X (zero_lt_one.trans_le hc) hX
    (fun y hy=>referenceWindow_agrees scaled reverse n U tstar r σ t c y hc hcb hy)
end Rows

theorem canonical_clipped_family_energy (J : ℕ) :
    ∃K : ℕ, ∃C : ℝ, 0<C ∧ ∀scaled reverse : Bool, ∀n : ℕ, n≤2 →
    ∀U : ℝ, 0<U → ∀tstar r : ℝ, ∀σ∈Set.Icc (0 : ℝ) 1, ∀t : ℝ,
    ∀{ι ρ : Type*} [DecidableEq ι] [DecidableEq ρ]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (_hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool : Finset ι) (Ψ : O→*ℂ) (m : O) (slots : Finset ρ) (lists : ρ→Finset ι) (a : ρ→ι→ℂ)
    (labels : Finset (Ideal O)) (rows : Finset O) (D : Ideal O→ℝ) (_hD : ∀f∈labels,0≤D f)
    (c θ X Z F E : ℝ), 1≤c → c≤9/4 → 0<X → 0≤E →
    (∀s, normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
      (childLogTest referenceWindow s) X Z F ≤ E*(1+‖s‖)^(2*J)) →
    normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
      (clippedTest (inverseSourceSchwartz scaled reverse n U tstar r σ t) c θ) X Z F ≤
        C*E*(1+‖t‖)^(2*K)*(1+‖θ‖)^(2*J) := by
  obtain ⟨K,C,hC,hmass⟩ := familyDensity_moment J
  refine ⟨K,C^2,by positivity,?_⟩
  intro scaled reverse n hn U hU tstar r σ hσ t ι ρ _ _ p hp _ hcop hg hpr
    pool Ψ m slots lists a labels rows D hD c θ X Z F E hc hcb hX hE he
  have hb := canonical_clipped_energy p hp hcop hg hpr pool Ψ m slots lists a
    labels rows D hD (inverseSourceSchwartz scaled reverse n U tstar r σ t)
    (1/4) (9/4) (by norm_num) (source_support scaled reverse n U tstar r σ t)
    ((inverseSourceSchwartz scaled reverse n U tstar r σ t).smooth ⊤)
    referenceWindow c θ X Z F E J (zero_lt_one.trans_le hc) hX hE
    (fun y hy=>referenceWindow_agrees scaled reverse n U tstar r σ t c y hc hcb hy) he
  have hm := hmass scaled reverse n hn U hU tstar r σ hσ t c
  simp only [familyDensity_norm,logSource_eq_logSchwartz] at hm
  have hs := pow_le_pow_left₀
    (integral_nonneg (fun v : ℝ => by positivity)) hm 2
  apply hb.trans
  calc
    _ ≤ E*(1+‖θ‖)^(2*J)*(C*(1+‖t‖)^K)^2 :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by rw [mul_pow,←pow_mul]; ring_nf

theorem initial_raw_family_energy (J : ℕ) :
    ∃K : ℕ, ∃C : ℝ, 0<C ∧ ∀scaled reverse : Bool, ∀n : ℕ, n≤2 →
    ∀U : ℝ, 0<U → ∀tstar r : ℝ, ∀σ∈Set.Icc (0 : ℝ) 1, ∀t : ℝ,
    ∀{ι ρ : Type*} [DecidableEq ι] [DecidableEq ρ]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (_hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool : Finset ι) (Ψ : O→*ℂ) (m : O) (slots : Finset ρ) (lists : ρ→Finset ι) (a : ρ→ι→ℂ)
    (labels : Finset (Ideal O)) (rows : Finset O) (D : Ideal O→ℝ) (_hD : ∀f∈labels,0≤D f)
    (Z N F E : ℝ) (z : JointLogSeparation.Frequency×(Fin 6→ℝ)) (h : ℝ), 1<Z → 0≤E →
    (h = -InverseInitialClippedColumns.leftHeight z ∨ h = InverseInitialClippedColumns.rightHeight z) →
    (∀s, normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
      (childLogTest referenceWindow s) (Z^(max 0 N)) Z F ≤ E*(1+‖s‖)^(2*J)) →
    normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
      (childLogTest (inverseSourceSchwartz scaled reverse n U tstar r σ t) h) (Z^N) Z F ≤
        C*E*(1+‖t‖)^(2*K)*
          (InverseMoment.tripleHeight (4*J) z.1 * InverseMoment.coordinateHeight (4*J) z.2) := by
  obtain ⟨K,C,hC,hbound⟩ := canonical_clipped_family_energy J
  refine ⟨K,C,hC,?_⟩
  intro scaled reverse n hn U hU tstar r σ hσ t ι ρ _ _ p hp _ hcop hg hpr
    pool Ψ m slots lists a labels rows D hD Z N F E z h hZ hE hh he
  let W := inverseSourceSchwartz scaled reverse n U tstar r σ t
  by_cases hne : (freshColumns p pool W (Z^N)).Nonempty
  · obtain ⟨hc,hcb⟩ := freshColumns_clipping_range p hp pool W (1/4) (9/4)
      Z N hZ (by norm_num) (source_support scaled reverse n U tstar r σ t) hne
    rw [InverseInitialEnergyCallerClipping.normalized_energy_clipping p hp hcop hg
      pool Ψ m slots lists a labels rows D W (by linarith) N h F]
    apply (hbound scaled reverse n hn U hU tstar r σ hσ t
      p hp hcop hg hpr pool Ψ m slots lists a labels rows D hD
      (Z^(max 0 N-N)) h (Z^(max 0 N)) Z F E hc hcb (by positivity) hE he).trans
    exact mul_le_mul_of_nonneg_left
      (InverseInitialEnergyCallerUniform.initial_height_bound J z h hh) (by positivity)
  · have hz := Finset.not_nonempty_iff_eq_empty.mp hne
    change normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
      (childLogTest W h) (Z^N) Z F ≤ _
    unfold normalizedColumnEnergy
    simp_rw [canonical_row_zero_of_freshColumns_empty p hp hcop hg pool Ψ m _ _
      slots lists a W (Z^N) h hz,mul_zero,norm_zero,zero_pow (by omega : (2 : ℕ)≠0),
      Finset.sum_const_zero,mul_zero,Finset.sum_const_zero]
    dsimp [InverseMoment.tripleHeight,InverseMoment.coordinateHeight]
    positivity

end SevenEighths.DetectorDictionaryInverseClippedUniform

end

end OAI
