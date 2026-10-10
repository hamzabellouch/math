import OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileUniform
import OAI.NumberTheory.DirichletL.Descent.FirstGlobalPush

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open JointLogSeparation FourierBridge MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
open InverseMomentFirstProfileUniform InverseAmbientProfileTower
theorem actual_first_original_subset_two_energies (ε : ℝ) (hε : 0<ε)
    (U₀ : Fin 9 → 𝓢(ℝ,ℂ)) (g₁ g₂ Φ : 𝓢(ℝ,ℂ))
    (M₀ B₀ : Fin 9 → ℝ) (m₁ m₂ bcap : ℝ)
    (hM : ∀ i,0 ≤ M₀ i) (hB₀ : ∀ i,0 ≤ B₀ i)
    (hU : ∀ i,Function.support (U₀ i) ⊆ Set.Icc (-M₀ i) (M₀ i))
    (hg₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂) (Aker J : ℕ) :
    ∃ Cprofile Kpush : ℝ,0 ≤ Cprofile ∧ 0<Kpush ∧ ∀ {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (_hc : ∀ i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (_hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (F : Finset ι) (outer:Finset κ) (b : κ→SecondPassArithmetic.CubeCoordinates ι) (common : κ→Finset ι)
    (Ψ₁ Ψ₂ : Eis→*ℂ) (mleft mright : Eis) (dd:κ→Eis) (H₁ H₂ selector : κ→Finset ι→ℂ)
    (labels : κ→Finset (Ideal Eis)) (a : κ→Ideal Eis×Eis→ℂ) (Γ Y : ℝ)
    (_hΨ₁ : ∀ u,‖Ψ₁ u‖≤1) (_hΨ₂ : ∀ u,‖Ψ₂ u‖≤1)
    (_hΓ : 0≤Γ) (_hY : 0<Y)
    (_hlabels : ∀k∈outer,∀ f∈labels k,Squarefree f) (_hn : ∀k∈outer,∀ f∈labels k,f≠0)
    (_ha : ∀k∈outer,∀ x∈firstRetainedSource p (labels k) (b k) Y,‖a k x‖≤Γ)
    (ω₁ ω₂ : ℝ → ℂ) (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ : ℝ)
    (A₁ A₂ C R : (Σ _ : κ,Ideal Eis×Eis) → ℝ) (K L : ℝ) (_hK : 0<K) (s : Fin 9→ℝ)
    (_hs : ∀ i,0<s i)
    (selected : Finset (Σ _ : κ,Ideal Eis×Eis))
    (_hselected : selected⊆firstGlobalRetainedSource p outer labels b Y),
    let source := selected
    let C₁ := fun x : (Σ _ : κ,Ideal Eis×Eis) => firstCanonicalCoefficient p hp hcop hg (b x.1) (common x.1) true Ψ₁ mleft (dd x.1) (H₁ x.1) x.2
    let C₂ := fun x : (Σ _ : κ,Ideal Eis×Eis) => firstCanonicalCoefficient p hp hcop hg (b x.1) (common x.1) false Ψ₂ mright (dd x.1) (H₂ x.1) x.2
    let w := fun x : (Σ _ : κ,Ideal Eis×Eis) => retainedCubeWeight p hp hcop hg (b x.1) (common x.1) Ψ₁ Ψ₂ mleft mright (dd x.1) (a x.1) x.2
    ∀ (_hpos : ∀ x∈source,0<A₁ x ∧ 0<A₂ x ∧ 0<C x ∧ 0<R x ∧ dd x.1≠0 ∧ x.2.2≠0)
    (_hρ : ∀ i,|ρ i| ≤ B₀ i) (_hc₁ : 1 ≤ c₁) (_hc₂ : 1 ≤ c₂)
    (_hc₁b : c₁ ≤ bcap) (_hc₂b : c₂ ≤ bcap) (_hL : 0 ≤ L)
    (_hω₁ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x.1 j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) x.2.2 j ≠ 0 →
      (positiveSource g₁ c₁ θ₁) (A₁ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.1/(s 0*s 2*s 5*s 7)) ≠ 0 →
      ω₁ (primeProductNorm p j.2.2.1/s 7) = 1)
    (_hω₂ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x.1 j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) x.2.2 j ≠ 0 →
      (positiveSource g₂ c₂ θ₂) (A₂ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.2/(s 1*s 2*s 5*s 8)) ≠ 0 →
      ω₂ (primeProductNorm p j.2.2.2/s 8) = 1)
    (_hcut : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x.1 j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) x.2.2 j ≠ 0 →
      ω₁ (primeProductNorm p j.2.2.1/s 7) ≠ 0 → ω₂ (primeProductNorm p j.2.2.2/s 8) ≠ 0 →
      ∀ i,U₀ i ((firstRelativeLog (firstCommonNorms p (A₁ x) (A₂ x) (C x) (R x) (dd x.1) x.2.2 j) s i)+ρ i) = 1)
    (B₁ B₂ : ℝ) (_hB₁ : 0 ≤ B₁) (_hB₂ : 0 ≤ B₂)
    (_hleft : ∀ z : Frequency × (Fin 9 → ℝ),
      (∑k∈outer,firstCanonicalSecondEnergy p hp hg hinj F (b k) (common k) true Ψ₁ mleft (dd k) (H₁ k) (selector k) ω₁ (s 7)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) Y) ≤
        B₁*(tripleHeight J z.1*coordinateHeight J z.2))
    (_hright : ∀ z : Frequency × (Fin 9 → ℝ),
      (∑k∈outer,firstCanonicalSecondEnergy p hp hg hinj F (b k) (common k) false Ψ₂ mright (dd k) (H₂ k) (selector k) ω₂ (s 8)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) Y) ≤
        B₂*(tripleHeight J z.1*coordinateHeight J z.2)),
    ‖firstFamilyPhysicalRows p hg source F (fun x=>selector x.1) C₁ C₂ w (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂) Φ A₁ A₂ C R K (fun x=>dd x.1) (fun x=>x.2.2) s‖ ≤
      (Real.exp ((9/2:ℝ)*L)/firstRootScale s)*
        ((Γ*Kpush*Y^ε*(Real.sqrt B₁*Real.sqrt B₂))*(Cprofile*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
          (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
          (1+K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8))^Aker)) := by
  obtain ⟨Cprofile,hCprofile,hprofile⟩ := actual_first_moving_family_two_energies_uniform
    U₀ g₁ g₂ Φ M₀ B₀ m₁ m₂ bcap hM hB₀ hU hg₁ hg₂ Aker J
  obtain ⟨Kpush,hKpush,hpush⟩ := first_global_retained_push_uniform ε hε
  refine ⟨Cprofile,Kpush,hCprofile,hKpush,?_⟩
  intro ι κ _ _ p hp _ hg hinj hcop hc hpr F outer b common Ψ₁ Ψ₂ mleft mright dd H₁ H₂ selector labels a Γ Y
    hΨ₁ hΨ₂ hΓ hY hlabels hn ha ω₁ ω₂ ρ c₁ c₂ θ₁ θ₂ A₁ A₂ C R K L hK s hs selected hselected
    source C₁ C₂ w hpos hρ hc₁ hc₂ hc₁b hc₂b hL hω₁ hω₂ hcut B₁ B₂ hB₁ hB₂ hleft hright
  have hweight : 0≤Γ*Kpush*Y^ε := by positivity
  have hroot:Real.sqrt (Γ*Kpush*Y^ε*B₁)*Real.sqrt (Γ*Kpush*Y^ε*B₂)=Γ*Kpush*Y^ε*(Real.sqrt B₁*Real.sqrt B₂):=by
    rw [Real.sqrt_mul hweight,Real.sqrt_mul hweight]
    calc
      _=(Real.sqrt (Γ*Kpush*Y^ε))^2*(Real.sqrt B₁*Real.sqrt B₂):=by ring
      _= _:=by rw [Real.sq_sqrt hweight]
  rw [←hroot]
  apply hprofile p hp hg source F (fun x=>selector x.1) C₁ C₂ w ω₁ ω₂ ρ c₁ c₂ θ₁ θ₂
    A₁ A₂ C R K L hK (fun x=>dd x.1) (fun x=>x.2.2) s hpos hs hρ hc₁ hc₂ hc₁b hc₂b hL
    hω₁ hω₂ hcut (Γ*Kpush*Y^ε*B₁) (Γ*Kpush*Y^ε*B₂) (mul_nonneg hweight hB₁) (mul_nonneg hweight hB₂)
  · intro z
    have he := hpush p hp hinj hcop hg hc hpr F outer b common Ψ₁ Ψ₂ mleft mright dd
      labels a Γ Y hΨ₁ hΨ₂ hΓ hY hlabels hn ha true H₁ selector ω₁ (s 7)
      (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) (hs 7)
    simp only [ite_true,] at he
    have hm1 : firstFamilyEnergy p hg source F (fun x=>selector x.1) C₁ w true ω₁ (s 7)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) (fun x=>x.2.2) ≤
        firstFamilyEnergy p hg (firstGlobalRetainedSource p outer labels b Y) F
        (fun x=>selector x.1) C₁ w true ω₁ (s 7)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) (fun x=>x.2.2) := by
      unfold firstFamilyEnergy
      exact Finset.sum_le_sum_of_subset_of_nonneg hselected (fun x hx hn=>
        mul_nonneg (norm_nonneg _) (firstBlockEnergy_nonneg p hg _ _ _ _ _ _ _ _))
    apply (hm1.trans he).trans
    simpa only [mul_assoc,ite_true,ite_false,Bool.false_eq_true] using mul_le_mul_of_nonneg_left (hleft z) hweight
  · intro z
    have he := hpush p hp hinj hcop hg hc hpr F outer b common Ψ₁ Ψ₂ mleft mright dd
      labels a Γ Y hΨ₁ hΨ₂ hΓ hY hlabels hn ha false H₂ selector ω₂ (s 8)
      (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) (hs 8)
    simp only [ite_false,Bool.false_eq_true] at he
    have hm2 : firstFamilyEnergy p hg source F (fun x=>selector x.1) C₂ w false ω₂ (s 8)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) (fun x=>x.2.2) ≤
        firstFamilyEnergy p hg (firstGlobalRetainedSource p outer labels b Y) F
        (fun x=>selector x.1) C₂ w false ω₂ (s 8)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) (fun x=>x.2.2) := by
      unfold firstFamilyEnergy
      exact Finset.sum_le_sum_of_subset_of_nonneg hselected (fun x hx hn=>
        mul_nonneg (norm_nonneg _) (firstBlockEnergy_nonneg p hg _ _ _ _ _ _ _ _))
    apply (hm2.trans he).trans
    simpa only [mul_assoc,ite_true,ite_false,Bool.false_eq_true] using mul_le_mul_of_nonneg_left (hright z) hweight

end
end SevenEighths.InverseMoment

end OAI
