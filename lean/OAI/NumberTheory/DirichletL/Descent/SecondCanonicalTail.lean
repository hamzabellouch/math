import OAI.NumberTheory.DirichletL.Descent.SecondMarkedTail
import OAI.NumberTheory.DirichletL.Descent.SecondFreshTruncation
import OAI.NumberTheory.DirichletL.Descent.SecondCutoffScale

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InversePrincipalEnergy InverseSecondPrincipalCaller
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem first_fresh_canonical_error (ε : ℝ) (hε : 0<ε) (order : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (Ct Cm : ℝ), 0<Ct ∧ 0<Cm ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι → Eis) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i})≠2)
      (F D Bset : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
      (negative : Bool) (χ : RayCharacter) (Ψ : Eis→*ℂ),
      (∀ z,‖Ψ z‖≤1) → ∀ (m : Eis)
      (slots : Finset σ) (lists : σ→Finset ι) (coeff : σ→ι→ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i∈slots,∀ k∈lists i,‖coeff i k‖≤1) →
      (∀ i∈slots,Disjoint (lists i) D) →
      ∀ (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hs : Function.support om⊆Set.Icc a b)
      (X height Wbound Z M n ell V delta A B j t eta tau : ℝ),
      0<X → 0<Z → 1≤X*Real.exp Wbound → b≤Real.exp Wbound →
      X*Real.exp Wbound≤Z^(n-A-B-t+4*eta) →
      ∀ (c d : Eis), d≠0 → ‖ConcreteTraceCRT.eisEmbedding d‖^2≤Z^(delta+eta) →
      ∀ (r : FirstCoreIndex) (g theta : Finset ι→ℝ),
      (∀ G∈F.powerset,Z^(g G-eta)≤primeProductNorm p G) →
      (∀ G∈F.powerset,∀ E : G.powerset,primeProductNorm p E.val≤Z^(theta E.val+eta)) →
      let Y := Z^(firstPhysicalHeight M n ell V delta B j+12*eta+tau)
      let H := Z^tau
      let H₀ := markedRadial p slots lists coeff ∅ (principalWindow om a b ha hs negative height) X
      let Ψ₀ := firstCoreTwist negative χ Ψ r
      let m₀ := (m*b0Label p Bset v ε₁ ε₂)*∏ i∈D,p i
      let c₀ := c*jLabel p Bset v ε₁ ε₂
      let K := fun (G E : Finset ι) => childFrequencyBall
        (d*primeSubsetGenerator (fun i=>Ideal.span {p i}) E)
        (Z^(childM M ell A t (g G) (theta E) V j eta))
      ‖firstFreshSecondPoisson p hp hg hinj F D Bset v ε₁ ε₂ negative χ Ψ m
          (primeMark slots lists coeff) om X c d r height Y -
        truncatedSecondSource p hp hg hinj F Ψ₀ m₀ c₀ d H₀ rowMajorant Y K‖ ≤
        (128*(X*Real.exp Wbound))^4 *
          ((Cm*(X*Real.exp Wbound)^ε*SchwartzMap.seminorm ℝ 0 0 om)^2 *
            (Y*(Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
              (1+(X*Real.exp Wbound)^3/Y)^2/(1+H)^order)) := by
  obtain ⟨s,Ct,hCt,htail⟩ := full_second_correlated_tail order
  obtain ⟨Cm,hCm,hmark⟩ := marked_radial_uniform_bound ε hε
  refine ⟨s,Ct,Cm,hCt,hCm,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc F D Bset v ε₁ ε₂ negative χ Ψ hΨ m
    slots lists coeff hslots hcoeff hD om a b ha hs X height Wbound Z M n ell V delta A B j t eta tau
    hX hZ hL hb hLscale c d hd hdN r g theta hgN heN Y H H₀ Ψ₀ m₀ c₀ K
  have hY : 0<Y := Real.rpow_pos_of_pos hZ _
  have hH : 0≤H := (Real.rpow_pos_of_pos hZ _).le
  have hid := first_fresh_radial_truncated p hp hg hinj hc F D Bset v ε₁ ε₂ negative χ Ψ m
    slots lists coeff hD om a b ha hs X height Y hX hY c d r K
  change _ = truncatedSecondSource p hp hg hinj F Ψ₀ m₀ c₀ d H₀ rowMajorant Y K +
    secondSourceTail p hp hg hinj F Ψ₀ m₀ c₀ d H₀ rowMajorant Y K at hid
  rw [hid,add_sub_cancel_left]
  have hVsupp := principalWindow_upper om a b ha hs Wbound hb negative height
  have hcoef := hmark p hp hcop slots lists coeff hslots hcoeff ∅
    (principalWindow om a b ha hs negative height) X Wbound hX hVsupp
  simp only [Finset.card_empty,pow_zero,one_mul,principalWindow_seminorm_zero] at hcoef
  apply htail p hp hg hinj hc F Ψ₀
    (fun z=>(firstCoreTwist_norm_le negative χ Ψ r z).trans (hΨ z))
    m₀ c₀ d hd H₀ rowMajorant _ Y H (X*Real.exp Wbound)
    (fun G E=>Z^(childM M ell A t (g G) (theta E) V j eta))
    (by positivity) hY hH hL hcoef
  · exact markedRadial_support p slots lists coeff ∅ _ X Wbound hX hVsupp
  · intro G hG E
    exact second_correlated_radius_childM p hp d G E.val Z M n ell V delta A B j t (g G)
      (theta E.val) eta tau (X*Real.exp Wbound) hZ (zero_le_one.trans hL)
      hdN (heN G hG E) (hgN G hG) hLscale

end
end SevenEighths.InverseMoment

end OAI
