import OAI.NumberTheory.DirichletL.Descent.GlobalPriorityTailAggregate

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentGlobalPriorityTail
open InverseMoment InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseMomentGlobalPrincipalMass InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InversePrioritySecondSource InverseSecondPrincipalCaller InversePrincipalEnergy
open InverseWholePriorityRetainedSource FirstCauchyArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

theorem global_physical_tail_rapid (Jmax : ℕ) (Lcap tau saving : ℝ)
    (hLcap : 0≤Lcap) (htau : 0<tau) :
    ∃(s : Finset (ℕ×ℕ))(C : ℝ),0<C ∧
    ∀{ι σ : Type*}[DecidableEq ι][DecidableEq σ]
      (p : ι→O)(hp : ∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (Jo : ℕ),Jo≤Jmax → ∀(extra : CubeCoordinates ι→Finset ι)(pool : Finset ι)
      (source : Finset (Source ι Jo))(negative : Bool)(Ψ : O→*ℂ)(m : O)
      (w : Source ι Jo→ℂ)(slots : Finset σ)(lists : σ→Finset ι)(a : σ→ι→ℂ),
      (slots:Set σ).PairwiseDisjoint lists →
      (∀i∈slots,∀k∈lists i,‖a i k‖≤1) → (∀u,‖Ψ u‖≤1) → (∀x∈source,‖w x‖≤1) →
      ∀(om : 𝓢(ℝ,ℂ))(lo hi : ℝ)(hlo : 0<lo)(hs : Function.support om⊆Set.Icc lo hi)
      (X M Y Z height kappa eta : ℝ)(R : Finset ι→Finset ι→ℝ),
      kappa+(9/2:ℝ)*eta≤Lcap →
      0<X → hi≤Real.exp M → 1≤Z → 0<Y → 1≤X*Real.exp M →
      Y≤Z^Lcap → Y⁻¹≤Z^Lcap → X*Real.exp M≤Z^Lcap →
      (∀x∈source,SourceValid p x) → (∀x∈source,extra x.cube⊆x.cube.support) →
      (∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^Lcap) →
      (∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^Lcap) →
      (∀x∈source,‖eisEmbedding (∏i∈cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖≤Z^Lcap) →
      (∀x∈source,primeProductNorm p x.firstCommon≤Z^Lcap) →
      (∀x∈source,primeProductNorm p x.quotientSupport≤Z^Lcap) →
      (∀x∈source,∀G∈pool.powerset,∀E:G.powerset,
        correlatedSecondRadius p (secondParentDivisor p (parent p x)) G E.val
          (X*Real.exp M) Y (Z^tau)≤R G E.val) →
      (Z^kappa*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*((32*512)*(2:ℝ)^slots.card*
      (∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑J∈slots.powerset,
        ‖∑y∈wholeAssignedParents p (fun x=>extra x.cube) source negative J lists,
        coefficient p J a (globalPriorityOuter p hg negative Ψ m ray core w) y*
        priorityTailParent p hg hp hinj extra pool negative
          (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core)
          m slots J lists a (principalWindow om lo hi hlo hs negative height) X Y R y‖))≤
      C*(4:ℝ)^slots.card*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
        (SchwartzMap.seminorm ℝ 0 0 om)^2*Z^(-saving) := by
  obtain ⟨s,C,hC,hbound⟩ := global_parent_tail_aggregate_rapid Jmax Lcap tau (saving+Lcap) hLcap htau
  refine ⟨s,C,hC,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop hc Jo hJo extra pool source negative Ψ m w slots lists a
    hslots ha hΨ hw om lo hi hlo hs X M Y Z height kappa eta R hkappa hX hhi hZ hY hscale hy hyi hXcap
    hsource hextra hb₁ hb₂ hactive hcommon hquot hR
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hh := hbound p hp hg hinj hcop hc Jo hJo extra pool source negative Ψ m w slots lists a
    hslots ha hΨ hw om lo hi hlo hs X M Y Z height R hX hhi hZ hY hscale hy hyi hXcap
    hsource hextra hb₁ hb₂ hactive hcommon hquot hR
  have he : Z^kappa*Real.exp ((9/2:ℝ)*(eta*Real.log Z))=Z^(kappa+(9/2:ℝ)*eta) := by
    rw [Real.rpow_add hz,Real.rpow_def_of_pos hz ((9/2:ℝ)*eta)]
    congr 2
    ring
  have hP : Z^kappa*Real.exp ((9/2:ℝ)*(eta*Real.log Z))≤Z^Lcap := by
    rw [he]
    exact Real.rpow_le_rpow_of_exponent_le hZ hkappa
  apply (mul_le_mul_of_nonneg_left hh (by positivity)).trans
  calc
    _ ≤ Z^Lcap*(C*(4:ℝ)^slots.card*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
      (SchwartzMap.seminorm ℝ 0 0 om)^2*Z^(-(saving+Lcap))) :=
      mul_le_mul_of_nonneg_right hP (by positivity)
    _ = _ := by
      have he₂ : Z^Lcap*Z^(-(saving+Lcap))=Z^(-saving) := by
        rw [←Real.rpow_add hz]
        congr 1
        ring
      calc
        _ = C*(4:ℝ)^slots.card*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
          (SchwartzMap.seminorm ℝ 0 0 om)^2*(Z^Lcap*Z^(-(saving+Lcap))) := by ring
        _ = _ := by rw [he₂]

end SevenEighths.InverseMomentGlobalPriorityTail
end

end OAI
