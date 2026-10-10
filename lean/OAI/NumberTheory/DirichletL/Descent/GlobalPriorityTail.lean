import OAI.NumberTheory.DirichletL.Descent.GlobalPriorityTailMass
import OAI.NumberTheory.DirichletL.Descent.GlobalPriorityTailCollapse

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

theorem global_parent_tail_rapid (Jmax : ℕ) (Lcap tau saving : ℝ)
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
      (ray : RayCharacter×RayCharacter)(core : FirstCoreIndex)
      (w : Source ι Jo→ℂ)(slots J : Finset σ)(lists : σ→Finset ι)(a : σ→ι→ℂ),
      J⊆slots → (slots:Set σ).PairwiseDisjoint lists →
      (∀i∈slots,∀k∈lists i,‖a i k‖≤1) → (∀u,‖Ψ u‖≤1) → (∀x∈source,‖w x‖≤1) →
      ∀(om : 𝓢(ℝ,ℂ))(lo hi : ℝ)(hlo : 0<lo)(hs : Function.support om⊆Set.Icc lo hi)
      (X M Y Z height : ℝ)(R : Finset ι→Finset ι→ℝ),
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
      ‖∑y∈wholeAssignedParents p (fun x=>extra x.cube) source negative J lists,
        coefficient p J a (globalPriorityOuter p hg negative Ψ m ray core w) y*
        priorityTailParent p hg hp hinj extra pool negative
          (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core)
          m slots J lists a (principalWindow om lo hi hlo hs negative height) X Y R y‖≤
      C*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
        (SchwartzMap.seminorm ℝ 0 0 om)^2*Z^(-saving) := by
  obtain ⟨s,Ct,hCt,htail⟩ := priority_tail_parent_uniform Lcap tau (saving+13*Lcap) hLcap htau
  obtain ⟨Cm,hCm,hmark⟩ := finite_primeMark_small_power (1/2) (by norm_num)
  obtain ⟨Cs,hCs,hmass⟩ := original_tail_mass Jmax
  have hCb : 0<coefficientBound := coefficientBound_pos
  refine ⟨s,coefficientBound*Cm^2*Ct*Cs,by positivity,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop hc Jo hJo extra pool source negative Ψ m ray core w slots J lists a
    hJ hslots ha hΨ hw om lo hi hlo hs X M Y Z height R hX hhi hZ hY hscale hy hyi hXcap
    hsource hextra hb₁ hb₂ hactive hcommon hquot hR
  have hz : 0<Z := zero_lt_one.trans_le hZ
  let Ψ₀ := firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
  let V := principalWindow om lo hi hlo hs negative height
  let Q := (s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*(SchwartzMap.seminorm ℝ 0 0 om)^2
  let T := Ct*Q*Z^(-(saving+13*Lcap))
  have hT : 0≤T := by dsimp [T,Q];positivity
  have hΨ₀ : ∀u,‖Ψ₀ u‖≤1 := fun u=>(firstCoreTwist_norm_le negative _ Ψ core u).trans (hΨ u)
  have hout (x : Source ι Jo) (hx : x∈source) :
      ‖globalPriorityOuter p hg negative Ψ m ray core w x‖≤coefficientBound := by
    rw [globalPriorityOuter,norm_mul]
    exact (mul_le_mul (hw x hx)
      (priorityOuter_norm p hg x.cube negative Ψ m (fun _=>1) ray core x.quotientSupport
        (by simp) (hΨ _)) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hm (x : Source ι Jo) :
      ‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2≤
        Cm^2*primeProductNorm p (principalSupport extra negative x) := by
    have hh := hmark p hp hcop J lists a
      (fun i hi j hj hij=>hslots (hJ hi) (hJ hj) hij) (fun i hi=>ha i (hJ hi))
      (principalSupport extra negative x)
    have he : ((primeProductNorm p (principalSupport extra negative x))^(1/2:ℝ))^2=
        primeProductNorm p (principalSupport extra negative x) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul (primeProductNorm_pos p hp _).le]
      norm_num
    have hsupp : wholeExtractedSupport (fun x=>extra x.cube) negative x=principalSupport extra negative x := by
      simp only [wholeExtractedSupport,extractedSupport,principalSupport,Finset.union_assoc]
    rw [hsupp]
    exact (pow_le_pow_left₀ (norm_nonneg _) hh 2).trans_eq (by rw [mul_pow,he])
  have ht (x : Source ι Jo) (hx : x∈source) :
      ‖priorityTailParent p hg hp hinj extra pool negative Ψ₀ m slots J lists a V X Y R (parent p x)‖≤T := by
    simpa only [T,Q,mul_assoc] using htail p hp hg hinj hcop hc extra pool negative Ψ₀ m slots J lists a
      hslots ha hΨ₀ om lo hi hlo hs X M Y Z height R hX hhi hZ hY hscale hy hyi hXcap
      (parent p x) (hR x hx)
  have hmass₀ := hmass p hp hinj Jo hJo source Z Lcap hZ hLcap hsource hb₁ hb₂ hactive hcommon hquot extra negative hextra
  rw [original_paired_tail p hg hp hinj]
  calc
    _ ≤ ∑x∈source,‖globalPriorityOuter p hg negative Ψ m ray core w x*
      (‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      priorityTailParent p hg hp hinj extra pool negative Ψ₀ m slots J lists a V X Y R (parent p x)‖ := norm_sum_le _ _
    _ ≤ ∑x∈source,coefficientBound*(Cm^2*primeProductNorm p (principalSupport extra negative x))*T := by
      apply Finset.sum_le_sum
      intro x hx
      rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)]
      exact mul_le_mul (mul_le_mul (hout x hx) (hm x) (sq_nonneg _) coefficientBound_pos.le)
        (ht x hx) (norm_nonneg _)
        (mul_nonneg hCb.le (mul_nonneg (sq_nonneg _) (primeProductNorm_pos p hp _).le))
    _ = coefficientBound*Cm^2*T*(∑x∈source,primeProductNorm p (principalSupport extra negative x)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intros
      ring
    _ ≤ coefficientBound*Cm^2*T*(Cs*Z^(13*Lcap)) :=
      mul_le_mul_of_nonneg_left hmass₀ (by positivity)
    _ = _ := by
      have he : Z^(-(saving+13*Lcap))*Z^(13*Lcap)=Z^(-saving) := by
        rw [←Real.rpow_add hz]
        congr 1
        ring
      dsimp only [T,Q]
      calc
        _ = coefficientBound*Cm^2*Ct*Cs*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
          (SchwartzMap.seminorm ℝ 0 0 om)^2*(Z^(-(saving+13*Lcap))*Z^(13*Lcap)) := by ring
        _ = _ := by rw [he]

end SevenEighths.InverseMomentGlobalPriorityTail
end

end OAI
