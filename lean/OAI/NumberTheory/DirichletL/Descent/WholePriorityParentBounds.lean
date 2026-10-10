import OAI.NumberTheory.DirichletL.Descent.WholePriorityMass

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InverseSecondPrincipalCaller InversePrincipalEnergy InversePrioritySecondSource
local notation "O"=>ActualEisensteinCubic.O

variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

omit [DecidableEq σ] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem parent_residual_lists_subset {Jo:ℕ} (extra:CubeCoordinates ι→Finset ι)
    (negative:Bool) (lists:σ→Finset ι) (y:SecondParentSource ι Jo) (i:σ):
    residualLists p negative (fun i=>lists i\extra y.cube) y i⊆lists i:=
by
  intro k hk
  exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hk).1).1

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem parent_residual_lists_pairwise {Jo:ℕ} (extra:CubeCoordinates ι→Finset ι)
    (negative:Bool) (slots assigned:Finset σ) (lists:σ→Finset ι) (y:SecondParentSource ι Jo)
    (hslots:(slots:Set σ).PairwiseDisjoint lists):
    ((slots\assigned:Finset σ):Set σ).PairwiseDisjoint (residualLists p negative (fun i=>lists i\extra y.cube) y):=by
  intro i hi j hj hij
  exact (hslots (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hj).1 hij).mono
    (parent_residual_lists_subset p extra negative lists y i)
    (parent_residual_lists_subset p extra negative lists y j)

theorem priority_zero_parent_uniform (ε:ℝ) (hε:0<ε):
    ∃(s:Finset (ℕ×ℕ))(C:ℝ),0<C ∧
    ∀{ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
      (p:ι→O) (_hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι) (negative:Bool)
      (Ψ:O→*ℂ) (m:O) (slots assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ),
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) → (∀u,‖Ψ u‖≤1) →
    ∀(om:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hs:Function.support om⊆Set.Icc lo hi)
      (X M Y t:ℝ)(R:Finset ι→Finset ι→ℝ),
      0<X → hi≤Real.exp M → 1≤Y → (∀G E,0≤R G E) →
    ∀{Jo:ℕ}(y:SecondParentSource ι Jo),
      ‖priorityZeroParent p hg extra pool negative Ψ m slots assigned lists a
        (principalWindow om lo hi hlo hs negative t) X Y R y‖≤
      C*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*(SchwartzMap.seminorm ℝ 0 0 om)^2*
        Y*(X*Real.exp M)^(1+ε):=by
  obtain ⟨s,C,hC,hbound⟩:=marked_principal_energy ε hε
  refine ⟨s,C,hC,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop extra pool negative Ψ m slots assigned lists a hslots ha hΨ
    om lo hi hlo hs X M Y t R hX hhi hY hR Jo y
  have hpair:=parent_residual_lists_pairwise p extra negative slots assigned lists y hslots
  have hcoeff:∀i∈slots\assigned,∀k∈residualLists p negative (fun i=>lists i\extra y.cube) y i,‖a i k‖≤1:=by
    intro i hi k hk
    exact ha i (Finset.mem_sdiff.mp hi).1 k (parent_residual_lists_subset p extra negative lists y i hk)
  have hz:∀G∈pool.powerset,∀E∈G.powerset,(0:O)∈secondVariableCutoff p y R G E:=by
    intro G hG E hE
    exact zero_mem_childFrequencyBall _
      (mul_ne_zero (primeSubsetGenerator_ne_zero _ _) (primeSubsetGenerator_ne_zero _ _)) _ (hR G E)
  have hb:=hbound p hp hg hinj hcop (slots\assigned)
    (residualLists p negative (fun i=>lists i\extra y.cube) y) a hpair hcoeff ∅ pool Ψ hΨ
    (secondParentPuncture p m y) (secondParentLabel p y) (secondParentDivisor p y)
    (principalWindow om lo hi hlo hs negative t) rowMajorant X M Y hX hY
    (principalWindow_upper om lo hi hlo hs M hhi negative t) (secondVariableCutoff p y R) hz
    (fun _ _ _=>0) (by intros; simp)
  have hb':‖priorityZeroParent p hg extra pool negative Ψ m slots assigned lists a
      (principalWindow om lo hi hlo hs negative t) X Y R y‖≤_:=
    (le_add_of_nonneg_right (norm_nonneg _)).trans hb
  simpa only [Finset.card_empty,pow_zero,mul_one,principalWindow_seminorm_zero,mul_assoc] using hb'

theorem priority_tail_parent_uniform (Lcap tau saving:ℝ)(hLcap:0≤Lcap)(htau:0<tau):
    ∃(s:Finset (ℕ×ℕ))(C:ℝ),0<C ∧
    ∀{ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι) (negative:Bool)
      (Ψ:O→*ℂ) (m:O) (slots assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ),
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) → (∀u,‖Ψ u‖≤1) →
    ∀(om:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hs:Function.support om⊆Set.Icc lo hi)
      (X M Y Z t:ℝ)(R:Finset ι→Finset ι→ℝ),
      0<X → hi≤Real.exp M → 1≤Z → 0<Y → 1≤X*Real.exp M →
      Y≤Z^Lcap → Y⁻¹≤Z^Lcap → X*Real.exp M≤Z^Lcap →
    ∀{Jo:ℕ}(y:SecondParentSource ι Jo),
      (∀G∈pool.powerset,∀E:G.powerset,
        correlatedSecondRadius p (secondParentDivisor p y) G E.val (X*Real.exp M) Y (Z^tau)≤R G E.val) →
      ‖priorityTailParent p hg hp hinj extra pool negative Ψ m slots assigned lists a
        (principalWindow om lo hi hlo hs negative t) X Y R y‖≤
      C*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*(SchwartzMap.seminorm ℝ 0 0 om)^2*Z^(-saving):=by
  obtain ⟨s,C,hC,hbound⟩:=InverseWholePriorityRapidTail.marked_rapid_tail Lcap tau saving hLcap htau
  refine ⟨s,C,hC,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop hc extra pool negative Ψ m slots assigned lists a hslots ha hΨ
    om lo hi hlo hs X M Y Z t R hX hhi hZ hY hscale hy hyi hx Jo y hR
  have hpair:=parent_residual_lists_pairwise p extra negative slots assigned lists y hslots
  have hcoeff:∀i∈slots\assigned,∀k∈residualLists p negative (fun i=>lists i\extra y.cube) y i,‖a i k‖≤1:=by
    intro i hi k hk
    exact ha i (Finset.mem_sdiff.mp hi).1 k (parent_residual_lists_subset p extra negative lists y i hk)
  exact hbound p hp hcop hg hinj hc pool Ψ hΨ (secondParentPuncture p m y)
    (secondParentLabel p y) (secondParentDivisor p y) (primeSubsetGenerator_ne_zero _ _)
    (slots\assigned) _ a hpair hcoeff om rowMajorant lo hi hlo hs negative t X M Y Z R
    hX hhi hZ hY hscale hy hyi hx hR

end SevenEighths.InverseMoment

end

end OAI
