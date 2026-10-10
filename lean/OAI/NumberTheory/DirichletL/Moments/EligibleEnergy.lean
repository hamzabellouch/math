import OAI.NumberTheory.DirichletL.Moments.UniformDivisorShell

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEligibleEnergy
open HeckeFamily CenteredMomentActiveDivisorShell CenteredMomentActiveAllocation
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentDivisorRowEnergy
local notation "O" => ActualEisensteinCubic.O

structure Data (ι:Type*) [Fintype ι] extends Source ι where
  M : ι→ℝ
  M_ge_one : ∀i,1≤M i
  coefficient_bound : ∀i,∀I∈slots i,‖ν i I*W i ((Ideal.absNorm I:ℝ)/P i)‖≤M i
  b₁ : ℝ
  b₂ : ℝ
  support₁ : Function.support W₁⊆Set.Iic b₁
  support₂ : Function.support W₂⊆Set.Iic b₂
  X₁_pos : 0<X₁
  X₂_pos : 0<X₂
  Y₁_pos : 0<Y₁
  Y₂_pos : 0<Y₂
  same_product : Y₁*Y₂=X₁*X₂
  rows : Finset O
  weight : O→ℝ
  weight_nonneg : ∀z∈rows,0≤weight z

variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def Data.coefficient (s:Data ι) (i:ι) (I:Ideal O) : ℂ :=
  s.ν i I*s.W i ((Ideal.absNorm I:ℝ)/s.P i)

def Data.energy (s:Data ι) (D:Ideal O) : ℝ :=
  ∑z∈s.rows,s.weight z*‖(Real.sqrt (s.X₁*s.X₂*∏i,s.P i):ℂ)⁻¹*
    maskedRectangle s.η s.m s.A z s.t s.slots s.coefficient D s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂‖^2

def Data.childEnergy (s:Data ι) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) : ℝ :=
  ∑z∈s.rows,s.weight z*
    (‖allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a s.W₁ s.W₂ s.X₁ s.X₂‖^2+
     ‖allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a s.W₁ s.W₂ s.Y₁ s.Y₂‖^2)

def Data.profileFactor (s:Data ι) : ℝ :=
  (2*(max 1 s.b₁*max 1 s.b₂))*(∏i,s.M i)^2

lemma Data.energy_nonneg (s:Data ι) (D:Ideal O) : 0≤s.energy D :=
  Finset.sum_nonneg (fun z hz=>mul_nonneg (s.weight_nonneg z hz) (sq_nonneg _))

lemma Data.child_nonneg (s:Data ι) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) : 0≤s.childEnergy D a :=
  Finset.sum_nonneg (fun z hz=>mul_nonneg (s.weight_nonneg z hz) (add_nonneg (sq_nonneg _) (sq_nonneg _)))

omit [DecidableEq ι] in
lemma Data.profile_nonneg (s:Data ι) : 0≤s.profileFactor :=by
  unfold Data.profileFactor
  exact mul_nonneg (by positivity) (sq_nonneg _)

lemma Data.reduction_pos (s:Data ι) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) : 0<formalReductionFactor D a s.P :=
  mul_pos (selectedNorm_pos D a) (Finset.prod_pos (fun i _=>s.P_pos i))

theorem actual_source_from_children (N:ℕ) (hslots:Fintype.card ι≤N) (ε:ℝ) (hε:0<ε) :
    ∃C:ℝ,0<C ∧ ∀s:Data ι,∀D:Ideal O,Squarefree D → ∀E:ℝ,0≤E →
      (∀a∈s.toSource.active D,s.childEnergy D a≤E) →
      s.energy D≤C*(Ideal.absNorm D:ℝ)^ε*s.profileFactor*E*
        ∑a∈s.toSource.active D,1/formalReductionFactor D a s.P := by
  obtain ⟨C,hC,hbound⟩:=active_raw_to_retained_energy (ι:=ι) N hslots ε hε
  refine ⟨C,hC,?_⟩
  intro s D hD E hE hchild
  have hh:=hbound s.η s.m s.A s.t s.slots s.prime s.coefficient s.M s.P
    (fun i=>zero_le_one.trans (s.M_ge_one i)) s.P_pos s.coefficient_bound D hD s.W₁ s.W₂
    s.b₁ s.b₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) s.support₁ s.support₂
    s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos rfl s.same_product s.rows s.weight s.weight_nonneg
  change s.energy D≤_ at hh
  apply hh.trans
  calc
    _≤C*(Ideal.absNorm D:ℝ)^ε*∑a∈s.toSource.active D,
        (s.profileFactor/formalReductionFactor D a s.P)*E:=by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      apply Finset.sum_le_sum
      intro a ha
      have hp:(∏i∈frozenIndices D a,s.M i)≤∏i,s.M i:=
        Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
          (fun i _=>zero_le_one.trans (s.M_ge_one i)) (fun i _ _=>s.M_ge_one i)
      apply mul_le_mul _ (hchild a ha) (s.child_nonneg D a) _
      · apply div_le_div_of_nonneg_right _ (s.reduction_pos D a).le
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left₀ (Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.M_ge_one i))) hp 2
      · exact div_nonneg s.profile_nonneg (s.reduction_pos D a).le
    _=_:=by
      simp only [div_eq_mul_inv,one_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring

lemma sqrt_sum_le {α:Type*} (S:Finset α) (f:α→ℝ) (hf:∀a∈S,0≤f a) :
    Real.sqrt (∑a∈S,f a)≤∑a∈S,Real.sqrt (f a) := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨Finset.sum_nonneg (fun a _=>Real.sqrt_nonneg _),?_⟩
  have hh:=Finset.sum_sq_le_sq_sum_of_nonneg (s:=S) (f:=fun a=>Real.sqrt (f a))
    (fun a _=>Real.sqrt_nonneg _)
  have he:(∑a∈S,Real.sqrt (f a)^2)=∑a∈S,f a:=Finset.sum_congr rfl (fun a ha=>Real.sq_sqrt (hf a ha))
  rwa [he] at hh

lemma sqrt_reciprocal (x:ℝ) (_hx:0<x) : Real.sqrt (1/x)=1/Real.sqrt x := by
  rw [Real.sqrt_div (by norm_num:0≤(1:ℝ)),Real.sqrt_one]

theorem actual_source_root_from_children (N:ℕ) (hslots:Fintype.card ι≤N) (ε:ℝ) (hε:0<ε) :
    ∃C:ℝ,0<C ∧ ∀s:Data ι,∀D:Ideal O,Squarefree D → ∀E:ℝ,0≤E →
      (∀a∈s.toSource.active D,s.childEnergy D a≤E) →
      Real.sqrt (s.energy D)≤C*Real.sqrt ((Ideal.absNorm D:ℝ)^ε)*Real.sqrt (s.profileFactor*E)*
        ∑a∈s.toSource.active D,1/Real.sqrt (formalReductionFactor D a s.P) := by
  obtain ⟨C,hC,hbase⟩:=actual_source_from_children (ι:=ι) N hslots ε hε
  refine ⟨Real.sqrt C,Real.sqrt_pos.mpr hC,?_⟩
  intro s D hD E hE hc
  have hp:0≤(Ideal.absNorm D:ℝ)^ε:=Real.rpow_nonneg (Nat.cast_nonneg _) _
  have he:0≤s.profileFactor*E:=mul_nonneg s.profile_nonneg hE
  have hs:=sqrt_sum_le (s.toSource.active D) (fun a=>1/formalReductionFactor D a s.P)
    (fun a _=>div_nonneg zero_le_one (s.reduction_pos D a).le)
  simp_rw [sqrt_reciprocal _ (s.reduction_pos D _)] at hs
  have hh:=Real.sqrt_le_sqrt (hbase s D hD E hE hc)
  have hrew:C*(Ideal.absNorm D:ℝ)^ε*s.profileFactor*E*
      (∑a∈s.toSource.active D,1/formalReductionFactor D a s.P)=
      (C*(Ideal.absNorm D:ℝ)^ε*(s.profileFactor*E))*
      (∑a∈s.toSource.active D,1/formalReductionFactor D a s.P):=by ring
  rw [hrew,Real.sqrt_mul (mul_nonneg (mul_nonneg hC.le hp) he),
    Real.sqrt_mul (mul_nonneg hC.le hp),Real.sqrt_mul hC.le] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hs (by positivity))

end SevenEighths.CenteredMomentEligibleEnergy

end

end OAI
