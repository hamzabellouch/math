import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPair
import OAI.NumberTheory.DirichletL.Moments.ExceptionalAsymmetricSource

namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalCommon
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentExceptionalAmplitudePair
open CenteredMomentExceptionalAllocationShell CenteredMomentExceptionalWholeSource
open CenteredMomentExceptionalMaskedSource UniqueFactorizationMonoid CenteredMomentDivisorExtraction
open CenteredMomentDivisorRectangle CenteredMomentExceptionalAsymmetricSource
open CenteredMomentFiniteProfileExceptional
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u} [Fintype ι] [DecidableEq ι]

def profileMass {lo hi:ℝ} (R:Finset (ℕ×ℕ))
    {α κ:Type u} [Fintype α] [Fintype κ] [DecidableEq α] [DecidableEq κ]
    (s:Data α)(v:Data κ)(p q:Profiles lo hi)(J:ℕ):ℝ:=
  p.control R*q.control R*(1+‖s.t‖)^J*(1+‖v.t‖)^J*slotControl s*slotControl v*
    Real.sqrt (volume s)*Real.sqrt (volume v)

lemma profileMass_nonneg {lo hi:ℝ} (R:Finset (ℕ×ℕ))
    {α κ:Type u} [Fintype α] [Fintype κ] [DecidableEq α] [DecidableEq κ]
    (s:Data α)(v:Data κ)(p q:Profiles lo hi)(J:ℕ):0≤profileMass R s v p q J:=by
  have hp:=Profiles.control_nonneg p R
  have hq:=Profiles.control_nonneg q R
  have hs:=slotControl_nonneg s
  have hv:=slotControl_nonneg v
  unfold profileMass
  positivity

theorem actual_paired_asymmetric (lo hi ε B:ℝ) (hlo:0<lo) (hhi:0≤hi) (hε:0<ε) (hB:0≤B):
    ∃J:ℕ,∃R:Finset (ℕ×ℕ),(0,0)∈R ∧ ∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧
      ∀(ι κ:Type u) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ],
      ∀(s:Data ι)(v:Data κ)(p q:Profiles lo hi)(Z r rRight:ℝ),1<Z → ∀z:O,
      ProfileAdmissible s p Q Z B r z → ProfileAdmissible v q Q Z B rRight z →
      ∀(D:Ideal O)(a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
        (b:Allocation D (Finset.univ:Finset (κ⊕Fin 2))),
      ‖amplitude s D a z‖*‖amplitude v D b z‖≤
        C*p.control R*q.control R*Z^(2*ε)*(1+‖s.t‖)^J*(1+‖v.t‖)^J*
          slotControl s*slotControl v*Real.sqrt (volume s)*Real.sqrt (volume v)*
            exceptionalWeight s.toSource v.toSource D a b Z r:=by
  obtain ⟨J,R,hR,hJ⟩:=allocated_amplitude_source_control lo hi ε B hlo hhi hε hB
  refine ⟨J,R,hR,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hbound⟩:=hJ Q hQ
  refine ⟨C^2,sq_pos_of_pos hC,?_⟩
  intro ι κ _ _ _ _ s v p q Z r rRight hZ z hs hv D a b
  have hpoint (α:Type u) [Fintype α] [DecidableEq α] (s:Data α)(p:Profiles lo hi)(r0:ℝ)
      (hs:ProfileAdmissible s p Q Z B r0 z)(a:Allocation D (Finset.univ:Finset (α⊕Fin 2))):
      ‖amplitude s D a z‖≤C*p.control R*Z^ε*(1+‖s.t‖)^J*slotControl s*Real.sqrt (volume s)/
        (formalReductionFactor D a s.P*Z^(max (r0-Real.logb Z (formalReductionFactor D a s.P)) 0)):=by
    have hpc := Profiles.control_nonneg p R
    obtain ⟨hP,hm,hA,hz,hml,hm2,hcond,hex,hW₁,hW₂,hX₁,hX₂,hY₁,hY₂⟩:=hs
    apply norm_le_of_squared _ _ _ _ _
    · exact mul_nonneg (by positivity) (slotControl_nonneg s)
    · exact (volume_pos s).le
    · exact s.reduction_pos D a
    · exact Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
    · exact hbound (p.profile 0) (p.profile 1) (p.support 0) (p.support 1)
        α s Z hZ hP z hm hA hz hml hm2 hcond hex D a r0 hW₁ hW₂ hX₁ hX₂ hY₁ hY₂

  have hpc := Profiles.control_nonneg p R
  have hqc := Profiles.control_nonneg q R
  have hl:=hpoint ι s p r hs a
  have hr:=hpoint κ v q rRight hv b
  have hcap:1≤Z^(max (rRight-Real.logb Z (formalReductionFactor D b v.P)) 0):=
    Real.one_le_rpow hZ.le (le_max_right _ _)
  have hr':‖amplitude v D b z‖≤
      C*q.control R*Z^ε*(1+‖v.t‖)^J*slotControl v*Real.sqrt (volume v)/formalReductionFactor D b v.P:=by
    apply hr.trans
    apply div_le_div_of_nonneg_left
      (mul_nonneg (mul_nonneg (by positivity) (slotControl_nonneg v)) (Real.sqrt_nonneg _))
      (v.reduction_pos D b)
    exact le_mul_of_one_le_right (v.reduction_pos D b).le hcap
  apply (mul_le_mul hl hr' (norm_nonneg _) (by
    exact div_nonneg (mul_nonneg (mul_nonneg (by positivity)
      (slotControl_nonneg s)) (Real.sqrt_nonneg _)) (mul_nonneg (s.reduction_pos D a).le (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)))).trans_eq
  rw [←reduction_cap_identity s v D a b Z r hZ]
  have hp:Z^(2*ε)=(Z^ε)^2:=by rw [mul_comm (2:ℝ) ε,Real.rpow_mul (zero_lt_one.trans hZ).le,Real.rpow_two]
  rw [hp]
  ring

theorem actual_paired_capped (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(ε B:ℝ) (hε:0<ε) (hB:0≤B):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧
      ∀(α κ:Type u) [Fintype α] [Fintype κ] [DecidableEq α] [DecidableEq κ],
      ∀(s:Data α)(v:Data κ)(p q:Profiles wlo whi)(Z r rRight:ℝ),1<Z → ∀z:O,
      ProfileAdmissible s p Q Z B r z → ProfileAdmissible v q Q Z B rRight z →
      ∀(D:Ideal O)(a:Allocation D (Finset.univ:Finset (α⊕Fin 2)))
        (b:Allocation D (Finset.univ:Finset (κ⊕Fin 2))),
      ‖amplitude s D a z‖*‖amplitude v D b z‖≤
        C*p.control Sprofile*q.control Sprofile*Z^(2*ε)*(1+‖s.t‖)^J*(1+‖v.t‖)^J*
          slotControl s*slotControl v*Real.sqrt (volume s)*Real.sqrt (volume v)*
            exceptionalWeight s.toSource v.toSource D a b Z (max r 0):=by
  obtain ⟨J,Sprofile,hSprofile,hJ⟩:=actual_paired_asymmetric wlo whi ε B hwlo hwhi hε hB
  refine ⟨J,Sprofile,hSprofile,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hbound⟩:=hJ Q hQ
  refine ⟨C,hC,?_⟩
  intro α κ _ _ _ _ s v p q Z r rRight hZ z hs hv D a b
  rw [←raw_cap_weight s v hs.1 D a b Z r hZ]
  exact hbound α κ s v p q Z r rRight hZ z hs hv D a b

theorem actual_whole_asymmetric (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(ε δ B Lbound:ℝ)
    (hε:0<ε)(hδ:0<δ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(I L:Finset ι)(s:Data I)(v:Data L)(p q:Profiles wlo whi),
      (∀i:L,v.lo i=lo i) → (∀i:L,v.hi i=hi i) →
      ∀r rRight:ℝ,∀rows:Finset O,(∀z∈rows,ProfileAdmissible s p Q Z B r z) →
      (∀z∈rows,ProfileAdmissible v q Q Z B rRight z) →
      ∀Ds:Finset (Ideal O),(∀D∈Ds,(moebius D:ℂ)≠0 → (D.absNorm:ℝ)≤Z^Lbound) →
      (∑D∈Ds,‖(moebius D:ℂ)‖*
        ∑a∈s.toSource.active D,∑b∈v.toSource.active D,
          ∑z∈rows,‖amplitude s D a z‖*‖amplitude v D b z‖)≤
        C*(rows.card:ℝ)*Z^(2*ε+δ-max r 0)*profileMass Sprofile s v p q J:=by
  obtain ⟨J,Sprofile,hSprofile,hJ⟩:=actual_paired_capped wlo whi hwlo hwhi ε B hε hB
  obtain ⟨Cs,hCs,hmass⟩:=whole_weight_bound lo hi Lbound δ hL hδ
  refine ⟨J,Sprofile,hSprofile,?_⟩
  intro Q hQ
  obtain ⟨Ca,hCa,hpoint⟩:=hJ Q hQ
  refine ⟨Ca*Cs,mul_pos hCa hCs,?_⟩
  filter_upwards [hmass] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro I L s v p q hlo hhi r rRight rows hs hv Ds hDs
  have hz:=zero_lt_one.trans hZ.1
  let A:ℝ:=Ca*(rows.card:ℝ)*Z^(2*ε)*profileMass Sprofile s v p q J
  have hA:0≤A:=mul_nonneg (by positivity) (profileMass_nonneg Sprofile s v p q J)
  have hterm (D:Ideal O)(a:CenteredMomentDivisorAllocation.Allocation D (Finset.univ:Finset (I⊕Fin 2)))
      (b:CenteredMomentDivisorAllocation.Allocation D (Finset.univ:Finset (L⊕Fin 2))):
      (∑z∈rows,‖amplitude s D a z‖*‖amplitude v D b z‖)≤
        A*exceptionalWeight s.toSource v.toSource D a b Z (max r 0):=by
    calc
      _≤∑z∈rows,Ca*Z^(2*ε)*profileMass Sprofile s v p q J*
          exceptionalWeight s.toSource v.toSource D a b Z (max r 0):=by
        apply Finset.sum_le_sum
        intro z hzrow
        exact (hpoint I L s v p q Z r rRight hZ.1 z (hs z hzrow) (hv z hzrow) D a b).trans_eq
          (by dsimp [profileMass];ring)
      _=_:=by simp only [Finset.sum_const, nsmul_eq_mul];dsimp [A];ring
  calc
    _≤∑D∈Ds,‖(moebius D:ℂ)‖*
        ∑a∈s.toSource.active D,∑b∈v.toSource.active D,
          A*exceptionalWeight s.toSource v.toSource D a b Z (max r 0):=by
      apply Finset.sum_le_sum
      intro D hD
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Finset.sum_le_sum (fun a _=>Finset.sum_le_sum (fun b _=>hterm D a b))
    _=A*(∑D∈Ds,‖(moebius D:ℂ)‖*
        ∑a∈s.toSource.active D,∑b∈v.toSource.active D,
          exceptionalWeight s.toSource v.toSource D a b Z (max r 0)):=by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro D hD
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _≤A*(Cs*Z^(δ-max r 0)):=mul_le_mul_of_nonneg_left (hZ.2 I L s.toSource v.toSource hlo hhi Ds hDs (max r 0)) hA
    _=_:=by
      rw [show 2*ε+δ-max r 0=2*ε+(δ-max r 0) by ring,Real.rpow_add hz]
      dsimp [A]
      ring

theorem actual_masked_asymmetric (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(ε δ B Lbound:ℝ)
    (hε:0<ε)(hδ:0<δ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(I L:Finset ι)(s:Data I)(v:Data L)(p q:Profiles wlo whi),
      (∀i:L,v.lo i=lo i) → (∀i:L,v.hi i=hi i) →
      ∀r rRight:ℝ,∀rows:Finset O,(∀z∈rows,ProfileAdmissible s p Q Z B r z) →
      (∀z∈rows,ProfileAdmissible v q Q Z B rRight z) →
      ∀Ds:Finset (Ideal O),(∀D∈Ds,(moebius D:ℂ)≠0 → (D.absNorm:ℝ)≤Z^Lbound) →
      (∑D∈Ds,‖(moebius D:ℂ)‖*∑z∈rows,
        ‖maskedAmplitude s D z‖*‖maskedAmplitude v D z‖)≤
        C*(rows.card:ℝ)*Z^(2*ε+δ-max r 0)*profileMass Sprofile s v p q J:=by
  obtain ⟨J,Sprofile,hSprofile,hJ⟩:=actual_whole_asymmetric wlo whi hwlo hwhi lo hi ε δ B Lbound hε hδ hB hL
  refine ⟨J,Sprofile,hSprofile,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hCZ⟩:=hJ Q hQ
  refine ⟨C,hC,?_⟩
  filter_upwards [hCZ] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro I L s v p q hlo hhi r rRight rows hs hv Ds hDs
  exact (whole_masked_le s v Ds rows).trans (hZ.2 I L s v p q hlo hhi r rRight rows hs hv Ds hDs)

end SevenEighths.CenteredMomentFiniteProfileExceptionalCommon

end

end OAI
