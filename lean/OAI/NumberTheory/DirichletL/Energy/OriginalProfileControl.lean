import OAI.NumberTheory.DirichletL.Energy.NaturalInputMatches
import OAI.NumberTheory.DirichletL.Energy.ZeroComparison
import OAI.NumberTheory.DirichletL.Moments.FirstReferenceEnergy
import OAI.NumberTheory.DirichletL.Moments.SourceInputTailUniform

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyOriginalProfileControl
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentFiniteProfileExceptional
open CenteredMomentSourceInputTailUniform CenteredMomentFirstReferenceEnergy
open CenteredMomentEnergyZeroComparison CenteredMomentEnergyNaturalInputMatches
open CenteredMomentEnergyState CenteredMomentFirstCanonicalFamily CenteredMomentFirstPhysicalSource
variable {ι:Type*}[Fintype ι][DecidableEq ι]

omit [DecidableEq ι] in
lemma slot_product_le (s:Input ι)(N:ℕ)(C:ℝ)(hC:1≤C)
    (hN:Fintype.card ι≤N)(hM:∀i,s.M i≤C): (∏i,s.M i)≤C^N := by
  calc
    _≤∏_i:ι,C:=Finset.prod_le_prod₀ (fun i _=>(s.M_ge_one i).trans' zero_le_one) (fun i _=>hM i)
    _=C^(Fintype.card ι):=by simp
    _≤C^N:=pow_le_pow_right₀ hC hN

omit [DecidableEq ι] in
lemma plain_control_le {a b:ℝ}(s:Input ι)(p:Profiles a b)(S:Finset (ℕ×ℕ))
    (N:ℕ)(C:ℝ)(hC:1≤C)(hN:Fintype.card ι≤N)(hM:∀i,s.M i≤C):
    plainControl s (p.profile 0) (p.profile 1)≤C^N*p.control (insert (0,0) S) := by
  have h0 (i:Fin 2):SchwartzMap.seminorm ℝ 0 0 (p.profile i)≤
      sourceControl (insert (0,0) S) (p.profile i):=
    Seminorm.le_finset_sup_apply (p:=schwartzSeminormFamily ℝ ℝ ℂ)
      (s:=insert (0,0) S) (i:=(0,0)) (x:=p.profile i) (Finset.mem_insert_self _ _)
  have hpair:=mul_le_mul (h0 0) (h0 1) (apply_nonneg _ _) (sourceControl_nonneg _ _)
  have hh:=mul_le_mul (slot_product_le s N C hC hN hM) hpair
    (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)) (pow_nonneg (by linarith) _)
  simpa only [plainControl,Profiles.control,mul_assoc] using hh

omit [DecidableEq ι] in
lemma plain_control_sq_le {a b:ℝ}(s:Input ι)(p:Profiles a b)(S:Finset (ℕ×ℕ))
    (N:ℕ)(C:ℝ)(hC:1≤C)(hN:Fintype.card ι≤N)(hM:∀i,s.M i≤C):
    (plainControl s (p.profile 0) (p.profile 1))^2≤C^(2*N)*(p.control (insert (0,0) S))^2 := by
  have hh:=pow_le_pow_left₀ (plainControl_nonneg _ _ _) (plain_control_le s p S N C hC hN hM) 2
  simpa only [mul_pow,←pow_mul,Nat.mul_comm N 2] using hh

omit [DecidableEq ι] in
lemma zero_plain_control (s:Input ι)(hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)(W₁ W₂:𝓢(ℝ,ℂ)):
    plainControl (zeroInput s hz₁ hz₂) W₁ W₂=plainControl s W₁ W₂:=rfl

omit [DecidableEq ι] in
lemma lower_product (s:Input ι)(N:ℕ)(a:ℝ)(ha:0<a)
    (hN:Fintype.card ι≤N)(hlo:∀i,a≤s.lo i):
    (min 1 a)^N≤∏i,s.lo i := by
  have hm:0≤min 1 a:=le_min zero_le_one ha.le
  calc
    _≤(min 1 a)^(Fintype.card ι):=pow_le_pow_of_le_one hm (min_le_left _ _) hN
    _=∏_i:ι,min 1 a:=by simp
    _≤∏i,s.lo i:=Finset.prod_le_prod₀ (fun _ _=>hm) (fun i _=>(min_le_right _ _).trans (hlo i))

omit [DecidableEq ι] in
lemma source_factor_le (s:Input ι)(N:ℕ)(aslot a K:ℝ)(hs:0<aslot)(ha:0<a)(hK:0<K)
    (hN:Fintype.card ι≤N)(hlo:∀i,aslot≤s.lo i):
    sourceFactor s a a K≤
      (Real.exp (Real.log 4)*fixedPresentationCost/((min 1 aslot)^N*a*a))*K*(s.η.modulus.absNorm:ℝ) := by
  have hd:0<(min 1 aslot)^N*a*a:=by positivity
  have hprod:=lower_product s N aslot hs hN hlo
  have hden:(min 1 aslot)^N*a*a≤(∏i,s.lo i)*a*a:=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hprod ha.le) ha.le
  have hdiv:=div_le_div_of_nonneg_left (Real.exp_pos (Real.log 4)).le hd hden
  have hc:=fixedPresentationCost_pos
  have hn:0≤(s.η.modulus.absNorm:ℝ):=Nat.cast_nonneg _
  have hh:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hdiv hc.le) hK.le) hn
  unfold sourceFactor
  convert hh using 1 ; ring

local notation "O"=>HeckeFamily.O
section Input
variable {ι : Type*} [Fintype ι]
variable (Q : Ideal O) [NeZero Q]
local instance : Finite (O ⧸ Q) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne Q)
variable (H : Subgroup (O ⧸ Q)ˣ) (hH : RayOrthogonality.globalUnits Q ≤ H)
variable (η₀ : Character) (θ : ι → RayQuotient.Characters Q H)
variable (W : ℝ → ℂ) (hW : Continuous W)
variable (aslot bslot lo hi : ℝ) (haslot : 0 < aslot)
variable (hWs : Function.support W ⊆ Set.Icc aslot bslot)
variable (w σ freq : ι → ℝ) (hσ : ∀ i, σ i ∈ Set.Icc lo hi)
variable {Z Bmask bΦ a b : ℝ}
variable (state : NaturalState Z Bmask bΦ) (p : Profiles a b) (ha : 0 < a)
variable (t X₁ X₂ Y₁ Y₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
variable (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) (hsame : Y₁ * Y₂ = X₁ * X₂)

local notation "inp" => CenteredMomentEnergyNaturalInputMatches.input Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
  w σ freq hσ state p ha t X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hsame

theorem natural_plain_control (N:ℕ)(hN:Fintype.card ι≤N)(S:Finset (ℕ×ℕ)):
    (plainControl inp (p.profile 0) (p.profile 1))^2≤
      (profileBound W hW aslot bslot lo hi haslot hWs)^(2*N)*
        (p.control (insert (0,0) S))^2 :=
  plain_control_sq_le inp p S N _
    (profileBound_ge_one W hW aslot bslot lo hi haslot hWs) hN (fun _=>le_refl _)

theorem natural_zero_plain_control (N:ℕ)(hN:Fintype.card ι≤N)(S:Finset (ℕ×ℕ))
    (hz₁:(inp).W₁ 0=0)(hz₂:(inp).W₂ 0=0):
    (plainControl (zeroInput inp hz₁ hz₂) (p.profile 0) (p.profile 1))^2≤
      (profileBound W hW aslot bslot lo hi haslot hWs)^(2*N)*
        (p.control (insert (0,0) S))^2 :=
  plain_control_sq_le (zeroInput inp hz₁ hz₂) p S N _
    (profileBound_ge_one W hW aslot bslot lo hi haslot hWs) hN (fun _=>le_refl _)

theorem natural_source_factor (N:ℕ)(hN:Fintype.card ι≤N)(K:ℝ)(hK:0<K):
    sourceFactor inp a a K≤
      (Real.exp (Real.log 4)*fixedPresentationCost/((min 1 aslot)^N*a*a))*K*
        (state.character.modulus.absNorm:ℝ) :=
  source_factor_le inp N aslot a K haslot ha hK hN (fun _=>le_refl _)

theorem natural_zero_source_factor (N:ℕ)(hN:Fintype.card ι≤N)(K:ℝ)(hK:0<K)
    (hz₁:(inp).W₁ 0=0)(hz₂:(inp).W₂ 0=0):
    sourceFactor (zeroInput inp hz₁ hz₂) a a K≤
      (Real.exp (Real.log 4)*fixedPresentationCost/((min 1 aslot)^N*a*a))*K*
        (state.character.modulus.absNorm:ℝ) :=
  source_factor_le (zeroInput inp hz₁ hz₂) N aslot a K haslot ha hK hN (fun _=>le_refl _)

end Input
end SevenEighths.CenteredMomentEnergyOriginalProfileControl

end

end OAI
