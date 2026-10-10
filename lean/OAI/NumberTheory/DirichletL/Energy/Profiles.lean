import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalStability
import OAI.NumberTheory.DirichletL.Moments.ScaleSupremum

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentEnergyProfiles
open CenteredMomentFiniteProfileExceptional CenteredMomentAllocatedNaturalSource
open CenteredMomentScaleSupremum

structure Test (a b:ℝ) where
  profile : 𝓢(ℝ,ℂ)
  support : Function.support (profile:ℝ→ℂ)⊆Set.Icc a b

def lower (a b:ℝ):ℕ→ℝ
  | 0=>a
  | n+1=>lower a b n/max 1 b

lemma lower_pos (a b:ℝ)(ha:0<a)(n:ℕ):0<lower a b n:=by
  induction n with
  | zero=>exact ha
  | succ n ih=>exact div_pos ih (lt_of_lt_of_le zero_lt_one (le_max_left _ _))

def derivativeChoice (W:𝓢(ℝ,ℂ))(j:Fin 2):𝓢(ℝ,ℂ):=
  if j=0 then W else DetectorDictionaryInverseUniform.scaleCLM W

lemma derivativeChoice_apply (W:𝓢(ℝ,ℂ))(j:Fin 2):
    (derivativeChoice W j:ℝ→ℂ)=scaleTest W j:=by
  unfold derivativeChoice scaleTest
  split_ifs
  · rfl
  · exact funext (DetectorDictionaryInverseUniform.scaleCLM_apply W)

lemma derivativeChoice_support (a b:ℝ)(W:𝓢(ℝ,ℂ))
    (hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b)(j:Fin 2):
    Function.support (derivativeChoice W j:ℝ→ℂ)⊆Set.Icc a b:=by
  rw [derivativeChoice_apply]
  exact scaleTest_support W a b hs j

def step (a b:ℝ)(ha:0<a)(W:Test a b)(U:ℝ)(hU:0<U)(t:ℝ)(j:Fin 2):
    Test (a/max 1 b) b where
  profile:=derivativeChoice ((sourcePlain a b ha W.profile W.support).profile U hU t) j
  support:=derivativeChoice_support _ _ _ (sourcePlain_support a b ha W.profile W.support U hU t) j

theorem step_control (a b:ℝ)(ha:0<a)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀W:Test a b,∀U:ℝ,∀hU:0<U,∀t:ℝ,∀j:Fin 2,
      sourceControl S (step a b ha W U hU t j).profile≤
        C*sourceControl T W.profile*(1+‖t‖)^n:=by
  obtain ⟨n₀,T₀,C₀,hC₀,h₀⟩:=plain_profile_source_control a b ha S
  obtain ⟨n₁,T₁,C₁,hC₁,h₁⟩:=scaled_plain_profile_source_control a b ha S
  refine ⟨n₀+n₁,T₀∪T₁,C₀+C₁,add_pos hC₀ hC₁,?_⟩
  intro W U hU t j
  have hT₀:sourceControl T₀ W.profile≤sourceControl (T₀∪T₁) W.profile:=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_union_left : T₀⊆T₀∪T₁)) W.profile
  have hT₁:sourceControl T₁ W.profile≤sourceControl (T₀∪T₁) W.profile:=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_union_right : T₁⊆T₀∪T₁)) W.profile
  have hH:1≤1+‖t‖:=by linarith [norm_nonneg t]
  have hR:=sourceControl_nonneg (T₀∪T₁) W.profile
  by_cases hj:j=0
  · have hh:=h₀ W.profile W.support U hU t
    change sourceControl S (if j=0 then _ else _)≤_
    rw [ite_eq_left hj]
    apply hh.trans
    exact mul_le_mul
      (mul_le_mul (le_add_of_nonneg_right hC₁.le) hT₀ (sourceControl_nonneg _ _)
        (add_pos hC₀ hC₁).le)
      (pow_le_pow_right₀ hH (Nat.le_add_right _ _)) (by positivity) (by positivity)
  · have hh:=h₁ W.profile W.support U hU t
    change sourceControl S (if j=0 then _ else _)≤_
    rw [ite_eq_right hj]
    apply hh.trans
    exact mul_le_mul
      (mul_le_mul (le_add_of_nonneg_left hC₀.le) hT₁ (sourceControl_nonneg _ _)
        (add_pos hC₀ hC₁).le)
      (pow_le_pow_right₀ hH (Nat.le_add_left _ _)) (by positivity) (by positivity)

inductive Path (a b:ℝ)(ha:0<a)(T:ℝ)(W:Test a b):
    (n:ℕ)→Test (lower a b n) b→Prop
  | base : Path a b ha T W 0 W
  | next {n:ℕ}{V:Test (lower a b n) b}
      (path:Path a b ha T W n V)(U:ℝ)(hU:0<U)(t:ℝ)(j:Fin 2)(ht:‖t‖≤T):
      Path a b ha T W (n+1) (step _ b (lower_pos a b ha n) V U hU t j)

theorem path_control (a b:ℝ)(ha:0<a)(d:ℕ)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃R:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀W:Test a b,∀T:ℝ,0≤T→∀V:Test (lower a b d) b,Path a b ha T W d V→
      sourceControl S V.profile≤C*sourceControl R W.profile*(1+T)^n:=by
  induction d generalizing S with
  | zero=>
    refine ⟨0,S,1,zero_lt_one,?_⟩
    intro W T hT V hpath
    cases hpath
    simp
  | succ d ih=>
    obtain ⟨ns,Rs,Cs,hCs,hs⟩:=step_control (lower a b d) b (lower_pos a b ha d) S
    obtain ⟨np,R,Cp,hCp,hp⟩:=ih Rs
    refine ⟨np+ns,R,Cs*Cp,mul_pos hCs hCp,?_⟩
    intro W T hT V hpath
    cases hpath with
    | next old U hU t j ht=>
      rename_i V
      have h1:=hs V U hU t j
      have h2:=hp W T hT V old
      have hR:=sourceControl_nonneg R W.profile
      have h3:(1+‖t‖)^ns≤(1+T)^ns:=pow_le_pow_left₀ (by positivity) (by linarith) ns
      apply h1.trans
      apply (mul_le_mul (mul_le_mul_of_nonneg_left h2 hCs.le) h3 (by positivity) (by positivity)).trans_eq
      rw [pow_add]
      ring

lemma lower_antitone (a b:ℝ)(ha:0<a):Antitone (lower a b):=by
  apply antitone_nat_of_succ_le
  intro n
  exact div_le_self (lower_pos a b ha n).le (le_max_left _ _)

lemma support_at_depth (a b:ℝ)(ha:0<a)(d n:ℕ)(hn:n≤d)
    (V:Test (lower a b n) b):
    Function.support (V.profile:ℝ→ℂ)⊆Set.Icc (lower a b d) b:=by
  intro x hx
  exact ⟨(lower_antitone a b ha hn).trans (V.support hx).1,(V.support hx).2⟩

theorem paths_upto_control (a b:ℝ)(ha:0<a)(d:ℕ)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃R:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀W:Test a b,∀T:ℝ,0≤T→∀k:ℕ,k≤d→∀V:Test (lower a b k) b,
      Path a b ha T W k V→
      sourceControl S V.profile≤C*sourceControl R W.profile*(1+T)^n:=by
  choose J R C hC hbound using fun k:Fin (d+1)=>path_control a b ha k.val S
  let Rs:Finset (ℕ×ℕ):=Finset.univ.biUnion R
  let Cs:ℝ:=1+∑k,C k
  have hCs:0<Cs:=by
    have hh:=Finset.sum_nonneg (fun k (_:k∈(Finset.univ:Finset (Fin (d+1))))=>(hC k).le)
    dsimp [Cs];linarith
  refine ⟨∑k,J k,Rs,Cs,hCs,?_⟩
  intro W T hT k hk V hpath
  let l:Fin (d+1):=⟨k,by omega⟩
  have he:=hbound l W T hT V hpath
  have hR:R l⊆Rs:=by
    intro i hi
    exact Finset.mem_biUnion.mpr ⟨l,Finset.mem_univ _,hi⟩
  have hcontrol:sourceControl (R l) W.profile≤sourceControl Rs W.profile:=
    Seminorm.le_def.mp (Finset.sup_mono hR) W.profile
  have hconst:C l≤Cs:=by
    have hh:=Finset.single_le_sum (fun j (_:j∈(Finset.univ:Finset (Fin (d+1))))=>(hC j).le)
      (Finset.mem_univ l)
    dsimp [Cs];linarith
  have hdegree:J l≤∑j,J j:=Finset.single_le_sum (fun j (_:j∈(Finset.univ:Finset (Fin (d+1))))=>Nat.zero_le _) (Finset.mem_univ l)
  have hRpos:=sourceControl_nonneg Rs W.profile
  apply he.trans
  exact mul_le_mul (mul_le_mul hconst hcontrol (sourceControl_nonneg _ _) hCs.le)
    (pow_le_pow_right₀ (by linarith) hdegree) (by positivity) (by positivity)

open CenteredMomentSectorLocalization in
lemma annulus_support : Function.support (fun x:ℝ=>(annulus x:ℂ))⊆Set.Icc (1/4:ℝ) 1:=by
  intro x hx
  have hn:annulus x≠0:=by simpa using hx
  exact ⟨(lt_of_not_ge (fun h=>hn (annulus_zero_low x h))).le,
    (lt_of_not_ge (fun h=>hn (annulus_zero_high x h))).le⟩

def annulusTemplate:Test (1/4) 1 where
  profile:=(HasCompactSupport.of_support_subset_isCompact isCompact_Icc annulus_support).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp CenteredMomentSectorLocalization.annulus_smooth)
  support:=annulus_support

lemma annulusTemplate_apply (x:ℝ):annulusTemplate.profile x=(CenteredMomentSectorLocalization.annulus x:ℂ):=rfl

def annulusSeed (a b:ℝ)(ha:a≤1/4)(hb:1≤b):Test a b where
  profile:=annulusTemplate.profile
  support:=fun _x hx=>⟨ha.trans (annulusTemplate.support hx).1,
    (annulusTemplate.support hx).2.trans hb⟩

end SevenEighths.CenteredMomentEnergyProfiles

end

end OAI
