import OAI.NumberTheory.DirichletL.Inversion.InitialRetainedWindow
import OAI.NumberTheory.DirichletL.Inversion.InitialDyadicAssemblyRetained

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.InverseInitialRetainedSum
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open CanonicalQuadraticSieve CanonicalRowCompletion CanonicalCoefficientClass
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes InverseInitialEnergyCallerWindows
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialEnergyCallerState
open InverseInitialDyadicAssembly InverseSecondChildWindows Filter
local notation "O"=>ActualEisensteinCubic.O

theorem retained_sum_bound
    (W₁ W₂:ℝ→ℂ)(a₀ b₀ bcap:ℝ)(ha₀:0<a₀)(hbcap:1≤bcap)
    (hs₁:Function.support W₁⊆Set.Icc a₀ b₀)(hs₂:Function.support W₂⊆Set.Icc a₀ b₀)
    (hW₁:ContDiff ℝ ∞ W₁)(hW₂:ContDiff ℝ ∞ W₂)(Φ:𝓢(ℝ,ℂ))
    (cap gap eps π η τ loss:ℝ)(hcap:0≤cap)(hgap:0<gap)(heps:0<eps)(hπ:0<π)
    (hη:0<η)(hηone:η≤1)(hηsmall:η≤gap/50)(hτ:0<τ)(hτsmall:τ≤gap/50)(hloss:0<loss)(K:ℕ):
    ∃degree:ℕ,∃Btree:ℝ,1≤Btree ∧
    ∀q:ℕ,q≠0→∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→∀Dpool:ℕ,Btree*Z^(cap+1)≤Dpool→
    let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) Dpool (reflectionExcludedPrimes_bad q);
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    let p:=poolPrimary F;
    let hp:=poolPrimary_ne_zero F hF;
    let hcop:=poolPrimary_coprime F hF;
    let hg:=poolPrimary_good F hF;
    ∀{σ:Type}[DecidableEq σ](all assigned:Finset σ),assigned⊆all→all.card≤K→
    ∀(lists:σ→Finset (primePool F))(Hslot:σ→ℝ)(coeff:σ→primePool F→ℂ),
      (all:Set σ).PairwiseDisjoint lists→(∀i∈all\assigned,1≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,(P.val.absNorm:ℝ)≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,‖coeff i P‖≤1)→
    ∀(qelem:σ→O)(z al bl:σ→ℝ)(primeW:σ→ℝ→ℂ),
      (∀i∈all,0≤z i)→(∀i∈assigned,qelem i≠0)→
      (∀i∈assigned,Function.support (primeW i)⊆Set.Icc (al i) (bl i))→
      (∀i∈assigned,primeW i ((Ideal.absNorm (Ideal.span {qelem i}):ℝ)/Z^(z i))≠0)→
    ∀Ψ:O→*ℂ,(∀u,‖Ψ u‖≤1)→FactorsModulo (fixedBaseConductor q) Ψ→
    ∀(S:Finset (Source (ι:=primePool F) 0)),
      (∀x∈S,x.divisor⊆x.common)→(∀x∈S,x.frequency≠0)→
    ∀(D m r T:ℝ),0≤m→0<T→
      (∏i∈assigned,bl i)≤Z^η→
      (∏i∈all\assigned,Hslot i)≤Z^(assignedCenter (all\assigned) z+η)→
      D=r+assignedCenter all z-2*assignedCenter assigned z→
      r+2*assignedCenter all z≤m-2*gap→
      2*r+8*assignedCenter all z≤3*m-2*gap→
      r+assignedCenter all z+7*η≤cap→
    ∀(c₁ c₂ θ₁ θ₂:ℝ),1≤c₁→c₁≤bcap→1≤c₂→c₂≤bcap→
    ∀(w:Source (ι:=primePool F) 0→ℂ),(∀x∈S,‖w x‖≤1)→
      ‖∑k∈retainedWindows (fun _=>1) (physicalCaps (max 1 b₀) Z D T) Z D m (4*η+τ),
        windowBlock p hp hcop hg Finset.univ
          (cappedSource p S (fun _=>1) (physicalCaps (max 1 b₀) Z D T)) w Ψ
          (assignedElement assigned qelem) (primeMark (all\assigned) lists coeff)
          (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m (fun i=>(k i).val)‖≤
        C*Z^(m+15*η+π+eps+loss)*
          ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*degree)*
            (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*degree)) := by
  have hb:0<max 1 b₀:=zero_lt_one.trans_le (le_max_left _ _)
  obtain ⟨J,Btree,Tclip,hBtree,hTclip,hwindow⟩:=
    InverseInitialRetainedWindow.retained_window_bound W₁ W₂ a₀ b₀ bcap ha₀ hbcap hs₁ hs₂ hW₁ hW₂ Φ
      (fun _=>1/4) (fun _=>1) (by intros;norm_num) (by intros;norm_num)
      cap gap eps (cap+3) π hcap hgap heps (by linarith) hπ K
  obtain ⟨A,hA,hcount⟩:=retained_card_subpower (max 1 b₀) cap (4*η+τ) loss hb hcap (by positivity) hloss
  have hpowers:∀ᶠZ:ℝ in atTop,(4:ℝ)≤Z^η:=
    (tendsto_rpow_atTop hη).eventually (eventually_ge_atTop 4)
  have hlogs:∀ᶠZ:ℝ in atTop,Tclip≤3*η*Real.log Z:=by
    filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (Tclip/(3*η)))] with Z hZ
    exact (div_le_iff₀ (by positivity : 0<3*η)).mp hZ |>.trans_eq (mul_comm _ _)
  have hevent:=window_exponent_eventual_upper (max 1 b₀) 1 hb (by norm_num)
  obtain ⟨Zaux,haux⟩:=eventually_atTop.mp (hcount.and (hpowers.and (hlogs.and hevent)))
  refine ⟨J,Btree,hBtree,?_⟩
  intro q hq
  obtain ⟨C,Zq,hC,hZq,hw⟩:=hwindow q hq
  refine ⟨A*C,max Zq Zaux,mul_pos hA hC,lt_max_of_lt_left hZq,?_⟩
  intro Z hZ Dpool hD F hFa
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hFa i];infer_instance
  intro p hp hcop hg σ dec all assigned hassigned hK lists Hslot coeff hdis hHs hPs hac
    qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod S hdiv hf D m r T hm hT
    hprodj hprod hDeq hmargin₁ hmargin₂ hparent c₁ c₂ θ₁ θ₂ hc₁ hbc₁ hc₂ hbc₂ w hweight
  have hZq':Zq≤Z:=(le_max_left _ _).trans hZ
  obtain ⟨hcZ,hpow,hlog,hexp⟩:=haux Z ((le_max_right _ _).trans hZ)
  have hZp:1<Z:=hZq.trans_le hZq'
  have hDcap:D≤cap:=by
    have hg:0≤assignedCenter assigned z:=Finset.sum_nonneg (fun i hi=>hz i (hassigned hi))
    rw [hDeq]
    linarith
  let Sc:=cappedSource p S (fun _=>1) (physicalCaps (max 1 b₀) Z D T)
  have hdivc:∀x∈Sc,x.divisor⊆x.common:=fun x hx=>hdiv x (Finset.mem_filter.mp hx).1
  have hfc:∀x∈Sc,x.frequency≠0:=fun x hx=>hf x (Finset.mem_filter.mp hx).1
  have hlo:Z^(-η)≤(1/4:ℝ):=by
    rw [Real.rpow_neg (zero_lt_one.trans hZp).le]
    simpa only [one_div] using inv_anti₀ (by norm_num : (0:ℝ)<4) hpow
  have hnorm (k:Windows (fun _=>1) (physicalCaps (max 1 b₀) Z D T))
      (hk:k∈retainedWindows (fun _=>1) (physicalCaps (max 1 b₀) Z D T) Z D m (4*η+τ)):
      ‖windowBlock p hp hcop hg Finset.univ Sc w Ψ (assignedElement assigned qelem)
        (primeMark (all\assigned) lists coeff) (clippedSource W₁ c₁ θ₁)
        (clippedSource W₂ c₂ θ₂) Φ Z D m (fun i=>(k i).val)‖≤
        C*Z^(m+15*η+π+eps)*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*J)*
          (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*J)):=by
    have hsize:0<max 1 b₀*Z^D:=mul_pos hb (Real.rpow_pos_of_pos (zero_lt_one.trans hZp) D)
    have h0:=hexp.2 (max 1 b₀*Z^D) D hsize le_rfl (k 0).val (k 0).property
    have h1:=hexp.2 (max 1 b₀*Z^D) D hsize le_rfl (k 1).val (k 1).property
    apply hw Z hZq' Dpool hD all assigned hassigned hK lists Hslot coeff hdis hHs hPs hac
      qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod Sc hdivc hfc cutoff
      (fun i x hx=>Set.Ioo_subset_Icc_self (cutoff_support i hx))
      D (exponent Z (k 0).val) (exponent Z (k 2).val) (exponent Z (k 1).val)
      (exponent Z (k 3).val) m r η τ hη.le hηsmall hτsmall
      (fun _=>by linarith) hlo hlog hprodj hprod hDeq hmargin₁ hmargin₂ hparent
      (by linarith [h0.2,h1.1]) (Finset.mem_filter.mp hk).2 c₁ c₂ θ₁ θ₂ hc₁ hbc₁ hc₂ hbc₂
      (fun x=>w x*outerCutoff cutoff (sourceRelative p x Z D (exponent Z (k 0).val)
        (exponent Z (k 2).val) (exponent Z (k 1).val) (exponent Z (k 3).val))) ?_
    intro x hx
    rw [norm_mul]
    have hmul {a b : ℝ} (ha : a ≤ 1) (hb₀ : 0 ≤ b) (hb : b ≤ 1) : a * b ≤ 1 :=
      (mul_le_of_le_one_left hb₀ ha).trans hb
    apply hmul (hweight x (Finset.mem_filter.mp hx).1) (by positivity)
    unfold outerCutoff
    simp only [norm_mul]
    exact hmul (hmul (hmul (cutoff_norm_le _ _) (by positivity)
      (cutoff_norm_le _ _)) (by positivity) (cutoff_norm_le _ _)) (by positivity) (cutoff_norm_le _ _)
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum hnorm).trans
  rw [Finset.sum_const, nsmul_eq_mul]
  calc
    _≤(A*Z^loss)*(C*Z^(m+15*η+π+eps)*
        ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*J)*
          (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*J))):=
      mul_le_mul_of_nonneg_right (hcZ D m (4*η+τ) T hDcap hm le_rfl hT) (by positivity)
    _=_:=by rw [Real.rpow_add (zero_lt_one.trans hZp) (m+15*η+π+eps) loss];ring

end SevenEighths.InverseInitialRetainedSum

end

end OAI
