import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerReference
import OAI.NumberTheory.DirichletL.Inversion.InitialCanonicalEnergy
import OAI.NumberTheory.DirichletL.Descent.CanonicalRankExistence
import OAI.NumberTheory.DirichletL.Inversion.InitialCanonicalState

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.InverseInitialRetainedPhysical
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge CanonicalQuadraticSieve
open CanonicalRowCompletion InverseReflectedPhase InverseMoment InverseInitialClippedColumns
open CanonicalCoefficientClass ConcreteTraceCRT SecondPassArithmetic FirstPassCubeLabels IdealMobiusDivisorSum
open InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerModes
open InverseInitialQuotientGeometry InverseInitialEnergyCallerGeometry InverseInitialCanonicalState
local notation "O"=>ActualEisensteinCubic.O

theorem retained_physical_bound
    (W₁ W₂:ℝ→ℂ)(a₀ b₀:ℝ)(ha₀:0<a₀)
    (hs₁:Function.support W₁⊆Set.Icc a₀ b₀)(hs₂:Function.support W₂⊆Set.Icc a₀ b₀)
    (hW₁:ContDiff ℝ ∞ W₁)(hW₂:ContDiff ℝ ∞ W₂)
    (Φ:𝓢(ℝ,ℂ))(Vlog:Fin 6→ℝ→ℂ)(Mlog:Fin 6→ℝ)
    (hVlog:∀i,ContDiff ℝ ∞ (Vlog i))(hSlog:∀i,HasCompactSupport (Vlog i))
    (hMlog:∀i,0≤Mlog i)(hbox:∀i y,Vlog i y≠0→|y|≤Mlog i)
    (ω₁ ω₂:ℝ→ℂ)(lo b:ℝ)(hlo:0<lo)(hb:1≤b)
    (hω₁:Function.support ω₁⊆Set.Icc lo b)(hω₂:Function.support ω₂⊆Set.Icc lo b)
    (hd₁:ContDiff ℝ ∞ ω₁)(hd₂:ContDiff ℝ ∞ ω₂)
    (cap margin eps U π:ℝ)(hcap:0≤cap)(hmargin:0<margin)(heps:0<eps)(hU:0≤U)(hπ:0<π)(K:ℕ):
    ∃degree:ℕ,∃Btree:ℝ,1≤Btree ∧ ∀q:ℕ,q≠0→∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→∀Dpool:ℕ,Btree*Z^(cap+1)≤Dpool→
    let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) Dpool (reflectionExcludedPrimes_bad q);
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    let p:=poolPrimary F;
    let hp:=poolPrimary_ne_zero F hF;
    let hcop:=poolPrimary_coprime F hF;
    let hg:=poolPrimary_good F hF;
    ∀{σ:Type}[DecidableEq σ](slots:Finset σ),slots.card≤K→
    ∀(lists:σ→Finset (primePool F))(Hslot:σ→ℝ)(a:σ→primePool F→ℂ),
      (slots:Set σ).PairwiseDisjoint lists→(∀i∈slots,1≤Hslot i)→
      (∀i∈slots,∀P∈lists i,(P.val.absNorm:ℝ)≤Hslot i)→
      (∀i∈slots,∀P∈lists i,‖a i P‖≤1)→∀z:ℝ,0≤z→(∏i∈slots,Hslot i)≤Z^z→
    ∀Ψ:O→*ℂ,(∀u,‖Ψ u‖≤1)→FactorsModulo (fixedBaseConductor q) Ψ→
    ∀(S:Finset (Source (ι:=primePool F) 0)),
      (∀x∈S,x.divisor⊆x.common)→(∀x∈S,x.frequency≠0)→
    ∀(j:O)(D B v θ H R m η:ℝ),R≤U→0≤η→
    ∀(c₁ c₂ θ₁ θ₂:ℝ),0<c₁→0<c₂→
      BlockSupport p (pointSource Finset.univ S) W₁ W₂ ω₁ ω₂ Vlog Z D B v θ H c₁ c₂ θ₁ θ₂→
      (∀t∈quotientSet p S,(t.absNorm:ℝ)≤Z^R)→
    ∀(w:Source (ι:=primePool F) 0→ℂ),(∀x∈S,‖w x‖≤1)→
    ∀(labels:Finset (Ideal O))(rows:Finset O),
      (∀f∈labels,Admissible f ∧ (f.absNorm:ℝ)≤Z^(θ+v+2*η))→
      rows⊆nonzeroChildFrequencyBall 1 (Z^(θ+H+2*η))→(∀k∈rows,-k∈rows)→
      (∀x∈S,(initialChild (toTuple p (sectorSource
        (unitSector p hp (InverseInitialRayAttachment.poolPrimary_primary F hF) (sourcePoint x ∅ ∅)) x))).2.1∈labels ∧
        (initialChild (toTuple p (sectorSource
        (unitSector p hp (InverseInitialRayAttachment.poolPrimary_primary F hF) (sourcePoint x ∅ ∅)) x))).2.2∈rows)→
      max 0 (columnCenter D B v)-columnCenter D B v≤3*η→R=B-θ+2*η→
      (∀t∈quotientSet p S,
        j*primaryGenerator t≠0 ∧ 0≤θ+v+2*η ∧ 0≤θ+H+2*η ∧
        0≤fullPunctureWidth Z t j ∧
        ‖eisEmbedding (j*primaryGenerator t)‖^2=Z^(fullPunctureWidth Z t j) ∧
        θ+H+2*η≤cap ∧ max 0 (columnCenter D B v)+(θ+v+2*η)≤cap ∧
        CanonicalMargins (max 0 (columnCenter D B v)+(θ+v+2*η))
          (θ+H+2*η) (fullPunctureWidth Z t j) z margin)→
      ‖physicalBlock p hp hcop hg (pointSource Finset.univ S) (w∘erasePoint) Ψ j
        (primeMark slots lists a) (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m‖≤
        C*Z^(m+15*η+π+eps)*
          ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*degree)*
            (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*degree)) := by
  obtain ⟨fresh₁,fresh₂,hsf₁,hsf₂,hphysical⟩:=
    InverseInitialEnergyCallerReference.actual_physical_reference_bound
      W₁ W₂ a₀ b₀ ha₀ hs₁ hs₂ hW₁ hW₂ Φ Vlog Mlog hVlog hSlog hMlog hbox
      ω₁ ω₂ lo b hlo hb hω₁ hω₂ hd₁ hd₂
  obtain ⟨af₁,bf₁,haf₁,hab₁,_,hs₁f⟩:=hsf₁
  obtain ⟨af₂,bf₂,haf₂,hab₂,_,hs₂f⟩:=hsf₂
  obtain ⟨J₁,B₁,hB₁,hm₁⟩:=canonical_marked_energy_exists cap cap margin eps hcap hcap hmargin heps
    K fresh₁ af₁ bf₁ haf₁ (haf₁.le.trans hab₁) (subset_trans (subset_closure) hs₁f)
  obtain ⟨J₂,B₂,hB₂,hm₂⟩:=canonical_marked_energy_exists cap cap margin eps hcap hcap hmargin heps
    K fresh₂ af₂ bf₂ haf₂ (haf₂.le.trans hab₂) (subset_trans (subset_closure) hs₂f)
  let J:=J₁+J₂
  obtain ⟨Cp,hCp,hphysical⟩:=hphysical J K U π hU hπ
  refine ⟨J,B₁+B₂,by linarith,?_⟩
  intro q hq
  obtain ⟨C₁,Z₁,hC₁,hZ₁,hm₁⟩:=hm₁ q hq
  obtain ⟨C₂,Z₂,hC₂,hZ₂,hm₂⟩:=hm₂ q hq
  refine ⟨Cp*(C₁+C₂),max Z₁ Z₂,mul_pos hCp (add_pos hC₁ hC₂),lt_max_of_lt_left hZ₁,?_⟩
  intro Z hZ Dpool hD F hFa
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hFa i];infer_instance
  intro p hp hcop hg σ dec slots hslots lists Hslot a hdis hHslot hP ha z hz hprod Ψ hΨ hperiod
    S hdiv hf j D B v θ H R m η hR hη c₁ c₂ θ₁ θ₂ hc₁ hc₂ hsupport hn w hw labels rows hlabels hrows hneg hchild hclip hReq hstate
  have hZp:1<Z:=hZ₁.trans_le ((le_max_left _ _).trans hZ)
  have hD₁:B₁*Z^(cap+1)≤Dpool:=
    (mul_le_mul_of_nonneg_right (by linarith : B₁≤B₁+B₂) (Real.rpow_nonneg (by linarith) _)).trans hD
  have hD₂:B₂*Z^(cap+1)≤Dpool:=
    (mul_le_mul_of_nonneg_right (by linarith : B₂≤B₁+B₂) (Real.rpow_nonneg (by linarith) _)).trans hD
  have hmoment₁:=hm₁ Z ((le_max_left _ _).trans hZ) Dpool hD₁ slots hslots lists Hslot a hdis hHslot hP ha z hz hprod Ψ hΨ hperiod
  have hmoment₂:=hm₂ Z ((le_max_right _ _).trans hZ) Dpool hD₂ slots hslots lists Hslot a hdis hHslot hP ha z hz hprod Ψ hΨ hperiod
  have hbound:=hphysical p hp hcop hg
    (InverseInitialRayAttachment.poolPrimary_injective F hFa)
    (InverseInitialRayAttachment.poolPrimary_primary F hFa) (poolPrimary_odd F hFa)
    S hdiv hf Finset.univ Ψ hΨ j slots hslots lists a ha
    Z D B v θ H R m η hZp hR (mul_nonneg hη (Real.log_pos hZp).le)
    c₁ c₂ θ₁ θ₂ hc₁ hc₂ hsupport hn w hw labels rows
    (fun f hf=>(hlabels f hf).1.1) hneg hchild
    (max 0 (columnCenter D B v)+(θ+v)) (C₁+C₂) (eps+4*η) (by positivity) hclip
    (by unfold columnCenter;ring) hReq ?_
  · convert hbound using 1
    rw [show m+11*η+π+(eps+4*η)=m+15*η+π+eps by ring]
    ring
  · intro s ρ A₁ hA₁ A₂ hA₂ t ht
    obtain ⟨hm,hV,hM,hQ,hnorm,hMc,hFc,hmargin⟩:=hstate t ht
    have hweight:∀f∈labels,((idealDivisors f).card:ℝ)^(A₁.card+A₂.card+1)≤secondLabelWeight K f:=by
      intro f hf
      exact assigned_label_weight_le slots A₁ A₂ K hslots (Finset.mem_powerset.mp hA₁)
        (Finset.mem_powerset.mp hA₂) f (hlabels f hf).1.1
    have hleft:=InverseInitialCanonicalEnergy.initial_child_from_rank p hp hcop hg Finset.univ Ψ
      (secondRayMinus Ψ ρ) slots (slots\A₁) lists a fresh₁ Z cap cap z margin eps C₁
      (max 0 (columnCenter D B v)) (θ+v) (θ+H+2*η) (fullPunctureWidth Z t j) η K J₁
      (j*primaryGenerator t) hZp ((show IsBaseRayTwist Ψ Ψ from Or.inl rfl).secondMinus ρ) hm
      (le_max_left _ _) hV hM hQ hMc hFc hmargin hnorm Finset.sdiff_subset labels hlabels rows hrows
      _ (by intros;positivity) hweight s hmoment₁
    have hright:=InverseInitialCanonicalEnergy.initial_child_from_rank p hp hcop hg Finset.univ Ψ
      (secondRayPlus Ψ ρ) slots (slots\A₂) lists a fresh₂ Z cap cap z margin eps C₂
      (max 0 (columnCenter D B v)) (θ+v) (θ+H+2*η) (fullPunctureWidth Z t j) η K J₂
      (j*primaryGenerator t) hZp ((show IsBaseRayTwist Ψ Ψ from Or.inl rfl).secondPlus ρ) hm
      (le_max_left _ _) hV hM hQ hMc hFc hmargin hnorm Finset.sdiff_subset labels hlabels rows hrows
      _ (by intros;positivity) hweight s hmoment₂
    constructor
    · apply hleft.trans
      have hexp:max 0 (columnCenter D B v)+(θ+v)+eps+4*η=
        max 0 (columnCenter D B v)+(θ+v)+(eps+4*η):=by ring
      rw [hexp]
      gcongr
      · linarith
      · linarith [norm_nonneg s]
      · dsimp [J]; omega
    · apply hright.trans
      have hexp:max 0 (columnCenter D B v)+(θ+v)+eps+4*η=
        max 0 (columnCenter D B v)+(θ+v)+(eps+4*η):=by ring
      rw [hexp]
      gcongr
      · linarith
      · linarith [norm_nonneg s]
      · dsimp [J]; omega

end SevenEighths.InverseInitialRetainedPhysical

end

end OAI
