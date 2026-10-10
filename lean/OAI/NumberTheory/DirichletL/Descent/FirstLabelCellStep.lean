import OAI.NumberTheory.DirichletL.Descent.FirstLabelCellStepPhysicalGates
import OAI.NumberTheory.DirichletL.Descent.GlobalPriorityFixedChildStepUniform

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstLabelCell
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseFirstPriorityParents InverseFirstGlobalParents
open InverseMomentGlobalRetainedGates InverseInitialArithmetic InverseSecondSourceBlocks
open InverseSecondFibers InverseInitialClippedColumns RayFourExpansion FirstCauchyArithmetic
open InverseWholePriorityRetainedSource
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

def ChildBounds {ι σ : Type} [DecidableEq ι] [DecidableEq σ]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ) (negative : Bool)
    (Ψ : O→*ℂ) (m : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (Z M r ell V eta tau window b epschild A : ℝ) (K degree : ℕ) : Prop :=
  ∀(ray : RayCharacter×RayCharacter)(core : FirstCoreIndex)(assigned : Finset σ),assigned⊆slots→
  let S := source p pool Q k l j negative assigned lists Z M r ell V eta tau window b
  let Ψ₀ := firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
  (∀z : SecondRayIndex,∀d∈keys p S,∀s : ℝ,∀J₁∈(slots\assigned).powerset,∀γ∈actualSecondTriples p 1 1 (cell p S d),
    normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ₀ z)
      (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₁) lists a
      ((actualCellLabels p S d).filter Squarefree)
      (nonzeroChildFrequencyBall 1 (actualCellRowRadius Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d))
      (secondLabelWeight K) (childLogTest ω₁ s)
      (Z^(max 0 (secondCellColumnExponent Z (columnScale Z r k l negative) d))) Z
      (actualCellTotalExponent Z (columnScale Z r k l negative) (exponent Z (k 2)) (exponent Z j) eta d)≤
      A*Z^(actualCellTotalExponent Z (columnScale Z r k l negative) (exponent Z (k 2)) (exponent Z j) eta d+epschild)*
        (1+‖s‖)^(2*degree)) ∧
  (∀z : SecondRayIndex,∀d∈keys p S,∀s : ℝ,∀J₂∈(slots\assigned).powerset,∀γ∈actualSecondTriples p 1 1 (cell p S d),
    normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ₀ z)
      (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₂) lists a
      ((actualCellLabels p S d).filter Squarefree)
      (nonzeroChildFrequencyBall 1 (actualCellRowRadius Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d))
      (secondLabelWeight K) (childLogTest ω₂ s)
      (Z^(max 0 (secondCellColumnExponent Z (columnScale Z r k l negative) d))) Z
      (actualCellTotalExponent Z (columnScale Z r k l negative) (exponent Z (k 2)) (exponent Z j) eta d)≤
      A*Z^(actualCellTotalExponent Z (columnScale Z r k l negative) (exponent Z (k 2)) (exponent Z j) eta d+epschild)*
        (1+‖s‖)^(2*degree))

theorem actual_label_cell_step (om : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo)
    (hsupport : Function.support om⊆Set.Icc lo hi) (negative : Bool)
    (window Ltail Lgate tau saving : ℝ) (hhi : hi≤Real.exp window)
    (hLtail : 0≤Ltail) (hLgate : 0≤Lgate) (htau : 0<tau)
    (bcap : ℝ) (hbcap : 1≤bcap) (dsmall : ℝ) (hdsmall : 0<dsmall)
    (B₀ : Fin 6→ℝ) (hB₀ : ∀i,0≤B₀ i) (K : ℕ) (epsmass : ℝ) (hepsmass : 0<epsmass) :
    ∃(ω₁ ω₂ : 𝓢(ℝ,ℂ))(loFresh hiFresh : ℝ),0<loFresh ∧ loFresh≤hiFresh ∧
      HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
    ∀degree : ℕ,∃C Cbin Czero Ctail : ℝ,0≤C ∧ 0≤Cbin ∧ 0≤Czero ∧ 0≤Ctail ∧
    ∀{ι σ : Type}[DecidableEq ι][DecidableEq σ](p : ι→O)(hp : ∀i,p i≠0)
      [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (hinj : Function.Injective (fun i=>Ideal.span {p i})) (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool : Finset ι)(Q : Finset (ι→₀ℕ))(k : SourceIndex)(l j : ℕ)
      (Ψ : O→*ℂ)(m : O)(slots : Finset σ)(lists : σ→Finset ι)(a : σ→ι→ℂ)
      (Z M r ell V eta pi b Lcol LY epschild A t : ℝ)(ρ : Fin 6→ℝ),
      2≤Z→0≤eta→2≤Z^eta→0≤ell+eta→
      (∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))→
      (slots:Set σ).PairwiseDisjoint lists→slots.card≤K→(∀i∈slots,∀q∈lists i,‖a i q‖≤1)→
      (∀u,‖Ψ u‖≤1)→(∀i,|ρ i|≤B₀ i)→hi≤b→b≤bcap→1≤b→b≤Z^(6*eta)→
      Real.exp window≤Z^(4*eta)→0≤A→
      columnScale Z r k l negative*Real.exp window≤Z^Lcol→
      (firstCellRadius Z M r ell V eta tau k j)⁻¹≤Z^LY→
      b*columnScale Z r k l negative≤Z^Lgate→exponent Z (k 3)+eta+2*Lcol+tau+LY≤Lgate→
      epsmass*(ell+exponent Z (k 4)/2+exponent Z l+Lgate+11*eta/2)≤pi→
      epsmass*(r-columnA Z k negative-exponent Z (k 2)-exponent Z l)+7*eta/2+
        dsmall*(3*ell+exponent Z (k 2)+exponent Z l+5*eta)+
        2*epsmass*(2*ell+exponent Z (k 2)+exponent Z l+4*eta)≤pi+eta/2→
      1≤firstCellRadius Z M r ell V eta tau k j→1≤columnScale Z r k l negative*Real.exp window→
      firstCellRadius Z M r ell V eta tau k j≤Z^Ltail→
      (firstCellRadius Z M r ell V eta tau k j)⁻¹≤Z^Ltail→
      columnScale Z r k l negative*Real.exp window≤Z^Ltail→
      firstKappa M r ell V (exponent Z (k 3)) (columnA Z k negative) (exponent Z (k 2)) (exponent Z (k 4))+
        (9/2:ℝ)*eta≤Ltail→
      ell+eta≤Ltail→exponent Z (k 4)+eta≤Ltail→exponent Z (k 2)+eta≤Ltail→exponent Z l+eta≤Ltail→
      ChildBounds p hp hcop hg pool Q k l j negative Ψ m slots lists a ω₁ ω₂
        Z M r ell V eta tau window b epschild A K degree→
      (Z^(firstKappa M r ell V (exponent Z (k 3)) (columnA Z k negative) (exponent Z (k 2)) (exponent Z (k 4)))*
        Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      globalPriorityOriginalEnergy p hg hp hinj (extra negative) pool
        (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k l j) (parentWeight p l)
        negative Ψ m slots lists a om (columnScale Z r k l negative) t (firstCellRadius Z M r ell V eta tau k j)≤
      Czero*Z^(r+3*ell+V+17*eta+tau+pi)+
      C*A*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder (2*degree))*(1+Cbin*Real.log Z)^4*
        Z^(r+3*ell+V+48*eta+tau+pi+epschild)+Ctail*Z^(-saving) := by
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hw₁,hw₂,hs₁,hs₂,hstep⟩ := global_priority_fixed_child_step_uniform_types
    om lo hi hlo hsupport negative window Ltail tau saving hhi hLtail htau bcap hbcap
    0 dsmall hdsmall (fun _=>Lgate) (fun _=>hLgate) B₀ hB₀ K epsmass hepsmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hw₁,hw₂,hs₁,hs₂,?_⟩
  intro degree
  obtain ⟨C,Cbin,Czero,Ctail,hC,hCbin,hCzero,hCtail,he⟩ := hstep degree
  refine ⟨C,Cbin,Czero,Ctail,hC,hCbin,hCzero,hCtail,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr hinj hc pool Q k l j Ψ m slots lists a
    Z M r ell V eta pi b Lcol LY epschild A t ρ hZ2 heta hbin hell hQ hdisj hslots ha hΨ hρ hhib hbb hb1 hb6
    hwindow hA hcol hYi hgeom hphysical hbudget hcost hY1 hX1 hYcap hYicap hXcap hPcap hellcap hactivecap hcommoncap hquotcap hchild
  have hZ : 1<Z := by linarith
  have hz : 0<Z := zero_lt_one.trans hZ
  have hX : 0<columnScale Z r k l negative := Real.rpow_pos_of_pos hz _
  have hY : 0<firstCellRadius Z M r ell V eta tau k j := Real.rpow_pos_of_pos hz _
  have hparent := label_parent_bounds p hp pool Q k l j Z ell eta hZ heta hbin hQ
  have htail := parent_tail_caps p hp pool Q k l j Z ell eta Ltail hZ heta hbin hLtail hQ
    hellcap hactivecap hcommoncap hquotcap
  apply he p hp hcop hg hpr hinj hc (extra negative) pool
    (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k l j)
    (label_parent_valid p pool Q k l j) (fun y hy=>extra_subset negative y.cube)
    (parentWeight p l) (fun y hy=>parentWeight_norm p l y) Ψ m slots lists a
    (secondCutoff p Z M r ell V eta tau window k l j negative)
    (firstCellRadius Z M r ell V eta tau k j)
    (fun _ d=>actualCellRowRadius Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d)
    (eta*Real.log Z) Z (columnScale Z r k l negative) epschild
    (actualCellLabelExponent Z (exponent Z (k 2)) (exponent Z j) eta)
    ell (exponent Z (k 4)) (exponent Z j) (exponent Z l) eta M r V
    (exponent Z (k 3)) (columnA Z k negative) (exponent Z (k 2)) pi b ρ t
    (fun assigned d=>actualCellLabels p (source p pool Q k l j negative assigned lists Z M r ell V eta tau window b) d) A
    hhib hbb hdisj hslots hA
  · intro ray core assigned hassigned
    obtain ⟨_,_,hrows,_,hn,hlabels,_,hcaps,hgeometry,hmass⟩ := source_step_arithmetic p hp pool Q k l j
      negative assigned lists Z M r ell V eta tau window b Lcol LY Lgate epsmass pi
      hZ heta hbin hepsmass.le hwindow hQ hcol hYi hgeom hphysical hbudget
    have hJ : assigned.card≤K := (Finset.card_le_card hassigned).trans hslots
    have hrest : (slots\assigned).card≤K := (Finset.card_le_card Finset.sdiff_subset).trans hslots
    have hbchild := hchild ray core assigned hassigned
    refine ⟨(fun i hi q hq=>ha i (hassigned hi) q hq),hρ,mul_nonneg heta (Real.log_nonneg hZ.le),hZ,hX,hY,heta,hbin,
      hrows,(fun x hx=>(hn x hx).1),(fun x hx=>(hn x hx).2.1),(fun x hx=>(hn x hx).2.2.1),
      (fun x hx=>(hn x hx).2.2.2.2.2.1),(fun x hx=>(hn x hx).2.2.2.2.1),hΨ,
      (fun i hi q hq=>ha i (Finset.mem_sdiff.mp hi).1 q hq),
      (fun i hi q hq=>ha i (Finset.mem_sdiff.mp hi).1 q hq),
      (fun d hd x hx=>hlabels d x hx),by omega,hrest,hrest,hA,rfl,rfl,rfl,(fun _=>rfl),hZ2,hb1,hb6,
      hcaps,hgeometry,hmass,hbchild.1,hbchild.2⟩
  · exact Nat.zero_le _
  · exact hell
  · exact dyadic_exponent_nonneg Z hZ _
  · exact dyadic_exponent_nonneg Z hZ _
  · exact hcost
  · exact fun y hy=>(hparent y hy).1
  · exact fun y hy=>(hparent y hy).2.1
  · exact fun y hy=>(hparent y hy).2.2.1
  · exact fun y hy=>(hparent y hy).2.2.2.1
  · exact fun y hy=>(hparent y hy).2.2.2.2.1
  · exact hY1
  · exact hX1
  · exact hYcap
  · exact hYicap
  · exact hXcap
  · exact hPcap
  · exact fun y hy=>(htail y hy).1
  · exact fun y hy=>(htail y hy).2.1
  · exact fun y hy=>(htail y hy).2.2.1
  · exact fun y hy=>(htail y hy).2.2.2.1
  · exact fun y hy=>(htail y hy).2.2.2.2
  · exact fun G E=>secondCutoff_nonneg p Z M r ell V eta tau window k l j negative hz G E
  · exact fun y hy G hG E=>secondCutoff_dominates p hp pool Q k l j negative Z M r ell V eta tau window hZ hbin y hy G E.val

end SevenEighths.InverseMomentFirstLabelCell
end

end OAI
