import OAI.NumberTheory.DirichletL.Descent.CanonicalChildSupport
import OAI.NumberTheory.DirichletL.Descent.FirstLabelCellStep

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CanonicalQuadraticSieve
open InverseInitialClippedColumns InverseSecondFibers InverseSecondSourceBlocks
open CanonicalCoefficientClass InverseMomentFirstLabelCell InverseMomentFirstChildWindows InverseFirstGlobalCaps
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type}[DecidableEq ι][DecidableEq σ]
variable (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
variable (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
variable (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def CanonicalRankMoments (pool:Finset ι)(base:O→*ℂ)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (W:𝓢(ℝ,ℂ))(Z Mmax Fcap z c eps A:ℝ)(K degree:ℕ):Prop :=
  ∀(Ψ:O→*ℂ),IsBaseRayTwist base Ψ→∀(m:O),m≠0→∀N V M Qwidth:ℝ,
    0≤N→0≤V→0≤M→0≤Qwidth→M≤Mmax→N+V≤Fcap→
    CanonicalMargins (N+V) M Qwidth z c→
    ‖ConcreteTraceCRT.eisEmbedding m‖^2=Z^Qwidth→
    ∀(subslots:Finset σ),subslots⊆slots→∀labels:Finset (Ideal O),
      (∀I∈labels,Admissible I ∧ (Ideal.absNorm I:ℝ)≤Z^V)→∀s:ℝ,
    normalizedColumnEnergy p hp hcop hg pool Ψ m subslots lists a labels
      (nonzeroChildFrequencyBall 1 (Z^M)) (secondLabelWeight K) (childLogTest W s) (Z^N) Z (N+V)≤
      A*Z^(N+V+eps)*(1+‖s‖)^(2*degree)

include hp in
theorem canonical_rank_moments_children
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(k:SourceIndex)(l j:ℕ)(negative:Bool)
    (base Ψ:O→*ℂ)(hΨ:IsBaseRayTwist base Ψ)(m:O)(hm:m≠0)
    (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)(ω₁ ω₂:𝓢(ℝ,ℂ))
    (Z M r ell V eta tau window b cutoff Qwidth z c eps A:ℝ)(K degree:ℕ)
    (hZ:1<Z)(heta:0≤eta)(hbin:2≤Z^eta)(hell:0≤ell)(hV:0≤V)
    (hb:1≤b)(hbt:b≤Z^(6*eta))(hwindow:Real.exp window≤Z^(4*eta))
    (_hd:0<cutoff)(hterminal:cutoff≤ell+V)(hsmall:eta≤cutoff/16)
    (hparent:CanonicalMargins (r+3*ell+V) M Qwidth z c)
    (hpuncture:(Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤Z^Qwidth)
    (hQ:∀v∈Q,‖ConcreteTraceCRT.eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
    (h₁:CanonicalRankMoments p hp hcop hg pool base slots lists a ω₁ Z (M-3*cutoff/2) (r+3*ell+V+15*eta) z (c-7*eta) eps A K degree)
    (h₂:CanonicalRankMoments p hp hcop hg pool base slots lists a ω₂ Z (M-3*cutoff/2) (r+3*ell+V+15*eta) z (c-7*eta) eps A K degree):
    ChildBounds p hp hcop hg pool Q k l j negative Ψ m slots lists a ω₁ ω₂
      Z M r ell V eta tau window b eps A K degree :=by
  intro ray core assigned hass
  let S:=source p pool Q k l j negative assigned lists Z M r ell V eta tau window b
  let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
  have hbase:IsBaseRayTwist base Ψ₀:=hΨ.firstCore _ _ _
  have hstate:=source_state_bounds p hp pool Q k l j negative assigned lists Z M r ell V eta tau window b cutoff
    hZ heta hbin hell hV hb hbt hwindow hterminal hsmall hQ
  have hmargin:=source_child_margins p hp hpr pool Q k l j negative assigned lists Z M r ell V eta tau window b
    m hm Qwidth z c hZ heta hbin hV hparent hpuncture hQ
  have hlabels:=source_labels p hp pool Q k l j negative assigned lists Z M r ell V eta tau window b hZ heta hbin hQ
  constructor
  · intro zz d hdcell s J hJ γ hγ
    have st:=hstate d hdcell
    have mg:=hmargin d γ hγ
    apply h₁ (secondRayMinus Ψ₀ zz) (hbase.secondMinus zz) (actualSecondInheritedRadicalPuncture m γ) mg.1
      (max 0 (secondCellColumnExponent Z (columnScale Z r k l negative) d))
      (actualCellLabelExponent Z (exponent Z (k 2)) (exponent Z j) eta d)
      (actualCellRowExponent Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d)
      (actualSecondPunctureWidth Z m γ) st.1 st.2.1 st.2.2.2.1 mg.2.1 (by linarith [st.2.2.2.2]) st.2.2.1 mg.2.2.2 mg.2.2.1
      ((slots\assigned)\J) (Finset.sdiff_subset.trans Finset.sdiff_subset)
      ((actualCellLabels p S d).filter Squarefree) ?_ s
    intro I hI
    exact ⟨actual_cell_labels_admissible p hp hg hc S d I hI,(hlabels.2 d I hI).2.2⟩
  · intro zz d hdcell s J hJ γ hγ
    have st:=hstate d hdcell
    have mg:=hmargin d γ hγ
    apply h₂ (secondRayPlus Ψ₀ zz) (hbase.secondPlus zz) (actualSecondInheritedRadicalPuncture m γ) mg.1
      (max 0 (secondCellColumnExponent Z (columnScale Z r k l negative) d))
      (actualCellLabelExponent Z (exponent Z (k 2)) (exponent Z j) eta d)
      (actualCellRowExponent Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d)
      (actualSecondPunctureWidth Z m γ) st.1 st.2.1 st.2.2.2.1 mg.2.1 (by linarith [st.2.2.2.2]) st.2.2.1 mg.2.2.2 mg.2.2.1
      ((slots\assigned)\J) (Finset.sdiff_subset.trans Finset.sdiff_subset)
      ((actualCellLabels p S d).filter Squarefree) ?_ s
    intro I hI
    exact ⟨actual_cell_labels_admissible p hp hg hc S d I hI,(hlabels.2 d I hI).2.2⟩

end SevenEighths.InverseMoment

end

end OAI
