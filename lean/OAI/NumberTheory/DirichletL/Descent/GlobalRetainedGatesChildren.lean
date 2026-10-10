import OAI.NumberTheory.DirichletL.Descent.GlobalRetainedGatesRadius

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentGlobalRetainedGates
open InverseMoment InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityRetainedSource InversePrioritySecondSource InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open InverseSecondFibers CompletedGauss
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ] {Jo : ℕ}
variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

lemma supported_original_property
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ) (b X : ℝ)
    (F : CubeCoordinates ι→Finset ι→Finset ι→Ideal O→Prop)
    (hF : ∀y∈original,F y.cube y.firstCommon y.firstDivisor (sourceIdeal p y.quotientSupport)) :
    ∀x∈supportedRetainedSource p extra original negative J lists pool cutoff b X,
      F x.cube x.firstCommon x.firstDivisor x.quotient := by
  intro x hx
  obtain ⟨y,hy,hb,hc,hd,hq,ho⟩ := original_coordinates p extra original negative J lists pool cutoff x
    (supported_subset p extra original negative J lists pool cutoff b X hx)
  rw [hb,hc,hd,hq]
  exact hF y hy

theorem supported_label_gates (hp : ∀i,p i≠0)
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ) (b X Z B j eta : ℝ) (hZ : 1<Z) (hbin : 2≤Z^eta)
    (hC : ∀y∈original,primeProductNorm p y.firstCommon≤Z^(B+eta))
    (hJ : ∀y∈original,‖eisEmbedding (jLabel p y.cube.support
      (fun i=>y.cube.leftExponent i+y.cube.rightExponent i) y.cube.leftBit y.cube.rightBit)‖^2≤Z^(j+eta)) :
    let source := supportedRetainedSource p extra original negative J lists pool cutoff b X
    (∀d,∀x∈cell p source d,(actualSecondChild p 1 1 x).2.1∈actualCellLabels p source d) ∧
    (∀d,∀I∈(actualCellLabels p source d).filter Squarefree,
      Squarefree I ∧ I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^(actualCellLabelExponent Z B j eta d)) := by
  intro source
  have hc := supported_original_property p extra original negative J lists pool cutoff b X
    (fun _ C _ _=>primeProductNorm p C≤Z^(B+eta)) hC
  have hj := supported_original_property p extra original negative J lists pool cutoff b X
    (fun q _ _ _=>‖eisEmbedding (jLabel p q.support
      (fun i=>q.leftExponent i+q.rightExponent i) q.leftBit q.rightBit)‖^2≤Z^(j+eta)) hJ
  exact ⟨fun d x hx=>actual_cell_labels_cover p source d x hx,
    fun d=>actual_cell_squarefree_labels p hp source
      (supported_frequency_ne_zero p extra original negative J lists pool cutoff b X) d Z B j eta hZ hbin hc hj⟩

theorem supported_child_margins (hp : ∀i,p i≠0)
    (hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (hvalid : ∀x∈original,SourceValid p x) (hextra : ∀x∈original,extra x.cube⊆x.cube.support)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ) (b : ℝ) (m : O) (hm : m≠0)
    (Z r ell V M Q z c A B t j eta : ℝ) (hZ : 1<Z)
    (hparent : CanonicalMargins (r+3*ell+V) M Q z c)
    (hA : 0≤A) (ht : 0≤t) (hV : 0≤V) (hj : 0≤j) (heta : 0≤eta) (hbin : 2≤Z^eta)
    (hQ : (Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤Z^Q)
    (h1 : ∀y∈original,‖eisEmbedding (primeProduct p y.cube.support y.cube.leftExponent)‖^2≤Z^(ell+eta))
    (h2 : ∀y∈original,‖eisEmbedding (primeProduct p y.cube.support y.cube.rightExponent)‖^2≤Z^(ell+eta))
    (hT : ∀y∈original,primeProductNorm p y.quotientSupport≤Z^(t+eta)) :
    let source := supportedRetainedSource p extra original negative J lists pool cutoff b (Z^(r-A-B-t))
    ∀d,∀γ∈actualSecondTriples p 1 1 (cell p source d),
      actualSecondInheritedRadicalPuncture m γ≠0 ∧ 0≤actualSecondPunctureWidth Z m γ ∧
      ‖eisEmbedding (actualSecondInheritedRadicalPuncture m γ)‖^2=Z^(actualSecondPunctureWidth Z m γ) ∧
      CanonicalMargins (actualCellTotalExponent Z (Z^(r-A-B-t)) B j eta d)
        (childM M ell A t (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j eta)
        (actualSecondPunctureWidth Z m γ) z (c-7*eta) := by
  intro source d γ hγ
  have hs := supported_conditions p hp extra original hvalid hextra negative J lists pool cutoff b (Z^(r-A-B-t))
  have hk := supported_frequency_ne_zero p extra original negative J lists pool cutoff b (Z^(r-A-B-t))
  have hb₁ := supported_original_property p extra original negative J lists pool cutoff b (Z^(r-A-B-t))
    (fun q _ _ _=>‖eisEmbedding (primeProduct p q.support q.leftExponent)‖^2≤Z^(ell+eta)) h1
  have hb₂ := supported_original_property p extra original negative J lists pool cutoff b (Z^(r-A-B-t))
    (fun q _ _ _=>‖eisEmbedding (primeProduct p q.support q.rightExponent)‖^2≤Z^(ell+eta)) h2
  have hq := supported_original_property p extra original negative J lists pool cutoff b (Z^(r-A-B-t))
    (fun _ _ _ I=>(Ideal.absNorm I:ℝ)≤Z^(t+eta)) (by
      intro y hy
      simpa only [sourceIdeal,←eisEmbedding_norm_sq_eq_absNorm_span,primeProductNorm] using hT y hy)
  exact actual_cell_triple_margins p hp hpr source hs hk d m hm
    Z r ell V M Q z c A B t j eta hZ hparent hA ht hV hj heta hbin hQ hb₁ hb₂ hq γ hγ

end SevenEighths.InverseMomentGlobalRetainedGates
end

end OAI
