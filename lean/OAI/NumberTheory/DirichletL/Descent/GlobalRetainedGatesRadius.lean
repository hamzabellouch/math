import OAI.NumberTheory.DirichletL.Descent.GlobalRetainedGatesGeometry

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentGlobalRetainedGates
open InverseMoment InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityRetainedSource InversePrioritySecondSource InverseInitialArithmetic
open InverseSecondUniformCutoff
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ] {Jo : ℕ}
variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

def supportedRetainedSource (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ) (b X : ℝ) : Finset (MarkedSecondSource ι (Jo+(J.card+J.card)) 0) :=
  geometrySource p (retainedSource p extra original negative J lists pool cutoff) b X

lemma supported_subset (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ) (b X : ℝ) :
    supportedRetainedSource p extra original negative J lists pool cutoff b X⊆
      retainedSource p extra original negative J lists pool cutoff := geometrySource_subset p _ b X

lemma supported_conditions (hp : ∀i,p i≠0)
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (hvalid : ∀x∈original,SourceValid p x) (hextra : ∀x∈original,extra x.cube⊆x.cube.support)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ) (b X : ℝ) :
    ActualSecondSourceConditions p (supportedRetainedSource p extra original negative J lists pool cutoff b X) :=
  ActualSecondSourceConditions.mono p (retained_conditions p hp extra original hvalid hextra negative J lists pool cutoff)
    (supported_subset p extra original negative J lists pool cutoff b X)

lemma supported_frequency_ne_zero
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ) (b X : ℝ) :
    ∀x∈supportedRetainedSource p extra original negative J lists pool cutoff b X,x.second.frequency≠0 := by
  intro x hx
  exact unified_frequency_ne_zero p pool _ (fun _=>cutoff) x
    (supported_subset p extra original negative J lists pool cutoff b X hx)

lemma supported_uniform_frequency_gate
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (Z delta eta L Y tau b X : ℝ) :
    ∀x∈supportedRetainedSource p extra original negative J lists pool
      (fun G E=>uniformSecondRadius p Z delta eta G E L Y (Z^tau)) b X,
      x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
        (uniformSecondRadius p Z delta eta x.second.sourceCommon x.second.divisor L Y (Z^tau)) := by
  intro x hx
  exact ((mem_unifiedSource p pool _ _ x).mp
    (supported_subset p extra original negative J lists pool _ b X hx)).2.2.2.2

theorem supported_cell_row_gates (hp : ∀i,p i≠0)
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (Z M r ell V delta A B j t eta tau L b X : ℝ)
    (hZ : 1<Z) (heta : 0≤eta) (hbin : 2≤Z^eta) (hL0 : 0≤L)
    (hL : L≤Z^(r-A-B-t+4*eta)) :
    let source := supportedRetainedSource p extra original negative J lists pool
      (fun G E=>uniformSecondRadius p Z delta eta G E L
        (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)) (Z^tau)) b X
    (∀x∈source,x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (actualCellRowRadius Z M ell A t V j eta (index p x))) ∧
    (∀d∈keys p source,0≤actualCellRowExponent Z M ell A t V j eta d) := by
  intro source
  have hgates := actual_cell_uniform_source_gates p hp source Z M r ell V delta A B j t eta tau L
    hZ heta hbin hL0 hL (supported_uniform_frequency_gate p extra original negative J lists pool Z delta eta L _ tau b X)
  refine ⟨?_,actual_cell_radius_nonnegative_on_keys p source Z M ell A t V j eta hZ hgates⟩
  intro x hx
  exact hgates (index p x) x (Finset.mem_filter.mpr ⟨hx,rfl⟩)

end SevenEighths.InverseMomentGlobalRetainedGates
end

end OAI
