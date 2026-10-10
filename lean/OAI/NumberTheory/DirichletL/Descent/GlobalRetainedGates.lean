import OAI.NumberTheory.DirichletL.Inversion.SecondUniformCutoff
import OAI.NumberTheory.DirichletL.Descent.ActualChildStateTriples
import OAI.NumberTheory.DirichletL.Descent.GlobalPrioritySource

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentGlobalRetainedGates
open InverseMoment InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityRetainedSource InversePrioritySecondSource InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ] {Jo : ℕ}
variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

def retainedSource (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ) : Finset (MarkedSecondSource ι (Jo+(J.card+J.card)) 0) :=
  unifiedSource p pool (wholeAssignedParents p (fun x=>extra x.cube) original negative J lists) (fun _=>cutoff)

lemma original_parent_witness
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ)
    (x : MarkedSecondSource ι (Jo+(J.card+J.card)) 0)
    (hx : x∈retainedSource p extra original negative J lists pool cutoff) :
    ∃y∈original,forgetAppended (Jo:=Jo) (secondParentOf x)=parent p y := by
  have hp := ((mem_unifiedSource p pool _ (fun _=>cutoff) x).mp hx).1
  obtain ⟨y,hy,q,hq,he⟩ := (mem_wholeAssignedParents p (fun x=>extra x.cube) original negative J lists _).mp hp
  exact ⟨y,hy,by simpa only [forget_attach] using congrArg (forgetAppended (Jo:=Jo)) he.symm⟩

lemma original_coordinates
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ)
    (x : MarkedSecondSource ι (Jo+(J.card+J.card)) 0)
    (hx : x∈retainedSource p extra original negative J lists pool cutoff) :
    ∃y∈original,x.cube=y.cube ∧ x.firstCommon=y.firstCommon ∧
      x.firstDivisor=y.firstDivisor ∧ x.quotient=sourceIdeal p y.quotientSupport ∧
      (∀i:Fin Jo,x.oldAssigned (Fin.castAdd (J.card+J.card) i)=y.oldAssigned i) := by
  obtain ⟨y,hy,he⟩ := original_parent_witness p extra original negative J lists pool cutoff x hx
  exact ⟨y,hy,congrArg SecondParentSource.cube he,congrArg SecondParentSource.firstCommon he,
    congrArg SecondParentSource.firstDivisor he,congrArg SecondParentSource.quotient he,
    fun i=>congrArg (fun z=>z.oldAssigned i) he⟩

lemma retained_conditions (hp : ∀i,p i≠0)
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (hvalid : ∀x∈original,SourceValid p x) (hextra : ∀x∈original,extra x.cube⊆x.cube.support)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ) :
    ActualSecondSourceConditions p (retainedSource p extra original negative J lists pool cutoff) :=
  unified_conditions p hp extra original hvalid hextra negative J lists pool (fun _=>cutoff)

lemma original_numeric_gates (extra : CubeCoordinates ι→Finset ι)
    (original : Finset (Source ι Jo)) (negative : Bool) (J : Finset σ)
    (lists : σ→Finset ι) (pool : Finset ι) (cutoff : Finset ι→Finset ι→ℝ)
    (B A C Q JL JU D : ℝ)
    (hB₁ : ∀y∈original,‖eisEmbedding (primeProduct p y.cube.support y.cube.leftExponent)‖^2≤B)
    (hB₂ : ∀y∈original,‖eisEmbedding (primeProduct p y.cube.support y.cube.rightExponent)‖^2≤B)
    (hA : ∀y∈original,primeProductNorm p (cubeActiveSupport y.cube.support
      (fun i=>y.cube.leftExponent i+y.cube.rightExponent i) y.cube.leftBit y.cube.rightBit)≤A)
    (hC : ∀y∈original,primeProductNorm p y.firstCommon≤C)
    (hQ : ∀y∈original,primeProductNorm p y.quotientSupport≤Q)
    (hJ : ∀y∈original,JL≤‖eisEmbedding (jLabel p y.cube.support
      (fun i=>y.cube.leftExponent i+y.cube.rightExponent i) y.cube.leftBit y.cube.rightBit)‖^2 ∧
      ‖eisEmbedding (jLabel p y.cube.support (fun i=>y.cube.leftExponent i+y.cube.rightExponent i)
        y.cube.leftBit y.cube.rightBit)‖^2≤JU)
    (hD : ∀y∈original,primeProductNorm p y.firstDivisor≤D) :
    ∀x∈retainedSource p extra original negative J lists pool cutoff,
      ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤B ∧
      ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤B ∧
      primeProductNorm p (cubeActiveSupport x.cube.support (fun i=>x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit)≤A ∧ primeProductNorm p x.firstCommon≤C ∧
      (Ideal.absNorm x.quotient:ℝ)≤Q ∧
      JL≤‖eisEmbedding (jLabel p x.cube.support (fun i=>x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit)‖^2 ∧
      ‖eisEmbedding (jLabel p x.cube.support (fun i=>x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit)‖^2≤JU ∧
      primeProductNorm p x.firstDivisor≤D := by
  intro x hx
  obtain ⟨y,hy,hb,hc,hd,hq,ho⟩ := original_coordinates p extra original negative J lists pool cutoff x hx
  rw [hb,hc,hd,hq]
  refine ⟨hB₁ y hy,hB₂ y hy,hA y hy,hC y hy,?_,(hJ y hy).1,(hJ y hy).2,hD y hy⟩
  simpa only [sourceIdeal,←eisEmbedding_norm_sq_eq_absNorm_span,primeProductNorm] using hQ y hy

end SevenEighths.InverseMomentGlobalRetainedGates
end

end OAI
