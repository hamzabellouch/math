import OAI.NumberTheory.DirichletL.Descent.FirstLabelCellStepData

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentFirstLabelCell
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseFirstPriorityParents InverseFirstGlobalParents
open InverseMomentGlobalRetainedGates InverseInitialArithmetic InverseSecondSourceBlocks
open InverseSecondUniformCutoff InversePrioritySecondSource
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
variable (p : ι→O) (hp : ∀i,p i≠0)

def parentWeight (l : ℕ) (x : Source ι 0) : ℂ :=
  (‖commonSelector p (fun _=>1) l x.quotientSupport‖:ℂ)

lemma parentWeight_norm (l : ℕ) (x : Source ι 0) : ‖parentWeight p l x‖≤1 := by
  simp only [parentWeight,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  simpa using InverseFirstGlobalCaps.commonSelector_norm p (fun _=>1) l x.quotientSupport

lemma secondCutoff_nonneg (Z M r ell V eta tau window : ℝ) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (hZ : 0<Z) (G E : Finset ι) :
    0≤secondCutoff p Z M r ell V eta tau window k l j negative G E := by
  apply uniformSecondRadius_nonneg _ _ _ _ _ _ _ _ _ hZ.le
  · unfold firstCellRadius
    positivity
  · exact Real.rpow_nonneg hZ.le _

include hp in
theorem secondCutoff_dominates (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (Z M r ell V eta tau window : ℝ) (hZ : 1<Z) (hbin : 2≤Z^eta) :
    ∀y∈InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k l j,∀G E : Finset ι,
      correlatedSecondRadius p (secondParentDivisor p (parent p y)) G E
        (columnScale Z r k l negative*Real.exp window) (firstCellRadius Z M r ell V eta tau k j) (Z^tau)≤
      secondCutoff p Z M r ell V eta tau window k l j negative G E := by
  intro y hy G E
  have hd := (InverseFirstGlobalCaps.parentCell_ideal_bounds p hp pool Q (fun _ _=>1) k l
    Z eta hZ hbin y (Finset.mem_filter.mp hy).1).2.1.2
  apply correlated_le_uniform p Z (exponent Z (k 3)) eta _ G E _ _ _
    (by unfold firstCellRadius;exact Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
    (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
  simpa [secondParentDivisor,parent,InverseFirstGlobalCaps.sourceIdeal_norm,
    primeSubsetGenerator_norm_eq_productNorm] using hd

include hp in
theorem parent_tail_caps (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (Z ell eta Lcap : ℝ) (hZ : 1<Z) (heta : 0≤eta) (hbin : 2≤Z^eta) (hcap : 0≤Lcap)
    (hQ : ∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
    (hell : ell+eta≤Lcap) (hactive : exponent Z (k 4)+eta≤Lcap)
    (hcommon : exponent Z (k 2)+eta≤Lcap) (hquot : exponent Z l+eta≤Lcap) :
    ∀y∈InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k l j,
      ‖eisEmbedding (primeProduct p y.cube.support y.cube.leftExponent)‖^2≤Z^Lcap ∧
      ‖eisEmbedding (primeProduct p y.cube.support y.cube.rightExponent)‖^2≤Z^Lcap ∧
      ‖eisEmbedding (∏i∈cubeActiveSupport y.cube.support
        (fun i=>y.cube.leftExponent i+y.cube.rightExponent i) y.cube.leftBit y.cube.rightBit,p i)‖≤Z^Lcap ∧
      primeProductNorm p y.firstCommon≤Z^Lcap ∧ primeProductNorm p y.quotientSupport≤Z^Lcap := by
  intro y hy
  have hb := label_parent_bounds p hp pool Q k l j Z ell eta hZ heta hbin hQ y hy
  have hpw {a : ℝ} (ha : a≤Lcap) : Z^a≤Z^Lcap := Real.rpow_le_rpow_of_exponent_le hZ.le ha
  refine ⟨hb.1.trans (hpw hell),hb.2.1.trans (hpw hell),?_,
    hb.2.2.2.1.trans (hpw hcommon),hb.2.2.2.2.1.trans (hpw hquot)⟩
  have he := hb.2.2.1.trans (hpw hactive)
  have hone := Real.one_le_rpow hZ.le hcap
  change ‖eisEmbedding (∏i∈_,p i)‖^2≤Z^Lcap at he
  have hn := norm_nonneg (eisEmbedding (∏i∈cubeActiveSupport y.cube.support
    (fun i=>y.cube.leftExponent i+y.cube.rightExponent i) y.cube.leftBit y.cube.rightBit,p i))
  nlinarith

end SevenEighths.InverseMomentFirstLabelCell
end

end OAI
