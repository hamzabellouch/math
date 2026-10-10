import OAI.Combinatorics.EditApproximation.Geometry.PreparedCachedKernelWork
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalCachedWords

namespace OAI

/-! The Boolean refinement kernel at a physical node uses cached words
for its child and table requests. -/

namespace EditApproximation

attribute [local irreducible] BinaryFraction.preparedLocalKernelWithWork

section Step

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
  (source target : List α) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tauWord aWord etaWord kappaWord deltaWord : BinaryFraction)
  (parentWords : TargetInterval target.length → BinaryFraction)
  (massWords initialWords : Fin M → TargetInterval target.length → BinaryFraction)
  (historyWords : ℕ → Fin M × TargetInterval target.length → BinaryFraction)
  (draw : PhysicalInternalNode M J → ℕ → CellGroupDraws M F Q)
  (integer : PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
  (node : PhysicalNode M J) (hbelow : node.1.val < J) (t : ℕ)
  (query : TargetInterval target.length)

def physicalPreparedStepWithWork : BinaryFraction × ℕ :=
  BinaryFraction.preparedLocalKernelWithWork source target (physicalSourceInterval source.length node)
    N P F exponent H Q eM eF hP hM hF tauWord aWord etaWord kappaWord deltaWord
    parentWords massWords initialWords (historyWords t) (historyWords (t + 1)) historyWords t
    (draw ⟨node, hbelow⟩ (t + 1)) (integer ⟨node, hbelow⟩ (Fin.ofNat R t)) query

omit [DecidableEq α] in
theorem physicalPreparedStepWithWork_bounds (B E S : ℕ) (hPdyadic : ∃ j : ℕ, P = 2 ^ j)
    (hb : BinaryFraction.PreparedKernelInputBounds (nx := source.length)
      N P F exponent H Q eM eF B E S t tauWord aWord etaWord kappaWord deltaWord
      parentWords massWords initialWords (historyWords t) (historyWords (t + 1)) historyWords
      (integer ⟨node, hbelow⟩ (Fin.ofNat R t))) :
    (physicalPreparedStepWithWork source target N P F exponent H Q eM eF hP hM hF
      tauWord aWord etaWord kappaWord deltaWord parentWords massWords initialWords historyWords
      draw integer node hbelow t query).1.width ≤ BinaryFraction.preparedKernelWordBudget M B ∧
    (physicalPreparedStepWithWork source target N P F exponent H Q eM eF hP hM hF
      tauWord aWord etaWord kappaWord deltaWord parentWords massWords initialWords historyWords
      draw integer node hbelow t query).2 ≤ BinaryFraction.preparedKernelBitBudget N M P F exponent eM eF B S :=
  BinaryFraction.preparedLocalKernelWithWork_bounds source target (physicalSourceInterval source.length node)
    N P F exponent H Q eM eF B E S hP hM hF hPdyadic tauWord aWord etaWord kappaWord deltaWord
    parentWords massWords initialWords (historyWords t) (historyWords (t + 1)) historyWords t
    (draw ⟨node, hbelow⟩ (t + 1)) (integer ⟨node, hbelow⟩ (Fin.ofNat R t)) query hb

variable (U : PhysicalEntry M J target.length → ℕ) (A tau eta kappa delta : ℚ) (T : ℕ)
  (ha : aWord.value = refinementFactor A F) (htau : tauWord.value = tau)
  (heta : etaWord.value = eta) (hkappa : kappaWord.value = kappa)
  (hdelta : deltaWord.value = delta)
  (hparent : ∀ r, (parentWords r).value = stageInitial source target U N P F A (node, r))
  (hmass : ∀ i r, (massWords i r).value =
    physicalLocalChildMass source target U N P F A T node hbelow i r)
  (hinitial : ∀ i r, (initialWords i r).value =
    stageInitial source target U N P F A (physicalChild node hbelow i, r))
  (hhistory : ∀ s i r, (historyWords s (i, r)).value =
    physicalLocalRefinement source target U N P F exponent Q A tau delta T draw
      (physicalLocalOnline source target U N P F exponent H T A tau eta kappa integer)
      (physicalChild node hbelow i) s r)
  (hwide : ¬ (physicalSourceInterval source.length node).hi -
    (physicalSourceInterval source.length node).lo ≤ 1)

include ha htau heta hkappa hdelta hparent hmass hinitial hhistory hwide in
theorem physicalPreparedStepWithWork_value :
    (physicalPreparedStepWithWork source target N P F exponent H Q eM eF hP hM hF
      tauWord aWord etaWord kappaWord deltaWord parentWords massWords initialWords historyWords
      draw integer node hbelow t query).1.value =
    physicalLocalRefinement source target U N P F exponent Q A tau delta T draw
      (physicalLocalOnline source target U N P F exponent H T A tau eta kappa integer)
      node (t + 1) query := by
  let children : PhysicalChildTables M target.length := fun i =>
    physicalLocalRefinement source target U N P F exponent Q A tau delta T draw
      (physicalLocalOnline source target U N P F exponent H T A tau eta kappa integer)
      (physicalChild node hbelow i)
  have honline : physicalLocalOnline source target U N P F exponent H T A tau eta kappa integer
      node children (t + 1) query =
      localOnlineCandidates source target (physicalSourceInterval source.length node)
        N P F exponent H tau (refinementFactor A F) eta kappa
        (fun r => stageInitial source target U N P F A (node, r))
        (physicalLocalChildMass source target U N P F A T node hbelow)
        (physicalBandChildInitial source target U N P F A node hbelow)
        children t (integer ⟨node, hbelow⟩ (Fin.ofNat R t)) query := by
    rw [physicalLocalOnline, dite_eq_left hbelow]
    simp only [Nat.add_sub_cancel]
  unfold physicalPreparedStepWithWork
  rw [BinaryFraction.preparedLocalKernelWithWork_value]
  simp_rw [ha, htau, heta, hkappa, hdelta, hparent, hmass, hinitial, hhistory]
  conv_rhs => rw [physicalLocalRefinement]
  rw [dite_eq_left hbelow, ite_eq_right hwide]
  dsimp only
  rw [honline]
  rfl

include hparent hinitial hhistory in
theorem physicalPreparedStep_input_ranges (hd : 0 ≤ delta) :
    (∀ r, 0 ≤ (parentWords r).value) ∧
    (∀ s ≤ t + 1, ∀ i r, 0 ≤ (historyWords s (i, r)).value ∧
      (historyWords s (i, r)).value ≤ (initialWords i r).value) := by
  constructor
  · intro r
    rw [hparent]
    exact stageInitial_nonneg_all_seeds source target U N P F A (node, r)
  · intro s _hs i r
    rw [hhistory, hinitial]
    exact physicalLocalRefinement_bounds source target U N P F exponent Q A tau delta T hd draw
      (physicalLocalOnline source target U N P F exponent H T A tau eta kappa integer)
      (physicalChild node hbelow i) s r

def physicalCachedStepWithWork (base : List Bool) (hbase : 0 < bitWordValue base) :
    BinaryFraction × ℕ :=
  BinaryFraction.finishCachedWithWork
    (physicalPreparedStepWithWork source target N P F exponent H Q eM eF hP hM hF
      tauWord aWord etaWord kappaWord deltaWord parentWords massWords initialWords historyWords
      draw integer node hbelow t query) base hbase (J - node.1.val)

omit [DecidableEq α] in
theorem physicalCachedStepWithWork_cost (base : List Bool) (hbase : 0 < bitWordValue base)
    (B E S D : ℕ) (hbaseWidth : base.length ≤ D) (hPdyadic : ∃ j : ℕ, P = 2 ^ j)
    (hb : BinaryFraction.PreparedKernelInputBounds (nx := source.length)
      N P F exponent H Q eM eF B E S t tauWord aWord etaWord kappaWord deltaWord
      parentWords massWords initialWords (historyWords t) (historyWords (t + 1)) historyWords
      (integer ⟨node, hbelow⟩ (Fin.ofNat R t))) :
    (physicalCachedStepWithWork source target N P F exponent H Q eM eF hP hM hF
      tauWord aWord etaWord kappaWord deltaWord parentWords massWords initialWords historyWords
      draw integer node hbelow t query base hbase).2 ≤
      BinaryFraction.preparedKernelBitBudget N M P F exponent eM eF B S +
        BinaryFraction.powerDenominatorBitBudget (J - node.1.val)
          (BinaryFraction.preparedKernelWordBudget M B) D + 1 := by
  have hk := physicalPreparedStepWithWork_bounds source target N P F exponent H Q eM eF hP hM hF
    tauWord aWord etaWord kappaWord deltaWord parentWords massWords initialWords historyWords
    draw integer node hbelow t query B E S hPdyadic hb
  have hc := BinaryFraction.powerDenominatorWithWork_cost
    (physicalPreparedStepWithWork source target N P F exponent H Q eM eF hP hM hF
      tauWord aWord etaWord kappaWord deltaWord parentWords massWords initialWords historyWords
      draw integer node hbelow t query).1 base hbase (J - node.1.val)
    (BinaryFraction.preparedKernelWordBudget M B) D hk.1 hbaseWidth
  exact Nat.add_le_add_right (Nat.add_le_add hk.2 hc) 1

include ha htau heta hkappa hdelta hparent hmass hinitial hhistory hwide in
theorem physicalCachedStepWithWork_value_width (ell : ℕ) (hell : 0 < ell)
    (hdeltaExact : delta = 1 / (ell : ℚ) ^ 10)
    (hsize : source.length + target.length ≤ N) (base : List Bool)
    (hbase : bitWordValue base = ell ^ 10 + 1) :
    (physicalCachedStepWithWork source target N P F exponent H Q eM eF hP hM hF
      tauWord aWord etaWord kappaWord deltaWord parentWords massWords initialWords historyWords
      draw integer node hbelow t query base (by rw [hbase]; omega)).1.value =
      physicalLocalRefinement source target U N P F exponent Q A tau delta T draw
        (physicalLocalOnline source target U N P F exponent H T A tau eta kappa integer)
        node (t + 1) query ∧
    (physicalCachedStepWithWork source target N P F exponent H Q eM eF hP hM hF
      tauWord aWord etaWord kappaWord deltaWord parentWords massWords initialWords historyWords
      draw integer node hbelow t query base (by rw [hbase]; omega)).1.width ≤
      Nat.size ((32 * F + 1) * N) + 2 * (J - node.1.val) * base.length + 3 := by
  rcases hdeltaExact with rfl
  have hraw := physicalPreparedStepWithWork_value source target N P F exponent H Q eM eF hP hM hF
    tauWord aWord etaWord kappaWord deltaWord parentWords massWords initialWords historyWords
    draw integer node hbelow t query U A tau eta kappa _ T ha htau heta hkappa hdelta
    hparent hmass hinitial hhistory hwide
  have hstored := physicalLocalOnlineRefinement_cached_word source target U N P F exponent H Q A tau eta kappa
    hsize T ell hell draw integer node (t + 1) query _ hraw base hbase
  exact ⟨hstored.1.trans hraw, hstored.2⟩

end Step

end EditApproximation

end OAI
