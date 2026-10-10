import OAI.Combinatorics.EditApproximation.Refinement.PhysicalQueryProgress
import OAI.Combinatorics.EditApproximation.Geometry.RefinementSupportBudget
import OAI.Combinatorics.EditApproximation.Refinement.ComputedEarlierHistory

namespace OAI

/-! The actual refinement query, including the reads used to construct
its initial and mass data, satisfies the two dependency branching budgets.
Only nonnegativity of the actual initial query value is used. -/

namespace EditApproximation

theorem computed_data_support_budget {nx ny M : ℕ} (parent : TargetInterval nx)
    (N P T : ℕ) (hN : 0 < N) (hell : 200 ≤ inputSmallLog N)
    (hM : M = (integerParameters N).M) (hP : P = (integerParameters N).P)
    (hT : T = (integerParameters N).T)
    (A : ℚ) (hA : A ≤ ((integerParameters N).initialFactor : ℚ))
    (initial : TargetInterval ny → ℚ) (q : TargetInterval ny) (hw : 0 ≤ initial q) :
    (refinementInitialSupport N P (inputSmallLog N) (40 * smallLogExponent N)
      (refinementFactor A (inputSmallLog N)) (initial q) q).length ≤
        1 + inputHeight N ^ (256 * (coarseExponent (inputSmallLog N) + 1)) ∧
    (refinementBandInputList (M := M) parent N P (inputSmallLog N) (40 * smallLogExponent N)
      (refinementFactor A (inputSmallLog N)) initial q).length * (T + 1) ≤
        inputHeight N ^ (256 * (coarseExponent (inputSmallLog N) + 1)) := by
  let H := inputHeight N
  let ell := inputSmallLog N
  let W := (dyadicQueryWindow N (initial q) (refinementFactor A ell) ell).length
  let C := ((32 * ell + 2) * 2 ^ (40 * smallLogExponent N) + 2) ^ 2
  let R := (64 * ell * P + 2) ^ 2 + C * (P + 1) ^ 2 + 1
  let history := (integerParameters N).T + (integerParameters N).S + 1
  let budget := localEarlierBudget W C M P ell history
  have hF : ell ≤ H := computed_smallLog_le_height N
  have hH : 64 ≤ H := (by omega : 64 ≤ ell).trans hF
  have hPpos : 1 ≤ P := by rw [hP]; exact one_le_pow₀ Nat.one_le_two_pow
  have hPpower : P ≤ H ^ (coarseExponent ell + 20) := by rw [hP]; exact le_rfl
  have hMpos : 0 < M := by
    rw [hM]
    change 0 < 2 ^ _
    exact Nat.two_pow_pos _
  have hMbound : M ≤ H := by
    rw [hM]
    exact pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) (Nat.div_le_self _ _)
  have hW : W ≤ H ^ 3 :=
    (computed_refinement_window N hN (by omega) A (initial q) hA).trans
      (computed_window_le_height_cube N hN (by omega) (by omega))
  have hbudget : budget ≤ H ^ (256 * (coarseExponent ell + 1)) :=
    localEarlierBudget_poly H (coarseExponent ell) W C M P ell history hH hPpos hPpower hW
      (computed_cell_budget_le_height_pow N hH) hMbound hF
      (computed_history_budget_le_height_sq N (by omega))
  have hhistory : T + 1 ≤ history := by dsimp only [history]; omega
  have hwide : 0 < (40 * P + 2) ^ 2 := by positivity
  have hfactor : 0 < M * history * (40 * P + 2) ^ 2 := by positivity
  have hraw : W * R ≤ budget := by
    have h := Nat.le_mul_of_pos_right (W * R) hfactor
    exact h.trans_eq (by dsimp only [budget, localEarlierBudget, R]; ring)
  have hband : W * R * M * (40 * P + 2) ^ 2 * (T + 1) ≤ budget := by
    apply (Nat.mul_le_mul_left (W * R * M * (40 * P + 2) ^ 2) hhistory).trans_eq
    dsimp only [budget, localEarlierBudget, R]
    ring
  have hdyadic : ∃ e : ℕ, P = 2 ^ e := ⟨_, hP.trans (computed_P_dyadic N)⟩
  constructor
  · exact (refinementInitialSupport_length N P ell (40 * smallLogExponent N)
      (refinementFactor A ell) (initial q) q hdyadic (by omega) hw).trans
      (Nat.add_le_add_left (hraw.trans hbudget) 1)
  · exact (Nat.mul_le_mul_right (T + 1)
      (refinementBandInputList_length parent N P ell (40 * smallLogExponent N)
        (refinementFactor A ell) initial q hdyadic (by omega) hw)).trans (hband.trans hbudget)

theorem computed_physicalRefinement_current_reads {α : Type*} (source target : List α)
    {M J : ℕ} (N P H : ℕ) (hN : 0 < N) (hell : 200 ≤ inputSmallLog N)
    (hM : M = (integerParameters N).M)
    (A tau eta kappa delta : ℚ) (hA : A ≤ ((integerParameters N).initialFactor : ℚ))
    (pass copy T S t : ℕ) (ht : 0 < t)
    (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (draw : CellGroupDraws M (inputSmallLog N) (inputSmallLog N ^ 80))
    (integer : ℕ → TargetInterval target.length → ℕ)
    (q : TargetInterval target.length) (answer : PhysicalTableRequest M J target.length → ℚ)
    (hw : 0 ≤ answer (PhysicalTableRequest.warmup pass copy node 0 q)) :
    (physicalRefinementDataRequestQuery source target N P (inputSmallLog N)
      (40 * smallLogExponent N) H (inputSmallLog N ^ 80) tau
      (refinementFactor A (inputSmallLog N)) eta kappa delta pass copy T S t ht node hbelow
      draw integer q).cost (fun request => answer request.val)
        (fun request => physicalCurrentReadWeight (T + t) request.val) ≤
      2 * M * inputSmallLog N ^ 256 := by
  subst M
  let initial := fun r => answer (PhysicalTableRequest.warmup pass copy node 0 r)
  let mass := fun i r => (∑ j : Fin T, answer (PhysicalTableRequest.warmup pass copy
    (physicalChild node hbelow i) j.val r)) / T
  let childInitial := fun i r => answer (PhysicalTableRequest.warmup pass copy
    (physicalChild node hbelow i) 0 r)
  let current := fun i r => answer (PhysicalTableRequest.refinement pass copy
    (physicalChild node hbelow i) T t r)
  let children := fun i s r => if s < t then answer (PhysicalTableRequest.refinement pass copy
    (physicalChild node hbelow i) T s r) else 0
  have hcard := computed_currentQueryInputCover_card source target N P hN hell
    (physicalSourceInterval source.length node) A tau hA initial mass childInitial current draw q hw
    (localOnlineCandidates source target (physicalSourceInterval source.length node)
      N P (inputSmallLog N) (40 * smallLogExponent N) H tau (refinementFactor A (inputSmallLog N))
      eta kappa initial mass childInitial children (t - 1) integer q)
    (localOnlineCandidates_length source target (physicalSourceInterval source.length node)
      N P (inputSmallLog N) (40 * smallLogExponent N) H tau (refinementFactor A (inputSmallLog N))
      eta kappa initial mass childInitial children (t - 1) integer q)
  have hread := physicalRefinementDataRequest_current_reads source target N P (inputSmallLog N)
    (40 * smallLogExponent N) H (inputSmallLog N ^ 80) tau (refinementFactor A (inputSmallLog N))
    eta kappa delta pass copy T S t ht node hbelow draw integer q answer
  apply hread.trans
  convert Nat.mul_le_mul_left 2 hcard using 1 <;> first | rfl | exact Nat.mul_assoc _ _ _

theorem computed_physicalRefinement_earlier_reads {α : Type*} (source target : List α)
    {M J : ℕ} (N P H : ℕ) (hN : 0 < N) (hell : 200 ≤ inputSmallLog N)
    (hM : M = (integerParameters N).M) (hP : P = (integerParameters N).P)
    (A tau eta kappa delta : ℚ) (hA : A ≤ ((integerParameters N).initialFactor : ℚ))
    (pass copy T S t : ℕ) (hT : T = (integerParameters N).T)
    (ht : 0 < t) (htime : t ≤ (integerParameters N).S)
    (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (draw : CellGroupDraws M (inputSmallLog N) (inputSmallLog N ^ 80))
    (integer : ℕ → TargetInterval target.length → ℕ)
    (q : TargetInterval target.length) (answer : PhysicalTableRequest M J target.length → ℚ)
    (hw : 0 ≤ answer (PhysicalTableRequest.warmup pass copy node 0 q)) :
    (physicalRefinementDataRequestQuery source target N P (inputSmallLog N)
      (40 * smallLogExponent N) H (inputSmallLog N ^ 80) tau
      (refinementFactor A (inputSmallLog N)) eta kappa delta pass copy T S t ht node hbelow
      draw integer q).cost (fun request => answer request.val)
        (fun request => physicalEarlierReadWeight (T + t) request.val) ≤
      inputHeight N ^ (257 * (coarseExponent (inputSmallLog N) + 1)) := by
  let initial := fun r => answer (PhysicalTableRequest.warmup pass copy node 0 r)
  let B := inputHeight N ^ (256 * (coarseExponent (inputSmallLog N) + 1))
  have hdata := computed_data_support_budget (physicalSourceInterval source.length node)
    N P T hN hell hM hP hT A hA initial q hw
  have hcover : (queryEarlierInputCover (M := M) (physicalSourceInterval source.length node)
      N P (inputSmallLog N) (40 * smallLogExponent N) t
      (refinementFactor A (inputSmallLog N)) initial q).card ≤ B := by
    subst M
    exact computed_queryEarlierHistory_card (physicalSourceInterval source.length node)
      N P t hN hell hP (by omega) A hA initial q hw
  dsimp only [initial] at hdata hcover
  have hread := physicalRefinementDataRequest_earlier_reads source target N P (inputSmallLog N)
    (40 * smallLogExponent N) H (inputSmallLog N ^ 80) tau (refinementFactor A (inputSmallLog N))
    eta kappa delta pass copy T S t ht node hbelow draw integer q answer
  dsimp only at hread
  have hsum : (physicalRefinementDataRequestQuery source target N P (inputSmallLog N)
      (40 * smallLogExponent N) H (inputSmallLog N ^ 80) tau
      (refinementFactor A (inputSmallLog N)) eta kappa delta pass copy T S t ht node hbelow
      draw integer q).cost (fun request => answer request.val)
        (fun request => physicalEarlierReadWeight (T + t) request.val) ≤ 2 + 3 * B := by
    omega
  have hHeight : 64 ≤ inputHeight N :=
    (by omega : 64 ≤ inputSmallLog N).trans (computed_smallLog_le_height N)
  have hB : 1 ≤ B := one_le_pow₀ (by omega)
  have hfinal : 2 + 3 * B ≤ inputHeight N ^ (257 * (coarseExponent (inputSmallLog N) + 1)) := by
    calc
      _ ≤ 5 * B := by omega
      _ ≤ inputHeight N * B := Nat.mul_le_mul_right B (by omega)
      _ = inputHeight N ^ (1 + 256 * (coarseExponent (inputSmallLog N) + 1)) := by
        dsimp only [B]
        rw [pow_add, pow_one]
      _ ≤ _ := pow_le_pow_right₀ (by omega) (by omega)
  exact hsum.trans hfinal

end EditApproximation

end OAI
