import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.AmbientPivotPotential
import OAI.Combinatorics.RamseyFive.Entropy.VariableTreeCost
import OAI.Combinatorics.RamseyFive.Marking.WindowDeletionCount

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree Marking Windows
open ParameterHierarchy Filter
open scoped Classical BigOperators LinearAlgebra.Projectivization Topology NNReal
noncomputable section
local instance costBDE (w : ℕ) : DecidableEq (Fin w×Bool) := Classical.decEq _
local instance costIDE (w n : ℕ) : DecidableEq (Slots w n) := Classical.decEq _

def windowCodeBudget (σ q P b : ℝ) (w H : ℕ) : ℝ :=
  let X:=nodeChargeConstant*q*P
  Real.log (w+1)+
    (X*H*(3*σ+Real.log 4+(b+1+2*Real.log (320/((9:ℝ)/100000)+320))*w)+
      (Real.log 2+X*(b+1+P))*w)+(2*(w:ℝ)+1)*Real.log 2

lemma windowCodeBudget_ge_header {σ q P b : ℝ} (w H : ℕ)
    (hσ : 0≤σ) (hq : 0≤q) (hP : 0≤P) (hb : 0≤b) :
    Real.log (w+1)≤windowCodeBudget σ q P b w H := by
  have hc : 0≤nodeChargeConstant := nodeChargeConstant_nonneg
  have hl : 0≤Real.log (320/((9:ℝ)/100000)+320) := Real.log_nonneg (by norm_num)
  unfold windowCodeBudget
  have hl2 : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have hl4 : 0≤Real.log 4 := Real.log_nonneg (by norm_num)
  have hh : 0≤(nodeChargeConstant*q*P*H*(3*σ+Real.log 4+(b+1+2*Real.log (320/((9:ℝ)/100000)+320))*w)+
      (Real.log 2+nodeChargeConstant*q*P*(b+1+P))*w)+(2*(w:ℝ)+1)*Real.log 2 := by positivity
  linarith

lemma windowCodeBudget_mono {σ q P b G : ℝ} {m w h H : ℕ}
    (_hσ : 0≤σ) (hq : 0≤q) (hP : 0≤P) (hb : 0≤b) (hG : 0≤G)
    (hG' : G≤3*σ+Real.log 4) (hm : m≤w) (hh : h≤H) :
    Real.log (w+1)+
      (nodeChargeConstant*q*P*h*(G+(b+1+2*Real.log (320/((9:ℝ)/100000)+320))*m)+
        (Real.log 2+nodeChargeConstant*q*P*(b+1+P))*m)+(2*(m:ℝ)+1)*Real.log 2≤
      windowCodeBudget σ q P b w H := by
  have hc : 0≤nodeChargeConstant := nodeChargeConstant_nonneg
  have hl : 0≤Real.log (320/((9:ℝ)/100000)+320) := Real.log_nonneg (by norm_num)
  have hl2 : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have hm' : (m:ℝ)≤w := by exact_mod_cast hm
  have hh' : (h:ℝ)≤H := by exact_mod_cast hh
  apply add_le_add
  · apply add_le_add le_rfl
    apply add_le_add
    · exact mul_le_mul (mul_le_mul_of_nonneg_left hh' (by positivity))
        (add_le_add hG' (mul_le_mul_of_nonneg_left hm' (by positivity)))
        (by positivity) (by positivity)
    · exact mul_le_mul_of_nonneg_left hm' (by positivity)
  · exact mul_le_mul_of_nonneg_right (by linarith) hl2

theorem eventually_allWindow_cost {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D k s : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))],
    ∀ (hd : finrank K V=5) (w n H : ℕ) [Nonempty (Fin n)]
      (p : Law (Slots w n→FlagPair K V)) (u : Slots w n→ℝ) (sel : Fin w×Bool→Fin n)
      (E : Finset (Fin w))
      (W : ∀hE : E.Nonempty,ReciprocalWindows p u sel (survivingOriginal E hE) s)
      (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K),
      Nat.card K=q → Range η σ D R → (L₀:ℝ)=L η σ D →
      0≤k+2*s+Real.log 4 → k+2*s+Real.log 4≤Cb*D*σ^(6*beta η) →
      (∀v∈E,u (earlySlot sel v)-u (lateSlot sel v)≤k) → w<2^H →
      let f := fun C : PivotContext K V =>
        fourFinitePredictor hd σ C.1 C.2 (P η σ D R) (σ^(-800*beta η)) R L₀
      let r := fun C : PivotContext K V =>
        fourFinitePredictor (K:=K) (V:=Dual K V) (by simpa using hd) σ C.2
          (C.1.map bidualPoint.toEmbedding) (P η σ D R) (σ^(-800*beta η)) R L₀
      ∀ (t : VariableTreeTape f r w) (z : WindowLevelsData (K:=K) (V:=V) E.card),
      variableTreeCost f r t (Finset.univ,Finset.univ)
        (allWindowEncoded f r p u sel E W σ hσ hq hd.le (9/100000) (9/10)
          (σ^(-1000*beta η)) (P η σ D R) (by norm_num) t z)≤
      windowCodeBudget σ (Nat.card K) (P η σ D R) (k+2*s+Real.log 4) w H := by
  filter_upwards [eventually_variable_tree_cost hη hη' Cb hCb] with σ hh
  intro D k s R L₀ q K V _ _ _ _ _ _ _ _ _ hd w n H _ p u sel E W hσ hq
    hcard hr hL hb hbhi hdrop hH
  dsimp only
  let f := fun C : PivotContext K V =>
    fourFinitePredictor hd σ C.1 C.2 (P η σ D R) (σ^(-800*beta η)) R L₀
  let r := fun C : PivotContext K V =>
    fourFinitePredictor (K:=K) (V:=Dual K V) (by simpa using hd) σ C.2
      (C.1.map bidualPoint.toEmbedding) (P η σ D R) (σ^(-800*beta η)) R L₀
  intro t z
  have hP : 0≤P η σ D R := le_of_lt (lt_of_lt_of_le (by positivity)
    (finite_bounds hη hη' hσ hr).2.2.2.2.2.1)
  change variableTreeCost f r t _ (allWindowEncoded f r p u sel E W _ _ _ _ _ _ _ _ _ t z)≤_
  unfold allWindowEncoded
  split_ifs with hE
  · have hs := hh D (k+2*s+Real.log 4) R L₀ q K V hd w
      ⟨E.card,Nat.lt_succ_of_le (by simpa using Finset.card_le_univ E)⟩
      (fun i=>(W hE).firstSupport i (z.1 i)) (fun i=>(W hE).secondSupport i (z.2 i))
      (fun i=>(W hE).first_nonempty i _) (fun i=>(W hE).second_nonempty i _) hσ hq
      hcard hr hL hb hbhi
      (fun i=>(W hE).support_product k (fun v=>hdrop _ (survivingOriginal_mem E hE v)) i (z.1 i) (z.2 i))
      t (Finset.univ,Finset.univ)
    apply hs.trans
    exact windowCodeBudget_mono (zero_le_one.trans hσ) (by positivity) hP hb
      (by exact le_max_left _ _) (ambient_pivotPotential hd σ hq)
      (by simpa using Finset.card_le_univ E)
      (finiteBalanced_height H E.card ((lt_of_le_of_lt (by simpa using Finset.card_le_univ E) hH)))
  · rw [variableTreeEmpty_cost]
    exact windowCodeBudget_ge_header w H (zero_le_one.trans hσ) (by positivity) hP hb
end
end SharpRamseyFive.ProjectiveIncidence

end OAI
