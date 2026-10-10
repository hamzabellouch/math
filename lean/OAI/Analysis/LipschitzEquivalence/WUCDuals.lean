import OAI.Analysis.LipschitzEquivalence.WUCFunctions

namespace OAI

universe uH

noncomputable section
namespace LipschitzCounterexample.CompactWSC
open scoped ContDiff BigOperators NNReal Topology
open Set Filter FreeSpace LocalizedLinearization
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local instance : NormedAddCommGroup (Space H) := inferInstance
local instance : NormedSpace ℝ (Space H) := inferInstance
local instance (K : Set H) : NormedAddCommGroup (supported K) := inferInstance
local instance (K : Set H) : NormedSpace ℝ (supported K) := inferInstance

theorem dual_bound_on_support {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {K : Set H} (h0 : (0:H) ∈ K)
    (T : Space H →L[ℝ] ℝ) (f : H → ℝ) {L : ℝ≥0} (hf : LipschitzOnWith L f K)
    (hT : ∀ x ∈ K, T (point x) = f x-f 0) (u : Space H) (hu : u ∈ supported K) :
    |T u| ≤ L*‖u‖ := by
  obtain ⟨g,hg,hfg⟩ := hf.extend_real
  let G := test (normalized g hg)
  have hk : supported K ≤ (T-G).ker := by
    apply supported_le_ker
    intro x hx
    change T (point x)-G (point x) = 0
    have he : G (point x) = g x-g 0 := test_point (normalized g hg) x
    rw [hT x hx,he,hfg hx,hfg h0,sub_self]
  have he : T u = G u := sub_eq_zero.mp (hk hu)
  rw [he,← Real.norm_eq_abs]
  exact (norm_test_apply_le _ _).trans
    (mul_le_mul_of_nonneg_right (norm_normalized_le g hg) (norm_nonneg u))

theorem smooth_wuc_duals {K : Set H} (h0 : (0:H) ∈ K)
    (w : ℕ → Smooth H) (hw0 : ∀ i, (w i).val 0 = 0)
    (hLip : ∀ (n : ℕ) (c : ℕ → ℝ), (∀ i, |c i| ≤ 1) →
      LipschitzOnWith 2 (fun x => ∑ i ∈ Finset.range n, c i*(w i).val x) K) :
    ∃ T : ℕ → Space H →L[ℝ] ℝ,
      (∀ i, ‖T i‖ ≤ 2) ∧
      (∀ i x, x ∈ K → T i (point x) = (w i).val x) ∧
      ∀ (n : ℕ) (c : ℕ → ℝ), (∀ i, |c i| ≤ 1) → ∀ u : Space H, u ∈ supported K →
        |∑ i ∈ Finset.range n, c i*T i u| ≤ 2*‖u‖ := by
  classical
  have hsingle (i : ℕ) : LipschitzOnWith 2 (w i).val K := by
    have hc (j : ℕ) : |(if j=i then 1 else 0:ℝ)| ≤ 1 := by split_ifs <;> norm_num
    have h := hLip (i+1) (fun j => if j=i then 1 else 0) hc
    have he (x : H) : (∑ j ∈ Finset.range (i+1), (if j=i then 1 else 0:ℝ)*(w j).val x) = (w i).val x := by simp
    simpa only [he] using h
  have hex (i : ℕ) := (hsingle i).extend_real
  choose g hg hfg using hex
  let T := fun i => test (normalized (g i) (hg i))
  have hT (i : ℕ) (x : H) (hx : x ∈ K) : T i (point x) = (w i).val x := by
    change test (normalized (g i) (hg i)) (point x) = _
    rw [test_point]
    change g i x-g i 0 = _
    rw [← hfg i hx,← hfg i h0,hw0 i,sub_zero]
  refine ⟨T,fun i => ?_,hT,?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num : (0:ℝ) ≤ 2)
    intro u
    exact (norm_test_apply_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_normalized_le (g i) (hg i)) (norm_nonneg u))
  · intro n c hc u hu
    let S : Space H →L[ℝ] ℝ := ∑ i ∈ Finset.range n, c i • T i
    have hp : ∀ x ∈ K, S (point x) =
        (∑ i ∈ Finset.range n, c i*(w i).val x)-(∑ i ∈ Finset.range n, c i*(w i).val 0) := by
      intro x hx
      simp only [S,sum_apply,smul_apply,smul_eq_mul,hT _ x hx,hw0,mul_zero,Finset.sum_const_zero,sub_zero]
    have hb := dual_bound_on_support h0 S _ (hLip n c hc) hp u hu
    simpa only [S,sum_apply,smul_apply,smul_eq_mul,NNReal.coe_ofNat] using hb

theorem exists_wuc_duals {K Q : Set H} (h0 : (0:H) ∈ K)
    (hQ : IsCompact Q) (hQc : Convex ℝ Q) (hKQ : K ⊆ Q)
    {C ρ α : ℝ} {μ : ℕ → Space H} (hC : 0 ≤ C) (hα : 0 < α)
    (hRich : (triangularRows K C ρ α μ).Rich) :
    ∃ (T : ℕ → Space H →L[ℝ] ℝ) (a : ℕ → RowItem K C ρ μ),
      (∀ i, ‖T i‖ ≤ 2) ∧ (∀ i, α/2 ≤ T i (a i).a.vector) ∧
      ∀ (n : ℕ) (c : ℕ → ℝ), (∀ i, |c i| ≤ 1) → ∀ u : Space H, u ∈ supported K →
        |∑ i ∈ Finset.range n, c i*T i u| ≤ 2*‖u‖ := by
  obtain ⟨w,a,hw0,hwdiag,hwLip⟩ := exists_wuc_functions hQ hQc hKQ hC hα hRich
  obtain ⟨T,hT,hpoint,hWUC⟩ := smooth_wuc_duals h0 w hw0
    (fun n c hc => (hwLip n c hc).mono hKQ)
  refine ⟨T,a,hT,fun i => ?_,hWUC⟩
  have he : T i (a i).a.vector = smoothPair (a i).a (w i) := by
    rw [dual_molecular]
    change (∑ j, (a i).a.coeff j*(_-_)) = ∑ j, (a i).a.coeff j*(_-_)
    apply Finset.sum_congr rfl
    intro j _
    change (a i).a.coeff j*(T i (point ((a i).a.p j))-T i (point ((a i).a.q j))) =
      (a i).a.coeff j*((w i).val ((a i).a.p j)-(w i).val ((a i).a.q j))
    rw [hpoint i _ ((a i).support j).1,hpoint i _ ((a i).support j).2]
  rw [he]
  exact hwdiag i

end LipschitzCounterexample.CompactWSC
end

end OAI
