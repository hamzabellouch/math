import Mathlib
import OAI.Combinatorics.UniformKServer.FiniteSeparation
import OAI.Combinatorics.UniformKServer.FiniteFlowCompact

namespace OAI

noncomputable section

/-! Finite-law removal on the literal compact causal-flow polytope. -/
namespace UniformKServer.FiniteFlowSpace
open Finset RealFlow FiniteProbability
open scoped Classical
variable {R C J : Type} [Fintype R] [Fintype C] [Fintype J] {H : ℕ}

def costVector (d : C→R→J→ℝ) (q : Word R H→ℝ) (x : Space R C J H) : Word R H→ℝ :=
  fun v=>flowCost (decode x) d [] (letters v)-q v

omit [Fintype R] in
theorem costVector_continuous (d : C→R→J→ℝ) (q : Word R H→ℝ) :
    Continuous (costVector d q) :=
  continuous_pi fun v=>(cost_continuous d [] (letters v)).sub continuous_const

omit [Fintype R] in
theorem costVector_combo (d : C→R→J→ℝ) (q : Word R H→ℝ)
    (a b : ℝ) (hab : a+b=1) (x y : Space R C J H) :
    costVector d q (a • x+b • y)=a • costVector d q x+b • costVector d q y := by
  funext v
  simp only [costVector,decode_combine,combine_cost,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  linear_combination (q v)*hab

theorem eliminate (T : C→R→J→C) (allowed : C→R→J→Prop) (s : C)
    (d : C→R→J→ℝ) (q : Word R H→ℝ)
    (hlaw : ∀P : Law (Word R H),∃ F : Data R C J,
      Valid F T allowed s H ∧
      P.expect (fun v=>flowCost F d [] (letters v))≤P.expect q) :
    ∃F : Data R C J,Valid F T allowed s H ∧
      ∀v : Word R H,flowCost F d [] (letters v)≤q v := by
  let K := costVector d q '' feasible (H:=H) T allowed s
  have hconv : Convex ℝ K := by
    intro u hu v hv a b ha hb hab
    obtain ⟨x,hx,rfl⟩ := hu
    obtain ⟨y,hy,rfl⟩ := hv
    exact ⟨a • x+b • y,feasible_convex T allowed s hx hy ha hb hab,costVector_combo d q a b hab x y⟩
  have hcompact : IsCompact K :=
    (feasible_compact T allowed s).image (costVector_continuous d q)
  have hp (P : Law (Word R H)) : ∃x∈K,P.expect x≤0 := by
    obtain ⟨F,hF,hcost⟩ := hlaw P
    refine ⟨costVector d q (encode F),⟨encode F,encode_feasible F T allowed s hF,rfl⟩,?_⟩
    have he : P.expect (costVector d q (encode F))=
        P.expect (fun v=>flowCost F d [] (letters v))-P.expect q := by
      unfold costVector
      rw [Law.expect_sub]
      congr 1
      apply congrArg P.expect
      funext v
      exact decode_encode_cost F d [] (letters v) (by simpa using letters_bound v)
    rw [he]
    linarith
  let P₀ : Law (Word R H) := ⟨fun v=>if v=code [] (by simp) then 1 else 0,
    by intro v; split_ifs <;> norm_num,by simp⟩
  obtain ⟨x,hx,_⟩ := hp P₀
  obtain ⟨y,hy,hneg⟩ := FiniteSeparation.finite_minimax K ⟨x,hx⟩ hconv hcompact hp
  obtain ⟨z,hz,rfl⟩ := hy
  refine ⟨decode z,hz.2,?_⟩
  intro v
  have := hneg v
  change flowCost (decode z) d [] (letters v)-q v≤0 at this
  linarith

end UniformKServer.FiniteFlowSpace

end

end OAI
