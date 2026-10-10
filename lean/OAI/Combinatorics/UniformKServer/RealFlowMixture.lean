import Mathlib
import OAI.Combinatorics.UniformKServer.RealFlow
import OAI.Combinatorics.UniformKServer.LawSupport

namespace OAI

noncomputable section

/-! Independent finite random seeds are eliminated by linear flow mixtures,
not by revealing them to the request law. -/
namespace UniformKServer.RealFlow
open Finset FiniteProbability
open scoped Classical
variable {R C J Z : Type*} [Fintype C] [Fintype J] [Fintype Z]

def mixture (P : Law Z) (F : Z→Data R C J) : Data R C J where
  mass w c := P.expect (fun z=>(F z).mass w c)
  flow w r c j := P.expect (fun z=>(F z).flow w r c j)

theorem mixture_valid (P : Law Z) (F : Z→Data R C J) (T : C→R→J→C)
    (allowed : C→R→J→Prop) (s : C) (H : ℕ)
    (hv : ∀ z,Valid (F z) T allowed s H) : Valid (mixture P F) T allowed s H := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro w hw c
    exact P.expect_nonneg _ (fun z=>(hv z).mass_nonneg w hw c)
  · intro w hw
    change (∑ c,P.expect (fun z=>(F z).mass w c))=1
    rw [←Law.expect_univ]
    simp only [(hv _).mass_total w hw,Law.expect_const]
  · intro c
    change P.expect (fun z=>(F z).mass [] c)=_
    simp only [(hv _).initial,Law.expect_const]
  · intro w hw r c j
    exact P.expect_nonneg _ (fun z=>(hv z).flow_nonneg w hw r c j)
  · intro w hw r c j hj
    change P.expect (fun z=>(F z).flow w r c j)=0
    simp only [(hv _).support w hw r c j hj,Law.expect_const]
  · intro w hw r c
    change (∑ j,P.expect (fun z=>(F z).flow w r c j))=P.expect _
    rw [←Law.expect_univ]
    exact congrArg P.expect (funext fun z=>(hv z).outflow w hw r c)
  · intro w hw r c'
    change (∑ c,∑ j,if T c r j=c' then P.expect (fun z=>(F z).flow w r c j) else 0)=P.expect _
    have he (c : C) (j : J) : (if T c r j=c' then P.expect (fun z=>(F z).flow w r c j) else 0)=
        P.expect (fun z=>if T c r j=c' then (F z).flow w r c j else 0) := by
      split_ifs <;> simp only [Law.expect_const]
    simp_rw [he]
    simp_rw [←Law.expect_univ]
    exact congrArg P.expect (funext fun z=>(hv z).inflow w hw r c')

theorem flowCost_append (F : Data R C J) (d : C→R→J→ℝ) (w u v : List R) :
    flowCost F d w (u++v)=flowCost F d w u+flowCost F d (w++u) v := by
  induction u generalizing w with
  | nil => simp [flowCost]
  | cons r rs ih =>
    rw [List.cons_append,flowCost,flowCost,ih]
    simp only [List.append_assoc,List.singleton_append,add_assoc]

theorem mixture_cost (P : Law Z) (F : Z→Data R C J) (d : C→R→J→ℝ) (w u : List R) :
    flowCost (mixture P F) d w u=P.expect (fun z=>flowCost (F z) d w u) := by
  induction u generalizing w with
  | nil => simp only [flowCost,Law.expect_const]
  | cons r rs ih =>
    rw [flowCost,ih]
    have hc : (∑ c,∑ j,(mixture P F).flow w r c j*d c r j)=
        P.expect (fun z=>∑ c,∑ j,(F z).flow w r c j*d c r j) := by
      have he (c : C) (j : J) : (mixture P F).flow w r c j*d c r j=
          P.expect (fun z=>(F z).flow w r c j*d c r j) := by
        simpa only [mixture,mul_comm] using (P.expect_mul (d c r j) (fun z=>(F z).flow w r c j)).symm
      simp_rw [he,←Law.expect_univ]
    rw [hc,←Law.expect_add]
    rfl

end UniformKServer.RealFlow

end

end OAI
