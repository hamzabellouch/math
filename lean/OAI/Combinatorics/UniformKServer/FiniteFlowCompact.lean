import Mathlib
import OAI.Combinatorics.UniformKServer.FiniteFlowSpace

namespace OAI

noncomputable section

namespace UniformKServer.FiniteFlowSpace
open Finset RealFlow
open scoped Classical
variable {R C J : Type} [Fintype C] [Fintype J] {H : ℕ}

theorem closed_forall {A : Type*} {I : Sort*} [TopologicalSpace A] (p : I→A→Prop)
    (h : ∀i,IsClosed {x|p i x}) : IsClosed {x|∀i,p i x} := by
  simp only [Set.ofPred_forall]
  exact isClosed_iInter h

def feasible (T : C→R→J→C) (allowed : C→R→J→Prop) (s : C) : Set (Space R C J H) :=
  Set.Icc 0 1 ∩ {x | Valid (decode x) T allowed s H}

theorem valid_closed (T : C→R→J→C) (allowed : C→R→J→Prop) (s : C) :
    IsClosed {x : Space R C J H | Valid (decode x) T allowed s H} := by
  have h₁ : IsClosed {x : Space R C J H | ∀w,w.length≤H → ∀c,0≤(decode x).mass w c} :=
    closed_forall _ fun w=>closed_forall _ fun _=>closed_forall _ fun c=>
      isClosed_le continuous_const (mass_continuous w c)
  have h₂ : IsClosed {x : Space R C J H | ∀w,w.length≤H → ∑c,(decode x).mass w c=1} :=
    closed_forall _ fun w=>closed_forall _ fun _=>
      isClosed_eq (continuous_finsetSum _ fun c _=>mass_continuous w c) continuous_const
  have h₃ : IsClosed {x : Space R C J H | ∀c,(decode x).mass [] c=if c=s then 1 else 0} :=
    closed_forall _ fun c=>isClosed_eq (mass_continuous [] c) continuous_const
  have h₄ : IsClosed {x : Space R C J H | ∀w,w.length<H → ∀r c j,0≤(decode x).flow w r c j} :=
    closed_forall _ fun w=>closed_forall _ fun _=>closed_forall _ fun r=>
      closed_forall _ fun c=>closed_forall _ fun j=>
        isClosed_le continuous_const (flow_continuous w r c j)
  have h₅ : IsClosed {x : Space R C J H | ∀w,w.length<H → ∀r c j,¬allowed c r j → (decode x).flow w r c j=0} :=
    closed_forall _ fun w=>closed_forall _ fun _=>closed_forall _ fun r=>
      closed_forall _ fun c=>closed_forall _ fun j=>closed_forall _ fun _=>
        isClosed_eq (flow_continuous w r c j) continuous_const
  have h₆ : IsClosed {x : Space R C J H | ∀w,w.length<H → ∀r c,∑j,(decode x).flow w r c j=(decode x).mass w c} :=
    closed_forall _ fun w=>closed_forall _ fun _=>closed_forall _ fun r=>
      closed_forall _ fun c=>
        isClosed_eq (continuous_finsetSum _ fun j _=>flow_continuous w r c j) (mass_continuous w c)
  have h₇ : IsClosed {x : Space R C J H | ∀w,w.length<H → ∀r c',
      (∑c,∑j,if T c r j=c' then (decode x).flow w r c j else 0)=(decode x).mass (w++[r]) c'} := by
    apply closed_forall _; intro w
    apply closed_forall _; intro hw
    apply closed_forall _; intro r
    apply closed_forall _; intro c'
    apply isClosed_eq _ (mass_continuous (w++[r]) c')
    apply continuous_finsetSum; intro c _
    apply continuous_finsetSum; intro j _
    by_cases he : T c r j=c'
    · simp only [ite_eq_left he]; exact flow_continuous w r c j
    · simp only [ite_eq_right he]; exact continuous_const
  convert h₁.inter (h₂.inter (h₃.inter (h₄.inter (h₅.inter (h₆.inter h₇)))) ) using 1
  ext x
  exact ⟨fun h=>⟨h.mass_nonneg,h.mass_total,h.initial,h.flow_nonneg,h.support,h.outflow,h.inflow⟩,
    fun ⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇⟩=>⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇⟩⟩

theorem feasible_compact [Fintype R] (T : C→R→J→C) (allowed : C→R→J→Prop) (s : C) :
    IsCompact (feasible (H:=H) T allowed s) := isCompact_Icc.inter_right (valid_closed T allowed s)

theorem feasible_convex (T : C→R→J→C) (allowed : C→R→J→Prop) (s : C) :
    Convex ℝ (feasible (H:=H) T allowed s) := by
  apply (convex_Icc _ _).inter
  intro x hx y hy a b ha hb hab
  change Valid (decode (a • x+b • y)) T allowed s H
  rw [decode_combine]
  exact combine_valid _ _ T allowed s H hx hy a b ha hb hab

theorem encode_feasible (F : Data R C J) (T : C→R→J→C) (allowed : C→R→J→Prop) (s : C)
    (hF : Valid F T allowed s H) : encode F∈feasible (H:=H) T allowed s :=
  ⟨encode_bounds F T allowed s hF,decode_encode_valid F T allowed s hF⟩

theorem decode_encode_cost (F : Data R C J) (d : C→R→J→ℝ) (w u : List R) (hu : w.length+u.length≤H) :
    flowCost (decode (H:=H) (encode F)) d w u=flowCost F d w u := by
  induction u generalizing w with
  | nil => rfl
  | cons r u ih =>
    have hw : w.length<H := by simp only [List.length_cons] at hu; omega
    rw [flowCost,flowCost]
    congr 1
    · simp only [decode_encode_flow F w hw]
    · exact ih _ (by simp only [List.length_append,List.length_cons,List.length_nil] at *; omega)

theorem cost_continuous (d : C→R→J→ℝ) (w u : List R) :
    Continuous (fun x : Space R C J H=>flowCost (decode x) d w u) := by
  induction u generalizing w with
  | nil => exact continuous_const
  | cons r u ih =>
    apply Continuous.add _ (ih _)
    exact continuous_finsetSum _ fun c _=>continuous_finsetSum _ fun j _=>
      (flow_continuous w r c j).mul continuous_const

end UniformKServer.FiniteFlowSpace

end

end OAI
