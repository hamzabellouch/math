import Mathlib
import OAI.Combinatorics.UniformKServer.RealFlowBounds
import OAI.Combinatorics.UniformKServer.RealFlowConvex

namespace OAI

noncomputable section

/-! A literal finite coordinate model of all horizon-H causal flows. Compactness
comes from their probability bounds, not from assuming a minimax input. -/
namespace UniformKServer.FiniteFlowSpace
open Finset RealFlow
open scoped Classical
variable {R C J : Type} {H : ℕ}

abbrev Word (R : Type) (H : ℕ) := (m : Fin (H+1)) × (Fin m.val→R)
def letters (w : Word R H) : List R := List.ofFn w.2
def code (w : List R) (hw : w.length≤H) : Word R H := ⟨⟨w.length,by omega⟩,fun i=>w[i]⟩

theorem letters_code (w : List R) (hw : w.length≤H) : letters (code w hw)=w := by
  change List.ofFn w.get = w
  exact List.ofFn_get w

theorem letters_length (w : Word R H) : (letters w).length=w.1.val := List.length_ofFn

theorem letters_bound (w : Word R H) : (letters w).length≤H := by
  rw [letters_length]
  have := w.1.isLt
  omega

abbrev Index (R C J : Type) (H : ℕ) := (Word R H×C) ⊕ (Word R H×R×C×J)
abbrev Space (R C J : Type) (H : ℕ) := Index R C J H→ℝ

def decode (x : Space R C J H) : Data R C J where
  mass w c := if hw : w.length≤H then x (.inl (code w hw,c)) else 0
  flow w r c j := if hw : w.length<H then x (.inr (code w hw.le,r,c,j)) else 0

def encode (F : Data R C J) : Space R C J H
  | .inl (w,c) => F.mass (letters w) c
  | .inr (w,r,c,j) => if (letters w).length<H then F.flow (letters w) r c j else 0

theorem decode_encode_mass (F : Data R C J) (w : List R) (hw : w.length≤H) (c : C) :
    (decode (H:=H) (encode F)).mass w c=F.mass w c := by
  simp only [decode,dite_eq_left hw,encode,letters_code]

theorem decode_encode_flow (F : Data R C J) (w : List R) (hw : w.length<H) (r : R) (c : C) (j : J) :
    (decode (H:=H) (encode F)).flow w r c j=F.flow w r c j := by
  simp only [decode,dite_eq_left hw,encode,letters_code,ite_eq_left hw]

section
variable [Fintype C] [Fintype J]

theorem decode_encode_valid (F : Data R C J) (T : C→R→J→C) (allowed : C→R→J→Prop) (s : C)
    (hF : Valid F T allowed s H) : Valid (decode (H:=H) (encode F)) T allowed s H := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro w hw c; rw [decode_encode_mass F w hw]; exact hF.mass_nonneg w hw c
  · intro w hw; simp only [decode_encode_mass F w hw]; exact hF.mass_total w hw
  · intro c; rw [decode_encode_mass F [] (by simp)]; exact hF.initial c
  · intro w hw r c j; rw [decode_encode_flow F w hw]; exact hF.flow_nonneg w hw r c j
  · intro w hw r c j hj; rw [decode_encode_flow F w hw]; exact hF.support w hw r c j hj
  · intro w hw r c; simp only [decode_encode_flow F w hw,decode_encode_mass F w hw.le]; exact hF.outflow w hw r c
  · intro w hw r c'
    have hwr : (w++[r]).length≤H := by simp only [List.length_append,List.length_singleton]; omega
    simp only [decode_encode_flow F w hw,decode_encode_mass F (w++[r]) hwr]
    exact hF.inflow w hw r c'

theorem encode_bounds (F : Data R C J) (T : C→R→J→C) (allowed : C→R→J→Prop) (s : C)
    (hF : Valid F T allowed s H) : encode (H:=H) F∈Set.Icc (0:Space R C J H) 1 := by
  constructor
  · intro i
    rcases i with ⟨w,c⟩|⟨w,r,c,j⟩
    · exact hF.mass_nonneg _ (letters_bound w) c
    · change 0≤(if (letters w).length<H then F.flow (letters w) r c j else 0)
      split_ifs with hw
      · exact hF.flow_nonneg _ hw r c j
      · exact le_rfl
  · intro i
    rcases i with ⟨w,c⟩|⟨w,r,c,j⟩
    · exact mass_le_one hF _ (letters_bound w) c
    · change (if (letters w).length<H then F.flow (letters w) r c j else 0)≤1
      split_ifs with hw
      · exact flow_le_one hF _ hw r c j
      · norm_num

end

theorem decode_combine (a b : ℝ) (x y : Space R C J H) :
    decode (a • x+b • y)=combine a b (decode x) (decode y) := by
  unfold decode combine
  congr 1
  · funext w c
    by_cases hw : w.length≤H <;> simp [hw]
  · funext w r c j
    by_cases hw : w.length<H <;> simp [hw]

theorem mass_continuous (w : List R) (c : C) :
    Continuous (fun x : Space R C J H=>(decode x).mass w c) := by
  by_cases hw : w.length≤H
  · simpa only [decode,dite_eq_left hw] using (continuous_apply (Sum.inl (code w hw,c) : Index R C J H) : Continuous (fun x : Space R C J H=>x (.inl (code w hw,c))))
  · simp only [decode,dite_eq_right hw]
    exact continuous_const

theorem flow_continuous (w : List R) (r : R) (c : C) (j : J) :
    Continuous (fun x : Space R C J H=>(decode x).flow w r c j) := by
  by_cases hw : w.length<H
  · simpa only [decode,dite_eq_left hw] using (continuous_apply (Sum.inr (code w hw.le,r,c,j) : Index R C J H) : Continuous (fun x : Space R C J H=>x (.inr (code w hw.le,r,c,j))))
  · simp only [decode,dite_eq_right hw]
    exact continuous_const

end UniformKServer.FiniteFlowSpace

end

end OAI
