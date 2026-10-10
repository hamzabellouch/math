import Mathlib
import OAI.Combinatorics.KMedian.CookLevin.CookClockProgram
import OAI.Combinatorics.KMedian.CookLevin.TableauRelationProgram
import OAI.Combinatorics.KMedian.Machines.FiniteBoundaryPrograms

namespace OAI

section Inline_PCPCookBoundaryProgram
namespace MetricKMedian.PCP.Compiler.CookProgram
open Binary Binary.Automatic CookLevin Complexity Tableau TableauDirectory FiniteList Turing Turing.TM2
open scoped Classical

variable {verify : Word×Word→Bool}
variable (P : Turing.TM2ComputableInPolyTime Complexity.encodePair encodeBit verify) (p : Polynomial ℕ)
variable [∀k,Fintype (P.tm.Γ k)]
local instance : Fintype P.tm.K := P.tm.kFin
local instance : Fintype P.tm.Λ := P.tm.ΛFin
local instance : Fintype P.tm.σ := P.tm.σFin
noncomputable instance tapeCoding : Coding P.tm.K := finiteCoding _
noncomputable instance tapeHardcoded : Hardcoded P.tm.K := ⟨fun _ _ _ f=>finite_function f⟩
noncomputable instance symbolCoding (k : P.tm.K) : Coding (P.tm.Γ k) := finiteCoding _
noncomputable instance symbolHardcoded (k : P.tm.K) : Hardcoded (P.tm.Γ k) := ⟨fun _ _ _ f=>finite_function f⟩
instance inputSymbolInhabited : Inhabited (P.tm.Γ P.tm.k₀) := ⟨P.inputAlphabet.invFun false⟩
instance outputSymbolInhabited : Inhabited (P.tm.Γ P.tm.k₁) := ⟨P.outputAlphabet.invFun false⟩
lemma poly_inputPrefix : Poly (inputPrefix P) := by
  exact Poly.list_map ((hardcoded P.inputAlphabet.invFun).comp Poly.snd) poly_firstWord
lemma poly_certificateBound : Poly (fun x : Word=>p.eval x.length) := by
  have h := Poly.list_length.comp ((poly_unaryPolynomial p).comp poly_wordUnits)
  apply poly_congr h
  intro x; simp only [List.length_replicate,List.length_map]
lemma poly_firstCell_fixed (k : P.tm.K) :
    Poly (fun z : Word×ℕ=>firstCellSet P.tm.m (boundary P p z.1) k z.2) := by
  by_cases hk : k=P.tm.k₀
  · subst k
    have hh := FiniteList.poly_prefixFilter (inputPrefix P) (fun x:Word=>p.eval x.length)
      (fun a : Query P.tm.m→Value P.tm.m => (a (q0 P.tm.m)).2.2 P.tm.k₀) (poly_inputPrefix P) (poly_certificateBound p)
    apply poly_congr hh
    intro z
    ext a
    simp [firstCellSet,boundary,initList]
  · apply poly_congr (Automatic.Poly.const (Finset.univ.filter (fun a : Query P.tm.m→Value P.tm.m => (a (q0 P.tm.m)).2.2 k=none)))
    intro z
    ext a
    simp [firstCellSet,boundary,initList,hk,prefixCell]
lemma poly_firstCell :
    Poly (fun z : (Word×P.tm.K)×ℕ=>firstCellSet P.tm.m (boundary P p z.1.1) z.1.2 z.2) := by
  have he : Poly (fun k : P.tm.K => decide (k=P.tm.k₀)) := hardcoded _
  have hc : Poly (fun k : P.tm.K => Finset.univ.filter (fun a : Query P.tm.m→Value P.tm.m => (a (q0 P.tm.m)).2.2 k=none)) := hardcoded _
  have hh := Poly.ite_prop (he.comp (Poly.snd.comp Poly.fst : Poly (fun z : (Word×P.tm.K)×ℕ=>z.1.2)))
    ((poly_firstCell_fixed P p P.tm.k₀).comp (Poly.pair (Poly.fst.comp Poly.fst) Poly.snd))
    (hc.comp (Poly.snd.comp Poly.fst))
  apply poly_congr hh
  rintro ⟨⟨x,k⟩,i⟩
  by_cases hk : k=P.tm.k₀
  · simp only [hk,ite_true]
  · rw [ite_eq_right hk]
    ext a
    simp [firstCellSet,boundary,initList,prefixCell,hk]

lemma poly_lastCell_fixed (k : P.tm.K) :
    Poly (fun z : Word×ℕ=>lastCellSet P.tm.m (boundary P p z.1) k z.2) := by
  by_cases hk : k=P.tm.k₁
  · subst k
    have hh := FiniteList.poly_getFilter (fun _ : Word=>[P.outputAlphabet.invFun true])
      (fun a : Query P.tm.m→Value P.tm.m => (a (q0 P.tm.m)).2.2 P.tm.k₁) (Automatic.Poly.const _)
    apply poly_congr hh
    intro z
    ext a
    simp [lastCellSet,boundary,haltList]
  · apply poly_congr (Automatic.Poly.const (Finset.univ.filter (fun a : Query P.tm.m→Value P.tm.m => (a (q0 P.tm.m)).2.2 k=none)))
    intro z
    ext a
    simp [lastCellSet,boundary,haltList,hk]
lemma poly_lastCell :
    Poly (fun z : (Word×P.tm.K)×ℕ=>lastCellSet P.tm.m (boundary P p z.1.1) z.1.2 z.2) := by
  have he : Poly (fun k : P.tm.K => decide (k=P.tm.k₁)) := hardcoded _
  have hc : Poly (fun k : P.tm.K => Finset.univ.filter (fun a : Query P.tm.m→Value P.tm.m => (a (q0 P.tm.m)).2.2 k=none)) := hardcoded _
  have hh := Poly.ite_prop (he.comp (Poly.snd.comp Poly.fst : Poly (fun z : (Word×P.tm.K)×ℕ=>z.1.2)))
    ((poly_lastCell_fixed P p P.tm.k₁).comp (Poly.pair (Poly.fst.comp Poly.fst) Poly.snd))
    (hc.comp (Poly.snd.comp Poly.fst))
  apply poly_congr hh
  rintro ⟨⟨x,k⟩,i⟩
  by_cases hk : k=P.tm.k₁
  · simp only [hk,ite_true]
  · rw [ite_eq_right hk]
    ext a
    simp [lastCellSet,boundary,haltList,hk]

lemma poly_accept : Poly (fun z : Word×TC (K:=P.tm.K)=>rawAccept P.tm.m (boundary P p z.1) z.2) := by
  let : Inhabited P.tm.K := ⟨P.tm.k₀⟩
  apply poly_rawAccept P.tm.m (boundary P p)
  · change Poly (fun _ : Word => Finset.univ.filter (fun z : Query P.tm.m→Value P.tm.m => (z (q0 P.tm.m)).1=(some P.tm.main,P.tm.initialState)))
    exact Automatic.Poly.const _
  · change Poly (fun _ : Word => Finset.univ.filter (fun z : Query P.tm.m→Value P.tm.m => (z (q0 P.tm.m)).1=(none,P.tm.initialState)))
    exact Automatic.Poly.const _
  · exact poly_firstCell P p
  · exact poly_lastCell P p
end MetricKMedian.PCP.Compiler.CookProgram

end Inline_PCPCookBoundaryProgram

end OAI
