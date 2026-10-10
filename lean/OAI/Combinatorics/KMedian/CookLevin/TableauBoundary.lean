import Mathlib
import OAI.Combinatorics.KMedian.CookLevin.TableauSystem

namespace OAI

section Inline_PCPTableauBoundary

namespace MetricKMedian.PCP.Tableau
open Turing.TM2 Function Finset
open scoped Classical

def prefixCell {A : Type} (p : List A) (b i : ℕ) (v : Option A) : Prop :=
  (i<p.length → v=p[i]?) ∧ (p.length+b ≤ i → v=none)
lemma prefixCell_complete {A : Type} (p w : List A) (b : ℕ) (hw : w.length≤b) (i : ℕ) :
    prefixCell p b i (p++w)[i]? := by
  constructor
  · intro hi; exact List.getElem?_append_left hi
  · intro hi; exact List.getElem?_eq_none (by simp only [List.length_append]; omega)
lemma prefixCell_sound {A : Type} (p s : List A) (b : ℕ)
    (h : ∀ i, prefixCell p b i s[i]?) : ∃ w, w.length≤b ∧ s=p++w := by
  have hp : p <+: s := List.prefix_iff_getElem?.mpr (fun i hi => by simpa only [List.getElem?_eq_getElem hi] using (h i).1 hi)
  obtain ⟨w,rfl⟩ := hp
  refine ⟨w,?_,rfl⟩
  have hl := List.getElem?_eq_none_iff.mp ((h (p.length+b)).2 le_rfl)
  simp only [List.length_append] at hl
  omega

variable {K : Type} {Γ : K → Type} {Λ σ : Type}
variable [Fintype K] [DecidableEq K] [Fintype Λ] [Fintype σ] [∀ k, Fintype (Γ k)]
variable (M : Λ → Stmt Γ Λ σ)
structure Boundary where
  firstControl : Control (Λ := Λ) (σ := σ)
  firstPrefix : ∀ k, List (Γ k)
  certificateBound : K → ℕ
  last : Cfg Γ Λ σ
abbrev BoundaryClause (L : ℕ) := Bool × (Unit ⊕ (K × Fin (L+1)))
def timeLast (T : ℕ) : Fin (T+1) := ⟨T,by omega⟩
def boundaryTime (T : ℕ) (side : Bool) : Fin (T+1) := if side then timeLast T else time0 T
def boundaryQuery (T L : ℕ) (b : BoundaryClause (K := K) L) (_ : Query M) : Var (K := K) T L :=
  b.2.elim (fun _ => ctrl T L (boundaryTime T b.1))
    (fun ki => cell T L (boundaryTime T b.1) ki.1 ki.2)
def boundaryRelation (B : Boundary (Γ := Γ) (Λ := Λ) (σ := σ)) (L : ℕ)
    (b : BoundaryClause (K := K) L) (z : Query M → Value M) : Prop :=
  match b.2 with
  | .inl _ => (z (q0 M)).1=if b.1 then (B.last.l,B.last.var) else B.firstControl
  | .inr (k,i) => if b.1 then (z (q0 M)).2.2 k=(B.last.stk k)[i.val]?
      else prefixCell (B.firstPrefix k) (B.certificateBound k) i.val ((z (q0 M)).2.2 k)
noncomputable def boundedSystem (B : Boundary (Γ := Γ) (Λ := Λ) (σ := σ)) (T L : ℕ) :
    FiniteCSP (Var (K := K) T L) (Clause (K := K) T L ⊕ BoundaryClause (K := K) L) (Query M) (Value M) where
  query := Sum.elim (query M T L) (boundaryQuery M T L)
  accept := Sum.elim ((system M T L).accept) (fun b => univ.filter (boundaryRelation M B L b))
lemma bounded_satisfies_iff (B : Boundary (Γ := Γ) (Λ := Λ) (σ := σ)) (T L : ℕ)
    (a : Var (K := K) T L → Value M) : (boundedSystem M B T L).Satisfies a ↔
      (system M T L).Satisfies a ∧ ∀ b, boundaryRelation M B L b (a ∘ boundaryQuery M T L b) := by
  simp only [FiniteCSP.Satisfies,boundedSystem,Sum.forall,Sum.elim_inl,Sum.elim_inr,
    mem_filter,mem_univ,true_and,system]

lemma decoded_boundary (B : Boundary (Γ := Γ) (Λ := Λ) (σ := σ)) (T L : ℕ)
    (a : Var (K := K) T L → Value M) (ha : (system M T L).Satisfies a)
    (hb : ∀ b, boundaryRelation M B L b (a ∘ boundaryQuery M T L b))
    (hL : ∀ k, (B.last.stk k).length≤L) :
    let c := decodeCfg M T L a ha (time0 T)
    (c.l,c.var)=B.firstControl ∧
    (∀ k, ∃ w, w.length≤B.certificateBound k ∧ c.stk k=B.firstPrefix k++w) ∧
    decodeCfg M T L a ha (timeLast T)=B.last := by
  refine ⟨hb (false,.inl ()),?_,?_⟩
  · intro k
    apply prefixCell_sound
    intro i
    by_cases hi : i≤L
    · have hh := hb (false,.inr (k,⟨i,by omega⟩))
      change prefixCell (B.firstPrefix k) (B.certificateBound k) i ((a (cell T L (time0 T) k ⟨i,by omega⟩)).2.2 k) at hh
      have hd := clamp_decode M T L a ha (time0 T) k i
      simp only [clamp,min_eq_left hi] at hd
      rw [← hd]
      exact hh
    · have hs := hb (false,.inr (k,⟨L,by omega⟩))
      change prefixCell (B.firstPrefix k) (B.certificateBound k) L ((a (cell T L (time0 T) k ⟨L,by omega⟩)).2.2 k) at hs
      have hend := (row_valid M T L a ha (time0 T) k).1
      change (a (cell T L (time0 T) k ⟨L,by omega⟩)).2.2 k=none at hend
      rw [hend] at hs
      have hp : (B.firstPrefix k).length≤L := by
        by_contra hn
        have hx := hs.1 (by omega)
        have hx' := List.getElem?_eq_none_iff.mp hx.symm
        omega
      change prefixCell (B.firstPrefix k) (B.certificateBound k) i (decodeRow M T L a ha (time0 T) k)[i]?
      rw [List.getElem?_eq_none ((decodeRow_length M T L a ha (time0 T) k).trans (by omega))]
      exact ⟨fun h => False.elim (by omega),fun _ => rfl⟩
  · have hc := hb (true,.inl ())
    change ((decodeCfg M T L a ha (timeLast T)).l,(decodeCfg M T L a ha (timeLast T)).var)=
      (B.last.l,B.last.var) at hc
    have hstk : (decodeCfg M T L a ha (timeLast T)).stk=B.last.stk := by
      funext k
      apply List.ext_getElem?
      intro i
      by_cases hi : i≤L
      · have hh := hb (true,.inr (k,⟨i,by omega⟩))
        change (a (cell T L (timeLast T) k ⟨i,by omega⟩)).2.2 k=(B.last.stk k)[i]? at hh
        have hd := clamp_decode M T L a ha (timeLast T) k i
        simp only [clamp,min_eq_left hi] at hd
        exact hd.symm.trans hh
      · change (decodeRow M T L a ha (timeLast T) k)[i]?=(B.last.stk k)[i]?
        rw [List.getElem?_eq_none ((decodeRow_length M T L a ha (timeLast T) k).trans (by omega)),
          List.getElem?_eq_none ((hL k).trans (by omega))]
    cases hd : decodeCfg M T L a ha (timeLast T) with
    | mk l v stk =>
      cases he : B.last with
      | mk l' v' stk' =>
        rw [hd,he] at hc hstk
        cases congrArg Prod.fst hc
        cases congrArg Prod.snd hc
        cases hstk
        rfl
end MetricKMedian.PCP.Tableau

end Inline_PCPTableauBoundary

end OAI
