import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.NumericalLine
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.NoFixedQualifyingPath

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace Finset Classical
noncomputable section
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L : ℕ}

def uncutTreeEdges (w : ClosedLine h ℓ) (a : S.FixedResidues w) : Finset (Fin ℓ) :=
  w.treeSteps.filter (fun e => ∀ p : S.FixedIndex w, (p.val:ℕ) ∣ w.label e →
    a p+(w.offset e.castSucc : ZMod (p.val:ℕ))=0)

structure TreePath (w : NumericalLine D h ℓ) (L : ℕ) where
  length : ℕ
  length_pos : 0 < length
  length_le : length ≤ L
  vertex : Fin (length+1) → ℤ
  distinct : Function.Injective vertex
  vertex_mem : ∀ i, ∃ j, vertex i=w.line.offset j
  edge : Fin length → Fin ℓ
  tree : ∀ i, edge i ∈ w.line.treeSteps
  forward : Fin length → Bool
  endpoints : ∀ i, if forward i then
    vertex i.castSucc=w.line.offset (edge i).castSucc ∧ vertex i.succ=w.line.offset (edge i).succ
    else vertex i.castSucc=w.line.offset (edge i).succ ∧ vertex i.succ=w.line.offset (edge i).castSucc

namespace TreePath
variable {w : NumericalLine D h ℓ}

def pathSign (P : TreePath w L) (i : Fin P.length) : ℤ :=
  if P.forward i then w.line.sign (P.edge i) else -w.line.sign (P.edge i)

lemma pathSign_mem (P : TreePath w L) (i : Fin P.length) :
    P.pathSign i = -1 ∨ P.pathSign i = 1 := by
  rcases w.line.sign_mem (P.edge i) with hs | hs <;>
    cases hf : P.forward i <;> simp [pathSign,hf,hs]

lemma path_step (P : TreePath w L) (i : Fin P.length) :
    P.vertex i.succ-P.vertex i.castSucc = P.pathSign i*h*w.line.label (P.edge i) := by
  have he := P.endpoints i
  have hs := w.line.step (P.edge i)
  cases hf : P.forward i <;> simp only [hf,Bool.false_eq_true,ite_false,ite_true] at he
  · rw [he.1,he.2]
    simp only [pathSign,hf,Bool.false_eq_true,ite_false]
    linear_combination -hs
  · rw [he.1,he.2]
    simpa only [pathSign,hf,ite_true] using hs

lemma vertex_residue_eq (P : TreePath w L) (p : S.Index) (i : Fin P.length)
    (hd : (p:ℕ) ∣ w.line.label (P.edge i)) :
    (P.vertex i.succ : ZMod (p:ℕ))=(P.vertex i.castSucc : ZMod (p:ℕ)) := by
  have he := P.endpoints i
  have hs := w.line.label_residue_eq (P.edge i) hd
  cases hf : P.forward i <;> simp only [hf,Bool.false_eq_true,ite_false,ite_true] at he
  · rw [he.1,he.2]; exact hs.symm
  · rw [he.1,he.2]; exact hs

lemma departure_lit (P : TreePath w L) (a : S.FixedResidues w.line)
    (hu : ∀ i, P.edge i ∈ uncutTreeEdges w.line a) (p : S.FixedIndex w.line)
    (i : Fin P.length) (hd : (p.val:ℕ) ∣ w.line.label (P.edge i)) :
    a p+(P.vertex i.castSucc : ZMod (p.val:ℕ))=0 := by
  have hl := (mem_filter.mp (hu i)).2 p hd
  have he := P.endpoints i
  cases hf : P.forward i <;> simp only [hf,Bool.false_eq_true,ite_false,ite_true] at he
  · rw [he.1,w.line.label_residue_eq (P.edge i) hd]; exact hl
  · rw [he.1]; exact hl

def IsGap (P : TreePath w L) (a : S.FixedResidues w.line) (p : S.FixedIndex w.line) : Prop :=
  1<P.length ∧ a p+(P.vertex 0 : ZMod (p.val:ℕ))=0 ∧
  a p+(P.vertex (Fin.last P.length) : ZMod (p.val:ℕ))=0 ∧
  ∀ j : Fin (P.length+1), 0<j.val → j.val<P.length →
    a p+(P.vertex j : ZMod (p.val:ℕ))≠0

lemma gap_prime_free (P : TreePath w L) (a : S.FixedResidues w.line)
    (hu : ∀ i, P.edge i ∈ uncutTreeEdges w.line a) (p : S.FixedIndex w.line)
    (hg : P.IsGap a p) : ∀ i, ¬(p.val:ℕ) ∣ w.line.label (P.edge i) := by
  intro i hi
  have hlen := hg.1
  have hd := P.departure_lit a hu p i hi
  by_cases hz : i.val=0
  · have ha : a p+(P.vertex i.succ : ZMod (p.val:ℕ))=0 := by
      rwa [P.vertex_residue_eq p.val i hi]
    exact hg.2.2.2 i.succ (by simp) (by simp; omega) ha
  · exact hg.2.2.2 i.castSucc (by dsimp; omega) (by exact i.isLt) hd

lemma gap_div_displacement (P : TreePath w L) (a : S.FixedResidues w.line)
    (p : S.FixedIndex w.line) (hg : P.IsGap a p) :
    ((p.val:ℕ):ℤ) ∣ P.vertex (Fin.last P.length)-P.vertex 0 := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p.val).mp
  rw [Int.cast_sub]
  exact sub_eq_zero.mpr (add_left_cancel (hg.2.2.1.trans hg.2.1.symm))

def specification (P : TreePath w L) (p : S.Index)
    (hfree : ∀ i, ¬(p:ℕ) ∣ w.line.label (P.edge i))
    (hd : ((p:ℕ):ℤ) ∣ P.vertex (Fin.last P.length)-P.vertex 0) :
    S.Specification D h L where
  length := P.length
  length_pos := P.length_pos
  length_le := P.length_le
  offset j := P.vertex j-P.vertex 0
  offset_zero := sub_self _
  offsets_distinct := by
    intro i j he
    apply P.distinct
    linarith
  label i := w.line.label (P.edge i)
  label_mem i := w.labels (P.edge i)
  sign := P.pathSign
  sign_mem := P.pathSign_mem
  step i := by simpa only [sub_sub_sub_cancel_right] using P.path_step i
  extra := p
  extra_not_div := hfree
  suffix := ⟨0,P.length_pos⟩
  extra_div_suffix := by simpa using hd

theorem gap_has_nonfixed (P : TreePath w L) (a : S.FixedResidues w.line)
    (hu : ∀ i, P.edge i ∈ uncutTreeEdges w.line a) (hf : NoFixedForbidden w.line D L a)
    (p : S.FixedIndex w.line) (hg : P.IsGap a p) :
    ∃ (i : Fin P.length) (q : S.Index), (q:ℕ) ∣ w.line.label (P.edge i) ∧ ¬S.IsFixed w.line q := by
  by_contra hn
  have ha : ∀ (i : Fin P.length) (q : S.Index), (q:ℕ) ∣ w.line.label (P.edge i) → S.IsFixed w.line q := by
    intro i q hq
    by_contra hnf
    exact hn ⟨i,q,hq,hnf⟩
  let s := P.specification p.val (P.gap_prime_free a hu p hg) (P.gap_div_displacement a p hg)
  apply no_fixed_qualifying_path w.line a hf s (P.vertex 0)
  · intro j
    simpa only [s,specification,add_sub_cancel] using P.vertex_mem j
  · intro q hq
    rcases mem_insert.mp hq with he | he
    · have he' : q=p.val := Subtype.ext he
      exact he' ▸ p.property
    · obtain ⟨i,_,hqi⟩ := mem_biUnion.mp he
      exact ha i q (Nat.mem_primeFactors.mp hqi).2.1
  · intro q
    constructor
    · intro hqp
      have he : q=p := Subtype.ext (Subtype.ext hqp)
      subst q
      exact hg.2.1
    · intro i hqi
      have hl := P.departure_lit a hu q i hqi
      change a q+((P.vertex 0+(P.vertex i.castSucc-P.vertex 0):ℤ):ZMod (q.val:ℕ))=0
      rw [show P.vertex 0+(P.vertex i.castSucc-P.vertex 0)=P.vertex i.castSucc by ring]
      exact hl

end TreePath
end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
