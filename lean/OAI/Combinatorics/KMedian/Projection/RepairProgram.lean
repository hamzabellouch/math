import Mathlib
import OAI.Combinatorics.KMedian.Amplification.RegularSpec
import OAI.Combinatorics.KMedian.Machines.ListAllProgram
import OAI.Combinatorics.KMedian.Projection.CSPProjection

namespace OAI

section Inline_PCPProjectionRepairProgram
namespace MetricKMedian.PCP.Compiler.SeedProgram
open Binary Binary.Automatic RegularProgram CloudProgram
open scoped Classical

variable {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
noncomputable def legal (t : CSPTable A) (v : ℕ) (d : Port) : Finset (A×A) :=
  (allowed t v d).filter (fun a => (rotate t v d).1=v → a.1=a.2)
noncomputable def choose (t : CSPTable A) (v : ℕ) (d : Port) : A×A :=
  (legal t v d).toList.headD default
noncomputable def repair (t : CSPTable A) (v : ℕ) (d : Port) (a : A×A) : A×A :=
  if a∈legal t v d then a else choose t v d
variable [Coding A]
omit [Inhabited A] [Coding A] in
lemma poly_legal : Poly (fun z : (CSPTable A×ℕ)×Port =>legal z.1.1 z.1.2 z.2) := by
  have hh : Poly (fun z : Finset (A×A)×Bool =>z.1.filter (fun a=>z.2=true → a.1=a.2)) := hardcoded _
  have hn : Poly (fun z : (CSPTable A×ℕ)×Port =>decide ((rotate z.1.1 z.1.2 z.2).1=z.1.2)) := by
    exact Poly.nat_eq.comp (Poly.pair (Poly.fst.comp poly_rotate) (Poly.snd.comp Poly.fst))
  apply poly_congr (hh.comp (Poly.pair poly_allowed hn))
  intro z
  simp only [decide_eq_true_eq,legal]
lemma poly_choose : Poly (fun z : (CSPTable A×ℕ)×Port =>choose z.1.1 z.1.2 z.2) := by
  have hh : Poly (fun s : Finset (A×A)=>s.toList.headD default) := hardcoded _
  exact hh.comp poly_legal
lemma poly_repair [Hardcoded A] : Poly (fun z : ((CSPTable A×ℕ)×Port)×(A×A) =>repair z.1.1.1 z.1.1.2 z.1.2 z.2) := by
  have hh : Poly (fun z : Finset (A×A)×(A×A) =>decide (z.2∈z.1)) := hardcoded _
  exact Poly.ite_prop (hh.comp (Poly.pair (poly_legal.comp Poly.fst) Poly.snd)) Poly.snd (poly_choose.comp Poly.fst)
noncomputable def allLegal (t : CSPTable A) : Bool :=
  (List.range (global t).length).all (fun v => (Ordered.fixed Port).entries.all (fun d => decide ((legal t v d).Nonempty)))
omit [Inhabited A] [Coding A] in
lemma poly_allLegal : Poly (allLegal (A:=A)) := by
  have hh : Poly (fun s : Finset (A×A)=>decide s.Nonempty) := hardcoded _
  unfold allLegal
  apply Poly.list_all
  · apply Poly.list_all
    · exact hh.comp (poly_legal.comp (show Poly (fun z : (CSPTable A×ℕ)×Port =>z) from Poly.identity))
    · exact Automatic.Poly.const _
  · exact Poly.list_indices.comp poly_global
omit [Coding A]
variable (t : CSPTable A) (h : t.WellFormed) [Nonempty (Fin t.2.length)]
omit [Inhabited A] in
lemma legal_correct (v : GlobalRegularization.Node (CloudSpec.C t h)) (d : Port) (a : A×A) :
    a∈legal t (CloudSpec.vertexCode t h v) d ↔ (CloudSpec.regularCSP t h).Legal (v,d) a := by
  rw [legal,Finset.mem_filter,CloudSpec.allowed_correct,CloudSpec.rotate_correct]
  change a∈_ ∧ ((ExpanderFamily.vertexEquiv _ ((CloudSpec.regularGraph t h).rotate (v,d)).1).val=(ExpanderFamily.vertexEquiv _ v).val → a.1=a.2) ↔ _
  simp only [Fin.val_inj,Equiv.apply_eq_iff_eq,PortCSP.Legal]
lemma choose_legal (v : GlobalRegularization.Node (CloudSpec.C t h)) (d : Port) (hh : (legal t (CloudSpec.vertexCode t h v) d).Nonempty) :
    (CloudSpec.regularCSP t h).Legal (v,d) (choose t (CloudSpec.vertexCode t h v) d) := by
  apply (legal_correct t h v d _).mp
  unfold choose
  apply Finset.mem_toList.mp
  cases he : (legal t (CloudSpec.vertexCode t h v) d).toList with
  | nil => exact False.elim (hh.ne_empty (Finset.toList_eq_nil.mp he))
  | cons a as => simp only [List.headD_cons,List.mem_cons,eq_self,true_or]
lemma repair_correct (v : GlobalRegularization.Node (CloudSpec.C t h)) (d : Port) (a : A×A) :
    repair t (CloudSpec.vertexCode t h v) d a=(CloudSpec.regularCSP t h).repair
      (fun p=>choose t (CloudSpec.vertexCode t h p.1) p.2) (v,d) a := by
  unfold repair PortCSP.repair
  simp only [legal_correct t h]
omit [Fintype A] [DecidableEq A] [Inhabited A] in
lemma global_length : (global t).length=(Fintype.card ExpanderFamily.Branch)^(GlobalRegularization.depth (CloudSpec.C t h)) := by
  rw [CloudSpec.global_table t h]
  simp only [RotationTable.table,List.length_ofFn]
omit [Inhabited A] in
lemma allLegal_correct : allLegal t=true ↔ ∀ p : GlobalRegularization.Node (CloudSpec.C t h)×Port,
    (legal t (CloudSpec.vertexCode t h p.1) p.2).Nonempty := by
  simp only [allLegal,List.all_eq_true,List.mem_range,decide_eq_true_eq]
  rw [global_length t h]
  constructor
  · intro hh p
    exact hh _ (ExpanderFamily.vertexEquiv _ p.1).isLt _ ((Ordered.fixed Port).all p.2)
  · intro hh i hi d hd
    have h := hh ((ExpanderFamily.vertexEquiv _).symm ⟨i,hi⟩,d)
    simpa only [CloudSpec.vertexCode,Equiv.apply_symm_apply] using h
end MetricKMedian.PCP.Compiler.SeedProgram

end Inline_PCPProjectionRepairProgram

end OAI
