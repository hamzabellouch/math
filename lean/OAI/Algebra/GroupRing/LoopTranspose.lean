import Mathlib
import OAI.Algebra.GroupRing.LoopTracks

namespace OAI



section
namespace TorsionFreeZeroDivisors.LoopTranspose
open scoped Topology unitInterval
noncomputable section
universe u
variable {X : Type u} [TopologicalSpace X] (x : X)
abbrev Other (b : Bool) := {j : Bool // j≠b}
instance (b : Bool) : Unique (Other b) where
  default := ⟨!b,by cases b <;> decide⟩
  uniq a := by rcases a with ⟨a,ha⟩;cases a <;> cases b <;> simp_all

def groupEquiv (b : Bool) : HomotopyGroup Bool X x≃*
    FundamentalGroup (GenLoop (Other b) X x) GenLoop.const where
  toEquiv := homotopyGroupEquivFundamentalGroup b
  map_mul' a c := by
    have h := HomotopyGroup.auxGroup_indep (X:=X) (x:=x) (Classical.arbitrary Bool) b
    apply Eq.trans (congrArg (fun i : Group (HomotopyGroup Bool X x) =>
      (homotopyGroupEquivFundamentalGroup b) (@Mul.mul _ i.toMul a c)) h)
    exact (homotopyGroupEquivFundamentalGroup b).apply_symm_apply _
def equiv (b : Bool) : HomotopyGroup Bool X x≃*FundamentalGroup (Path x x) (Path.refl x) := by
  let e := (groupEquiv x b).trans (LoopTracks.piOneHomeo (LoopTracks.uniqueLoopHomeo (Other b) x) GenLoop.const)
  have he : LoopTracks.uniqueLoopHomeo (Other b) x GenLoop.const=Path.refl x := by ext t;rfl
  rw [he] at e
  exact e

def turnPath (p : Path (Path.refl x) (Path.refl x)) : Path (Path.refl x) (Path.refl x) where
  toFun t := {
    toFun s := p s t
    continuous_toFun := (Path.continuous_uncurry_iff.mpr p.continuous).comp (continuous_id.prodMk continuous_const)
    source' := by rw [p.source];rfl
    target' := by rw [p.target];rfl }
  continuous_toFun := Path.continuous_uncurry_iff.mp
    ((Path.continuous_uncurry_iff.mpr p.continuous).comp continuous_swap)
  source' := by ext s;exact (p s).source
  target' := by ext s;exact (p s).target
lemma turnPath_turn (p : Path (Path.refl x) (Path.refl x)) : turnPath x (turnPath x p)=p := by
  ext s t;rfl

def turn : FundamentalGroup (Path x x) (Path.refl x)≃*FundamentalGroup (Path x x) (Path.refl x) :=
  (equiv x true).symm.trans (equiv x false)

lemma equiv_mk (b : Bool) (p : GenLoop Bool X x) :
    equiv x b (Quotient.mk' p)=Path.Homotopic.Quotient.mk
      (((GenLoop.toLoop b p).map (LoopTracks.uniqueLoopHomeo (Other b) x).continuous).cast
        (by ext t;rfl) (by ext t;rfl)) := by
  rfl
lemma turn_equiv_mk (p : GenLoop Bool X x) :
    turn x (equiv x true (Quotient.mk' p))=equiv x false (Quotient.mk' p) := by
  change equiv x false ((equiv x true).symm ((equiv x true) (Quotient.mk' p)))=_
  exact (equiv x false).congr_arg ((equiv x true).symm_apply_apply _)
lemma turns_representative (p : GenLoop Bool X x) :
    turnPath x (((GenLoop.toLoop true p).map (LoopTracks.uniqueLoopHomeo (Other true) x).continuous).cast
        (by ext t;rfl) (by ext t;rfl))=
      (((GenLoop.toLoop false p).map (LoopTracks.uniqueLoopHomeo (Other false) x).continuous).cast
        (by ext t;rfl) (by ext t;rfl)) := by
  ext s t
  change p (Cube.insertAt true (t,fun _=>s))=p (Cube.insertAt false (s,fun _=>t))
  apply congrArg p
  funext b
  cases b <;> simp [Cube.insertAt]

lemma turn_mk (p : Path (Path.refl x) (Path.refl x)) :
    turn x (Path.Homotopic.Quotient.mk p)=Path.Homotopic.Quotient.mk (turnPath x p) := by
  obtain ⟨q,hq⟩ := (equiv x true).surjective (Path.Homotopic.Quotient.mk p)
  induction q using Quotient.inductionOn with | h q=>
  change equiv x true (Quotient.mk' q)=Path.Homotopic.Quotient.mk p at hq
  rw [←hq,turn_equiv_mk,equiv_mk]
  rw [equiv_mk] at hq
  have h := Path.Homotopic.Quotient.eq.mp hq
  have ht : (turnPath x (((GenLoop.toLoop true q).map (LoopTracks.uniqueLoopHomeo (Other true) x).continuous).cast
      (by ext t;rfl) (by ext t;rfl))).Homotopic (turnPath x p) := by
    obtain ⟨H⟩ := h
    refine ⟨{
      toFun := fun z=>{
        toFun t:=H (z.1,t) z.2
        continuous_toFun:=?_
        source':=?_
        target':=?_ }
      continuous_toFun:=?_
      map_zero_left:=?_
      map_one_left:=?_
      prop':=?_ }⟩
    · exact (Path.continuous_uncurry_iff.mpr H.continuous).comp
        ((continuous_const.prodMk continuous_id).prodMk continuous_const)
    · rw [H.eq_fst z.1 (show (0:unitInterval)∈{0,1} from Or.inl rfl)]
      simp only [Path.coe_toContinuousMap,Path.source,Path.refl_apply]
    · rw [H.eq_fst z.1 (show (1:unitInterval)∈{0,1} from Or.inr rfl)]
      simp only [Path.coe_toContinuousMap,Path.target,Path.refl_apply]
    · apply Path.continuous_uncurry_iff.mp
      exact (Path.continuous_uncurry_iff.mpr H.continuous).comp
        (((continuous_fst.comp continuous_fst).prodMk continuous_snd).prodMk
          (continuous_snd.comp continuous_fst))
    · intro s;ext t;exact congrArg (fun r : Path x x=>r s) (H.apply_zero t)
    · intro s;ext t;exact congrArg (fun r : Path x x=>r s) (H.apply_one t)
    · intro s t ht;ext z
      rcases ht with rfl|rfl
      · change (H (s,z)) 0=_
        simp only [Path.coe_toContinuousMap,Path.source,Path.refl_apply]
      · change (H (s,z)) 1=_
        simp only [Path.coe_toContinuousMap,Path.target,Path.refl_apply]
  rw [turns_representative] at ht
  exact Path.Homotopic.Quotient.eq.mpr ht
end
end TorsionFreeZeroDivisors.LoopTranspose

end



end OAI
