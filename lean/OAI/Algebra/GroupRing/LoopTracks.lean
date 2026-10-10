import Mathlib

namespace OAI



section
namespace TorsionFreeZeroDivisors.LoopTracks
open scoped Topology unitInterval
noncomputable section
universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {x y : X}
/-- A genuine relative path homotopy is a path in the compact-open path space. -/
def pathOfHomotopy {p q : Path x y} (H : p.Homotopy q) : Path p q where
  toFun := H.eval
  continuous_toFun := Path.continuous_uncurry_iff.mp H.continuous
  source' := H.eval_zero
  target' := H.eval_one
/-- Conversely: no quotient or merely formal track is used here. -/
def homotopyOfPath {p q : Path x y} (h : Path p q) : p.Homotopy q where
  toFun z := h z.1 z.2
  continuous_toFun := Path.continuous_uncurry_iff.mpr h.continuous
  map_zero_left t := by rw [h.source];rfl
  map_one_left t := by rw [h.target];rfl
  prop' t z hz := by rcases hz with rfl|rfl <;> simp
lemma homotopic_iff_joined (p q : Path x y) : p.Homotopic q ↔ Joined p q := by
  constructor
  · rintro ⟨h⟩;exact ⟨pathOfHomotopy h⟩
  · rintro ⟨h⟩;exact ⟨homotopyOfPath h⟩

def piOneHomeo (e : X≃ₜY) (x : X) : FundamentalGroup X x≃*FundamentalGroup Y (e x) where
  toFun := Quotient.map (fun p : Path x x => p.map e.continuous)
    (fun _ _ h => h.map ⟨e,e.continuous⟩)
  invFun := Quotient.map (fun p : Path (e x) (e x) => (p.map e.symm.continuous).cast
    (e.symm_apply_apply x).symm (e.symm_apply_apply x).symm) (fun _ _ h => h.map ⟨e.symm,e.symm.continuous⟩)
  left_inv a := by
    induction a using Quotient.inductionOn with | h p =>
    apply congrArg Path.Homotopic.Quotient.mk
    ext t
    exact e.symm_apply_apply (p t)
  right_inv a := by
    induction a using Quotient.inductionOn with | h p =>
    apply congrArg Path.Homotopic.Quotient.mk
    ext t
    exact e.apply_symm_apply (p t)
  map_mul' a b := by
    induction a using Quotient.inductionOn with | h p =>
    induction b using Quotient.inductionOn with | h q =>
    exact congrArg Path.Homotopic.Quotient.mk (q.map_trans p e.continuous)

def uniqueLoopHomeo (N : Type*) [Unique N] (x : X) : GenLoop N X x≃ₜPath x x where
  toEquiv := genLoopEquivOfUnique N
  continuous_toFun := Path.continuous_uncurry_iff.mp (by
    change Continuous (fun z : GenLoop N X x × unitInterval => z.1 (fun _ => z.2))
    fun_prop)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : Path x x × (N→unitInterval) => z.1 (z.2 default))
    fun_prop

/-- The loop-space fundamental group is genuinely commutative (Eckmann-Hilton).
This is the coefficient group of two-cell homotopy-extension obstructions. -/
lemma loopGroup_comm (x : X) : ∀a b : FundamentalGroup (Path x x) (Path.refl x), a*b=b*a := by
  let N := {j : Bool // j≠true}
  let _ : Unique N := ⟨⟨false,by decide⟩,by intro a;rcases a with ⟨a,ha⟩;cases a <;> simp_all⟩
  let e : HomotopyGroup Bool X x≃* FundamentalGroup (GenLoop N X x) GenLoop.const :=
    { toEquiv := homotopyGroupEquivFundamentalGroup true
      map_mul' := by
        intro a b
        have h := HomotopyGroup.auxGroup_indep (X:=X) (x:=x) (Classical.arbitrary Bool) true
        apply Eq.trans (congrArg (fun i : Group (HomotopyGroup Bool X x) =>
          (homotopyGroupEquivFundamentalGroup true) (@Mul.mul _ i.toMul a b)) h)
        exact (homotopyGroupEquivFundamentalGroup true).apply_symm_apply _ }
  let f := piOneHomeo (uniqueLoopHomeo N x) GenLoop.const
  have hf : uniqueLoopHomeo N x GenLoop.const=Path.refl x := by ext t;rfl
  rw [←hf]
  intro a b
  obtain ⟨a,rfl⟩ := (e.trans f).surjective a
  obtain ⟨b,rfl⟩ := (e.trans f).surjective b
  rw [←map_mul,←map_mul,mul_comm]
end
end TorsionFreeZeroDivisors.LoopTracks

end



end OAI
