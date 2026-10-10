import OAI.NumberTheory.DirichletL.Descent.GlobalPriorityPhysical

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseMoment
open InverseFirstPriorityParents
variable {ι:Type*} [DecidableEq ι] {Jo:ℕ}
def eraseFirstQuotient (x:Source ι Jo):Source ι Jo:= {x with quotientSupport:=∅}
def fillFirstQuotient (x:Source ι Jo)(D:Finset ι):Source ι Jo:={x with quotientSupport:=D}
omit [DecidableEq ι] in
@[simp] theorem erase_fillFirstQuotient (x:Source ι Jo)(D:Finset ι):
    eraseFirstQuotient (fillFirstQuotient x D)=eraseFirstQuotient x:=rfl
omit [DecidableEq ι] in
@[simp] theorem eraseFirstQuotient_eq (x:Source ι Jo)(hx:x.quotientSupport=∅):
    eraseFirstQuotient x=x:=by cases x;simpa [eraseFirstQuotient] using hx.symm

def globalParentSource (outer:Finset (Source ι Jo))(pool:Finset ι)
    (selector:Source ι Jo→Finset ι→ℂ):Finset (Source ι Jo):=
  outer.biUnion (fun x=>(pool.powerset.filter (fun D=>selector x D≠0)).image (fillFirstQuotient x))

omit [DecidableEq ι] in
theorem sum_globalParentSource {A:Type*}[AddCommMonoid A]
    (outer:Finset (Source ι Jo))(pool:Finset ι)(selector:Source ι Jo→Finset ι→ℂ)
    (houter:∀x∈outer,x.quotientSupport=∅)(H:Source ι Jo→A):
    ∑x∈globalParentSource outer pool selector,H x=
      ∑x∈outer,∑D∈pool.powerset.filter (fun D=>selector x D≠0),H (fillFirstQuotient x D):=by
  unfold globalParentSource
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro x hx
    exact Finset.sum_image (fun D hD E hE he=>congrArg Source.quotientSupport he)
  · intro x hx y hy hxy
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨D,hD,rfl⟩:=Finset.mem_image.mp hz
    obtain ⟨E,hE,he⟩:=Finset.mem_image.mp hz'
    have he':=congrArg eraseFirstQuotient he
    simp only [erase_fillFirstQuotient,eraseFirstQuotient_eq _ (houter x hx),
      eraseFirstQuotient_eq _ (houter y hy)] at he'
    exact hxy he'.symm

omit [DecidableEq ι] in
theorem mem_globalParentSource
    (outer:Finset (Source ι Jo))(pool:Finset ι)(selector:Source ι Jo→Finset ι→ℂ)
    (houter:∀x∈outer,x.quotientSupport=∅)(x:Source ι Jo):
    x∈globalParentSource outer pool selector ↔
      eraseFirstQuotient x∈outer ∧ x.quotientSupport⊆pool ∧
        selector (eraseFirstQuotient x) x.quotientSupport≠0:=by
  constructor
  · intro hx
    obtain ⟨y,hy,hyx⟩:=Finset.mem_biUnion.mp hx
    obtain ⟨D,hD,rfl⟩:=Finset.mem_image.mp hyx
    simp only [erase_fillFirstQuotient,eraseFirstQuotient_eq _ (houter y hy)]
    exact ⟨hy,Finset.mem_powerset.mp (Finset.mem_filter.mp hD).1,(Finset.mem_filter.mp hD).2⟩
  · rintro ⟨hx,hD,hs⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨eraseFirstQuotient x,hx,Finset.mem_image.mpr ⟨x.quotientSupport,?_,?_⟩⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hD,hs⟩
    · cases x;rfl
end SevenEighths.InverseMoment

end

end OAI
