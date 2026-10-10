import OAI.Combinatorics.PolynomialVacuum.Cylinder.ArcResize

namespace OAI

namespace PolynomialVacuumCylinder
open Classical PolynomialVacuumAlgebra
variable {M H J K : ℕ} [NeZero M]
namespace ArcSystem
variable (S : ArcSystem (bandSites M H))
noncomputable def resizedArc (hS : arcChoiceLength S.code≤K) (hH : K<H) (hJ : K<J)
    (A : S.val) : BoundaryArc (bandSites M J) :=
  BoundaryArc.resize hH hJ ⟨A.val,(S.word_le_code_length A.val A.property).trans hS⟩
@[simp] theorem resizedArc_port (hS : arcChoiceLength S.code≤K) (hH : K<H) (hJ : K<J) (A : S.val) :
    (S.resizedArc hS hH hJ A).port=A.val.port := by simp [resizedArc]
@[simp] theorem resizedArc_shape (hS : arcChoiceLength S.code≤K) (hH : K<H) (hJ : K<J) (A : S.val) :
    (S.resizedArc hS hH hJ A).shape=A.val.shape := by simp [resizedArc]
theorem resizedArc_injective (hS : arcChoiceLength S.code≤K) (hH : K<H) (hJ : K<J) :
    Function.Injective (S.resizedArc hS hH hJ) := by
  intro A B he
  apply Subtype.ext
  exact congrArg (fun a : {A : BoundaryArc (bandSites M H) // A.Short K} => a.val) (BoundaryArc.resize_injective hH hJ he)

noncomputable def resize (hS : arcChoiceLength S.code≤K) (hH : K<H) (hJ : K<J)
    (hH' : 2*K≤H) (hJ' : 2*K≤J) : ArcSystem (bandSites M J) :=
  ⟨S.val.attach.image (S.resizedArc hS hH hJ),by
    intro A hA B hB hne
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hA
    obtain ⟨b,_,rfl⟩:=Finset.mem_image.mp hB
    apply (BoundaryArc.resize_disjoint hH hJ hH' hJ' _ _).mpr
    apply S.property a.property b.property
    intro he
    have hh : a=b := Subtype.ext he
    exact hne (congrArg (S.resizedArc hS hH hJ) hh)⟩

theorem resize_code (hS : arcChoiceLength S.code≤K) (hH : K<H) (hJ : K<J)
    (hH' : 2*K≤H) (hJ' : 2*K≤J) : (S.resize hS hH hJ hH' hJ').code=S.code := by
  let R:=S.resize hS hH hJ hH' hJ'
  change R.code=S.code
  funext p
  by_cases he : ∃A∈S.val,A.port=p
  · obtain ⟨A,hA,rfl⟩:=he
    let a : S.val:=⟨A,hA⟩
    have hm : S.resizedArc hS hH hJ a∈R.val := Finset.mem_image.mpr ⟨a,Finset.mem_attach _ _,rfl⟩
    have hh:=R.code_member _ hm
    simpa only [resizedArc_port,resizedArc_shape,code_member S A hA] using hh
  · rw [S.code_empty p he,R.code_empty]
    rintro ⟨A,hA,hp⟩
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hA
    exact he ⟨a.val,a.property,by simpa only [resizedArc_port] using hp⟩

theorem resize_weight (hS : arcChoiceLength S.code≤K) (hH : K<H) (hJ : K<J)
    (hH' : 2*K≤H) (hJ' : 2*K≤J) : (S.resize hS hH hJ hH' hJ').weight=S.weight := by
  unfold weight resize
  dsimp only
  rw [Finset.prod_image (fun A _ B _ he => S.resizedArc_injective hS hH hJ he)]
  simp only [resizedArc,BoundaryArc.resize_weight]
  exact Finset.prod_attach _ _

theorem resize_boundary (hS : arcChoiceLength S.code≤K) (hH : K<H) (hJ : K<J)
    (hH' : 2*K≤H) (hJ' : 2*K≤J) (i : ZMod M) :
    (S.resize hS hH hJ hH' hJ').current ((i,0),0)=S.current ((i,0),0) ∧
    (S.resize hS hH hJ hH' hJ').current ((i,(J : ℤ)),0)=S.current ((i,(H : ℤ)),0) := by
  have he (f : BoundaryArc (bandSites M J) → ℤ) :
      (∑A∈(S.resize hS hH hJ hH' hJ').val,f A)=∑a∈S.val.attach,f (S.resizedArc hS hH hJ a) := by
    exact Finset.sum_image (fun A _ B _ hh => S.resizedArc_injective hS hH hJ hh)
  simp only [current,Finsupp.finsetSum_apply]
  rw [he,he]
  constructor
  · simp only [resizedArc,fun a => (BoundaryArc.resize_boundary hH hJ a i).1]
    exact Finset.sum_attach S.val (fun A => A.current ((i,0),0))
  · simp only [resizedArc,fun a => (BoundaryArc.resize_boundary hH hJ a i).2]
    exact Finset.sum_attach S.val (fun A => A.current ((i,(H : ℤ)),0))

theorem resize_matches (hS : arcChoiceLength S.code≤K) (hH : K<H) (hJ : K<J)
    (hH' : 2*K≤H) (hJ' : 2*K≤J) (inp out : ZMod M → Spin) :
    matchesBoundary (recoverVertical J (S.resize hS hH hJ hH' hJ').current) inp out ↔
    matchesBoundary (recoverVertical H S.current) inp out := by
  have h0 : recoverVertical J (S.resize hS hH hJ hH' hJ').current 0=recoverVertical H S.current 0 := by
    funext i
    simp only [recoverVertical,Fin.val_zero,Nat.cast_zero,(S.resize_boundary hS hH hJ hH' hJ' i).1]
  have ht : recoverVertical J (S.resize hS hH hJ hH' hJ').current (Fin.last J)=
      recoverVertical H S.current (Fin.last H) := by
    funext i
    simp only [recoverVertical,Fin.val_last,(S.resize_boundary hS hH hJ hH' hJ' i).2]
  simp only [matchesBoundary,h0,ht]
end ArcSystem
end PolynomialVacuumCylinder

end OAI
