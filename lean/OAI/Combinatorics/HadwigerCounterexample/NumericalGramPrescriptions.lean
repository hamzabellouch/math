import OAI.Combinatorics.HadwigerCounterexample.SyntheticArraySlices

namespace OAI

/-! # Numerical Gram Prescriptions -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Function LinearMap Module
open scoped BigOperators Pointwise
variable {p : Shape} {n N d e : ℕ} {I : Type} [Fintype I] [DecidableEq I]

def spacePunch (p : Shape) (l : Tag p.g) (f : Flavor p.g) :=
  (Finset.univ.filter (usesPunch p l f)).card

omit [DecidableEq I] in
set_option maxHeartbeats 800000 in
theorem punch_real (p : Shape) (l : Tag p.g) (f : Flavor p.g) (G : Mat I I)
    (h : G.rank≤spacePunch p l f) :
    ∃ a : I→ Tickets p,labGram p l f a=G := by
  classical
  let P:= Finset.univ.filter (usesPunch p l f)
  let q:=Fintype.equivFinOfCardEq (Fintype.card_coe P)
  obtain ⟨u,v,hg⟩:=mul_factor G P.card h
  let x (i:I) (j:Punch p) := if h:j∈P then u i (q ⟨j,h⟩) else 0
  let y (i:I) (j:Punch p) := if h:j∈P then v (q ⟨j,h⟩) i else 0
  let a (i:I) : Tickets p := fun j => if j.2 then x i j.1 else y i j.1
  refine ⟨a,?_⟩
  rw [←hg]; ext i j
  change (∑ t:Punch p,(if usesPunch p l f t then a i (t,true)*a j (t,false) else 0))=∑ t,u i t * v t j
  have ht (t:Punch p) : a i (t,true)*a j (t,false)=x i t*y j t := rfl
  simp_rw [ht,← Finset.sum_filter]
  change ∑ t∈P,x i t*y j t=_
  calc _ = ∑ t:P,x i t.val*y j t.val := Eq.symm (Finset.sum_coe_sort P (fun t=>x i t*y j t))
       _ = _ := by
        have hh (t : ↑P) : x i t.val*y j t.val=u i (q t)*v (q t) j := by
          unfold x y; rw [dite_eq_left t.property,dite_eq_left t.property]
        simp_rw [hh]; exact Equiv.sum_comp q (fun t=>u i t*v t j)

theorem beam_rank (f : Sextant d e) : (pullM (cartM f) (cartM f) (beamMap e)).rank≤d := by
  classical
  rw [cart_target]
  let V := (beamMap e).submatrix (reflectSextant f) (reflectSextant f)
  let P : Mat (Hue d) (Fin d) := embedMat (fun x=>incarn x true)
  let Q : Mat (Fin d) (Hue d) := Matrix.of fun i j => V (incarn i true) j
  have hnone (j : Hue d) : V none j = 0 := rfl
  have hfalse (i : Fin d) (j : Hue d) : V (some (false,i)) j = 0 := by
    cases j with
    | none => rfl
    | some j => rcases j with ⟨b,j⟩; cases b <;> rfl
  have h : P*Q=V := by
    ext i j
    rcases i with _|⟨b,i⟩
    · simp [Matrix.mul_apply,P,embedMat,incarn,hnone]
    cases b
    · simp [Matrix.mul_apply,P,embedMat,incarn,hfalse]
    · simp [Matrix.mul_apply,P,Q,embedMat,incarn]
  change V.rank≤ d
  rw [←h]
  exact (Matrix.rank_mul_le_left ..).trans ((P.rank_le_card_width).trans_eq (by simp))

theorem sharedPunch (p : Shape) (hr : 1≤p.r) (l : Tag p.g) :
    1 ≤ spacePunch p l Flavor.sharedOnly := by
  let i : Punch p := (.inr (),⟨0,hr⟩)
  exact Finset.card_pos.mpr ⟨i,Finset.mem_filter.mpr ⟨mem_univ _,trivial⟩⟩

/-- selected pure excludes second tags -/
def creed (p : Shape) (E : Finset (Tag p.g)) :=
  Flavor.pure (Finset.univ.filter fun i : Tag p.g×Tag p.g => i.2∉E)

theorem purePunch (p : Shape) (l : Tag p.g) (E : Finset (Tag p.g)) :
    ((p.g-1)/2)*(p.g-E.card)*p.r≤spacePunch p l (creed p E) := by
  classical
  let u := Finset.univ.filter (fun i=> allowed i l)
  let v := Finset.univ\ E
  let Z := u ×ˢ (v ×ˢ (Finset.univ : Finset (Fin p.r)))
  let f (i : Tag p.g × Tag p.g × Fin p.r) : Punch p := (.inl (i.1,i.2.1),i.2.2)
  have hf : Injective f := by
    rintro ⟨i,j,k⟩ ⟨x,y,z⟩ h
    simpa only [Prod.mk.injEq,Sum.inl.injEq,f,and_assoc] using h
  have he : Z.image f⊆ Finset.univ.filter (usesPunch p l (creed p E)) := by
    rintro i hi
    obtain ⟨⟨i,j,k⟩,hv,rfl⟩:=mem_image.mp hi
    simp only [Z,u,v,mem_product,mem_sdiff,mem_filter,mem_univ,true_and,and_true] at hv
    refine mem_filter.mpr ⟨mem_univ _,?_⟩
    exact ⟨hv.1,mem_filter.mpr ⟨mem_univ _,hv.2⟩⟩
  have ht := card_le_card he
  rw [card_image_of_injective _ hf] at ht
  have hu : u.card=(p.g-1)/2 := by
    have h:= card_allowed' l; rw [Fintype.card_subtype] at h; exact h
  unfold spacePunch
  refine le_trans ?_ ht
  unfold Z v; rw [card_product,card_product,Finset.card_sdiff_of_subset (subset_univ _),
    card_univ,card_univ,hu,Fintype.card_fin,Fintype.card_fin,
    mul_assoc]
end HadwigerCounterexample

end

end OAI
