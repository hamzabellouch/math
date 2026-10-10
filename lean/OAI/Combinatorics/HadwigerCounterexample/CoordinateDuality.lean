import OAI.Combinatorics.HadwigerCounterexample.ScalarStatusAlgebra

namespace OAI

/-! # Coordinate Duality -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Submodule Function
open scoped BigOperators
namespace StatusAnalysis
variable {A B : Rates} {d e : ℕ}

structure DualCoefficients (A B : Rates) where
  left : Quota
  right : Quota
  gam : Grid→F
  hed : Grid→F
  north : (i:Grid)→ Cell (A i.1)
  south : (i:Grid)→ Cell (B i.2)
def DualCoefficients.bet (p : DualCoefficients A B) (i : Grid) (x : LedgerS A B i) :=
  p.gam i * x.1 + p.hed i * x.2.1 + (dotProduct (p.north i) x.2.2.1+
    dotProduct (p.south i) x.2.2.2)
def DualCoefficients.law (p : DualCoefficients A B) (V : StatusSp A B) :=
  ∀ i:Grid,∀ v∈V i, p.bet i (want _ _ v) =
    p.left i.2 * couple _ v.2.1 + p.right i.1 * couple _ v.2.2

private theorem coordinates (f : Question d e →ₗ[F] F) :
    ∃ a b : F,∃ (u : Cell d) (v : Cell e),∀ (x:Question d e),
    f x=a*x.1+b*x.2.1 + (dotProduct u x.2.2.1+dotProduct v x.2.2.2) := by
  let g := f ∘ₗ LinearMap.inr F F _ ∘ₗ LinearMap.inr F F _
  obtain ⟨u,hu⟩:=dotL_surj (g ∘ₗ LinearMap.inl F _ _)
  obtain ⟨v,hv⟩:=dotL_surj (g ∘ₗ LinearMap.inr F _ _)
  let a : Question d e := (1,0); let b : Question d e := (0,1,0)
  refine ⟨f a,f b,u,v,?_⟩
  rintro ⟨x,y,z,w⟩
  have he : ((x,y,z,w):Question d e)=x • a +y • b+((0,0,z,0)+(0,0,0,w)) := by
    unfold a b; ext <;> simp
  have h1 : f (0,0,z,0)=dotProduct u z := LinearMap.congr_fun hu z
  have h2 : f (0,0,0,w)=dotProduct v w := LinearMap.congr_fun hv w
  change f (x,y,z,w)=f a*x + f b*y + _
  conv_lhs => rw [he]
  rw [map_add,map_add,map_add,map_smul,map_smul,h1,h2]; simp [mul_comm]

theorem jargon_score (V : StatusSp A B) (T : Cabinet A B)
    (h : ¬scorecard V T) (hh : ∀ i,coverBase (V i)) :
    ∃ p : DualCoefficients A B, (p.left≠0 ∨ p.right≠0) ∧ p.law V ∧ ∑ i,p.bet i (T i)≠0 := by
  obtain ⟨p,hp,hf⟩:= counter_score V T h
  choose a b u v he using fun i=>coordinates (p.alf i)
  let g : DualCoefficients A B:=⟨p.altL,p.altR,a,b,u,v⟩
  have hz i x : g.bet i x=p.alf i x := (he i x).symm
  refine ⟨g,critic_nz V T hh p hp hf,fun i x hx=>?_,?_⟩
  · rw [hz]; exact hp i x hx
  simp_rw [hz]; exact hf

abbrev excessK (V : Space (Signal d e)) := V ⊓ LinearMap.ker (view d e)
theorem signal_dim :
    dim (Signal d e) = dim (View d e)+2 := by
  simp only [Signal,View,Whole,dim,finrank_prod,finrank_self]
  omega
theorem ker_two (V : Space (Signal d e)) :
    dim (excessK V) ≤ 2 := by
  have he : Surjective (view d e) := by
    rintro ⟨i,j,k⟩; exact ⟨(i,(j,0),(k,0)),rfl⟩
  have ht := LinearMap.finrank_range_add_finrank_ker (view d e)
  change rk (view _ _) + dim _=dim (Signal d e) at ht
  rw [rk_surj.mp he,signal_dim] at ht
  exact (Submodule.finrank_mono (show excessK V≤_ from inf_le_right)).trans
    (by omega : dim (LinearMap.ker (view d e)) ≤ 2)

def overage (V : Space (Signal d e)) := dim V - dim (View d e)
theorem overage_two (V : Space (Signal d e)) : overage V≤2 := by
  have hi : dim V ≤ dim (Signal d e) := finrank_le _
  rw [signal_dim] at hi; unfold overage; omega
theorem overage_mono {V W : Space (Signal d e)} (h : V≤W) :
    overage V≤overage W := Nat.sub_le_sub_right (finrank_mono h) _
theorem overage_lt {V W : Space (Signal d e)} (h : V<W) (he : coverBase V) :
    overage V<overage W := by
  have hh := finrank_lt_finrank_of_lt h; change dim V<dim W at hh
  have hx : dim (View d e) ≤ dim V := LinearMap.finrank_le_finrank_of_surjective he
  unfold overage; omega
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
