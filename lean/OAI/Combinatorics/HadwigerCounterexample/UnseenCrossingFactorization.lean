import OAI.Combinatorics.HadwigerCounterexample.FourCornerMasks

namespace OAI

/-! # Unseen Crossing Factorization -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Function Filter
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]
variable [DecidableEq J]
namespace Template
variable (v : Template p I)

private def spot (w : v.PackSlot) (A : PlusRack Unit N) :=
  upliftR (fun _:Unit=>w) A

omit [Fintype I] in
private theorem spot_else (w : v.PackSlot) (A : PlusRack Unit N) {i : v.PackSlot} (hi : i≠w) (j) :
    spot v w A j i=0 := by simp [spot,upliftR,Matrix.mul_apply,embedMat,hi]

private theorem spot_blind (j : I) (c : Corn) (w : v.PackSlot) (hc : ¬ sees v j c w)
    (x : v.PackStack N) (A : PlusRack Unit N) :
    yieldK v j c (x+(spot v w A,0)) = yieldK v j c x ∧
    yieldK v j c (x+(0,spot v w A)) = yieldK v j c x := by
  classical
  have hh {x y : v.PackStack N}
      (h : ∀ i,sees v j c i→∀ z,x.1 z i=y.1 z i∧x.2 z i=y.2 z i) :
      yieldK v j c x=yieldK v j c y := by
    funext i l b z
    let k : v.PackSlot := (arm j i c,⟨i,l⟩)
    have he : sees v j c k := rfl
    change yieldK v j c x k.2.1 k.2.2 b z=yieldK v j c y k.2.1 k.2.2 b z
    rw [yield_view _ j c x k he,yield_view _ j c y k he,(h k he z).1,(h k he z).2]
  constructor <;> apply hh <;> intro i hi z <;>
    simp only [Prod.fst_add,Prod.snd_add,Matrix.add_apply, Matrix.zero_apply,
      spot_else v w A (show i≠w from (fun h => hc (h ▸ hi))),add_zero,and_self]

set_option maxHeartbeats 800000 in
theorem cant_leak (v : Template p I) (j : I) (U : Wgt (Keys (p:=p) v.t N))
    (hU : ∀ i, |U i|≤1) (f : Vec (cantRail v j)) (hf : f≠0) :
    |avg unif (fun x=>phasedBy (ledgerM _ f) x * packSecs v j U x)| ≤ bp (-(N:ℝ)/2) := by
  classical
  obtain ⟨⟨⟨a,b⟩,hab⟩,he⟩ := Function.ne_iff.mp hf
  let M := ledgerM _ f
  have hh : M a b=1 := by
    unfold M ledgerM; simp only [Matrix.of_apply,dite_eq_left hab]
    exact (bit_cases _).resolve_left he
  let s := Finset.univ.filter (fun c=>sees v j c a)
  let t := univ\s
  let g (s : Finset Corn) (x : v.PackStack N) := ∏ i∈s,U (yieldK v j i x)
  have h0 (s x) : |g s x|≤1 := by unfold g; rw [abs_prod]; exact
    (prod_le_prod₀ (fun i _=>abs_nonneg _) (fun i _=>hU _)).trans_eq (by simp)
  let A (_ : Unit) := a
  let B (_ : Unit) := b
  have h1 x (q : PlusRack Unit N) : g s (x+(0,upliftR B q))=g s x := by
    apply prod_congr rfl
    intro k hk
    have ht (h : sees v j k b) := ((cant_mem ..).mp hab).2 ⟨k,(mem_filter.mp hk).2,h⟩
    exact congrArg _ (spot_blind v j k b ht x q).2
  have h2 x (q : PlusRack Unit N) : g t (x+(upliftR A q,0))=g t x := by
    apply prod_congr rfl
    intro k hk
    have ht (h : sees v j k a) :=
      (mem_sdiff.mp hk).2 (mem_filter.mpr ⟨mem_univ _,h⟩)
    exact congrArg _ (spot_blind v j k a ht x q).1
  let r := fun _ : v.PackStack N=> (1:ℝ)
  have hx x : phasedBy M x * packSecs v j U x=phasedBy M x * g s x * g t x*r x := by
    simp only [r,mul_one,mul_assoc]
    unfold g t packSecs; rw [mul_comm (∏ z∈s,_),prod_sdiff (subset_univ s)]
  change |avg unif (fun x=> phasedBy M x*_)|≤_
  simp_rw [hx]
  have ht := layerLeak M (g s) (g t) r A B (h0 s) (h0 t) h1 h2 (fun _ _ _=>rfl)
  have he : M.submatrix A B=1 := by ext i j; cases i; cases j; rw [Matrix.one_apply_eq]; exact hh
  simpa only [r,he,Matrix.rank_one,Fintype.card_unit,Nat.cast_one,mul_one,abs_one,
    unif_law.avg_const] using ht

def chairCut (v : Template p I) (j : I) (U : Wgt (Keys (p:=p) v.t N)) (δ : ℝ) :=
  thinCut unif U (Prod.fst ∘ v.chairK j N) (Prod.snd ∘ v.chairK j N) δ

theorem global_quart (v : Template p I) (j : I) (U : Wgt (Keys (p:=p) v.t N))
    (hU : ∀ i,|U i|≤1) (δ : ℝ) (h : chairCut v j U δ) :
    |avg unif (packSecs v j U)|≤δ := by
  classical
  let E := v.chairK j N
  have ht : mapW unif E=pairW unif unif := by rw [←pair_unif,unif_equiv]
  change |avg unif (fun i=>quart E U (v.untwin N i))|≤_
  rw [← mapW_avg,unif_equiv,pair_unif]
  exact quart_small E _ _ _ _ ht unif_law unif_law hU δ h
end Template
end HadwigerCounterexample

end

end OAI
