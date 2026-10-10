import OAI.Combinatorics.HadwigerCounterexample.QuadraticFourier

namespace OAI

/-! # Tester Fourier Support -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module Submodule Function LinearMap Finset
open scoped BigOperators
variable {p : Shape} {n : ℕ}

theorem roleT_scan (p : Shape) (i l : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (x : Knobs p.g n) :
    roleT p n i (useAtom p l s f x) = ∑ d:Tag p.g,scan p l f x (.inl (d,i)) := by
  classical
  unfold useAtom atom
  let M := mom p s (lit f l x)
  have h (t : Tag p.g) : (Pi.single l M : Tag p.g→ Moment p n) t ∈Wtag p n t := by
    by_cases ht : t=l
    · subst t; rw [Pi.single_eq_same]; exact Submodule.subset_span ⟨_,_,lit_allows f l x,rfl⟩
    simp [ht]
  rw [roleT_cut p i _ h,Finset.sum_eq_single l,Pi.single_eq_same]
  · simp_rw [scan_is p l s]; rfl
  · intro i _ hi; simp [hi]
  simp

theorem sharedT_scan (p : Shape) (hg : Odd p.g) (i l : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (x : Knobs p.g n) :
    let r := scan p l f x (.inr ())
    sharedT p n i (useAtom p l s f x)= r+(if l=i then r else 0) := by
  classical
  intro r
  unfold r useAtom atom
  rw [sharedT_cut _ hg,Finset.sum_eq_single l]
  · rw [Pi.single_eq_same,scan_is p l s f]; by_cases h : i=l <;> simp [h,asBlock,Ne.symm]
  · intro i _ hi; simp [hi]
  simp

theorem T0_scanZ (p : Shape) (hg : Odd p.g) (l : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (x : Profile p n) (u : Knobs p.g n) (y) :
    T0 p n x (useAtom p l s f (update u Block.Z y))=T0 p n x (useAtom p l s f u) := by
  simp_rw [T0_val,role_scan,roleT_scan]
  have h i : sharedT p n i (useAtom p l s f (update u Block.Z y))=sharedT p n i
      (useAtom p l s f u) := by rw [sharedT_scan p hg i,sharedT_scan p hg i]; simp only [scannedZ]
  simp_rw [h,scannedZ]

namespace Template

variable (v : Solo p)
def shanty (v : Solo p) (m : Mixer p n) (x : Profile p n) (t : Knobs p.g n) :=
  wsign (Tsym m x (useAtom p (v.t ()) (v.s ()) (v.f ()) t))
def stave (v : Solo p) (n : ℕ) := blockRay p n (v.s ()) Block.Z
def slash (v : Solo p) (m : Mixer p n) (x : Profile p n) := qmix m x (v.t ())

def scroll (v : Solo p) (m : Mixer p n) (x : Profile p n) :=
  let P:=stave v n; let M := slash v m x
  colSp (Pᵀ*M) ⊔ colSp (Pᵀ*Mᵀ)

theorem scroll_dim (v : Solo p) (m : Mixer p n) (x : Profile p n) :
    dim (scroll v m x) ≤ 2*(p.J*(p.g-1)*(2*totalRank x)) := by
  let P:=stave v n; let M:=slash v m x; let k:=p.J*(p.g-1)*(2*totalRank x)
  have hm : M.rank ≤ k := qmix_rank ..
  have h1 : dim (colSp (Pᵀ*M)) ≤ k := (Matrix.rank_mul_le_right ..).trans hm
  have h2 : dim (colSp (Pᵀ*Mᵀ)) ≤ k :=
    (Matrix.rank_mul_le_right ..).trans ((Matrix.rank_transpose _).le.trans hm)
  exact (Submodule.finrank_add_le_finrank_add_finrank ..).trans
    ((Nat.add_le_add h1 h2).trans_eq (two_mul _).symm)

theorem shanty_arc (v : Solo p) (m : Mixer p n) (x : Profile p n)
    (hg : Odd p.g) (u : Knobs p.g n) :
    let P := v.stave n; let M:= v.slash m x
    ∃ a : Ray p n,∃ b : F,∀ y,
      v.shanty m x (update u Block.Z y)=
        wsign (b + evmat M (P *ᵥ y+a) (P *ᵥ y+a)) := by
  intro P M
  let l := v.t (); let s := v.s (); let f := v.f ()
  let A := spring p l s f (update u Block.Z (0 : Vec (Fin n)))
  let b := T0 p n x (useAtom p l s f u)
  refine ⟨A,b,fun y => ?_⟩
  let t := update u Block.Z y
  let k := useAtom p l s f t
  have hx : Tsym m x k = T0 p n x k + evmat M (spring p l s f t) (spring p l s f t) := by
    unfold Tsym k useAtom; rw [LinearMap.add_apply,LinearMap.add_apply,Tmix_atom]
    exact congrArg (_ + ·) (mpair_outer ..)
  have ht : spring p l s f t=P *ᵥ y+A := (spring_update _ _ _ _ _ _ (Flavor.keepZ ..) _).trans
    (add_comm _ _)
  change wsign (Tsym m x k)=_
  rw [hx,ht]; unfold k t b
  rw [T0_scanZ p hg]

set_option maxHeartbeats 600000 in
theorem shanty_cap (v : Solo p) (m : Mixer p n) (x : Profile p n)
    (K s : ℕ) (hg : Odd p.g) (hm : unaryGood m K s) (hK : totalRank x≤K)
    (hx : 0<totalRank x) (u : Knobs p.g n) (i : Vec (Fin n)) :
    |zhat p (v.shanty m x) u i|≤bp (-((p.J-s:ℕ):ℝ)) := by
  classical
  obtain ⟨a,b,hab⟩ := shanty_arc v m x hg u
  let P := v.stave n; let M:= v.slash m x
  have hh := flare_affine M P a b i
  unfold zhat vectorPhase; simp_rw [hab,←wsign_add]
  have h : 2*((p.J-s:ℕ):ℝ)≤ (pullM P P (M+Mᵀ)).rank := by
    exact_mod_cast hm x (v.t ()) (v.s ()) hK hx
  exact (flare_rank _ (pullM P P (M+Mᵀ)) hh).trans (bp_le (by linarith only [h]))

set_option maxHeartbeats 800000 in
theorem shanty_outer (v : Solo p) (m : Mixer p n) (x : Profile p n) (u : Knobs p.g n)
    (hg : Odd p.g) (i : Vec (Fin n)) (hi : i∉scroll v m x) :
    zhat p (v.shanty m x) u i=0 := by
  classical
  let S:=scroll v m x; let P:=stave v n; let M:=slash v m x
  have hh : ∃ j∈annih S,dotProduct i j=1 := by
    by_contra! h
    apply hi
    rw [show v.scroll m x=S from rfl, ← annih_annih S]
    refine (annih_mem ..).mpr (fun j hj => (bit_cases _).resolve_right (h _ hj))
  obtain ⟨t,ht,he⟩ := hh
  let W y := v.shanty m x (update u Block.Z y)
  let C := P *ᵥ t
  have hz (y) : W (y+t)=W y := by
    obtain ⟨a,b,hQ⟩ := shanty_arc v m x hg u
    have hh (M : Moment p n) (h : colSp (Pᵀ*M)≤S) (i : Ray p n) :
        dotProduct C (M *ᵥ i)=0 := by
      have h1 := (annih_mem ..).mp ht _ (h (show (Pᵀ*M)*ᵥi∈_ from ⟨i,rfl⟩))
      rw [← mulVec_mulVec,dotProduct_transpose_mulVec] at h1; rw [dotProduct_comm]; exact h1
    let B := fun y => P *ᵥ y+a
    unfold W; simp_rw [hQ]
    change wsign (b+evmat M (B (y+t)) (B (y+t)))=_
    rw [show B (y+t)=B y+C by unfold B C; rw [mulVec_add]; ac_rfl]
    have h1 z : evmat M C z=0 := hh M le_sup_left z
    have h2 z : evmat M z C=0 := (evmat_transpose M _ _).symm.trans (hh Mᵀ le_sup_right z)
    unfold evmat at *
    simp_rw [mulVec_add,dotProduct_add,add_dotProduct,h1,h2]
    simp only [add_zero,B,P,M,mulVec_add,dotProduct_add,add_dotProduct]
  unfold zhat
  let Q (y) := vectorPhase i y*W y
  have hq (y) :
      Q (y+t) = Q y * (-1) := by unfold Q vectorPhase; rw [hz,dotProduct_add,wsign_add,he,wsign_one]; ring
  change avg unif Q=0
  have hh := phase_trans t Q
  simp_rw [hq] at hh; rw [avg_mul] at hh; linarith
end Template
end HadwigerCounterexample

end

end OAI
