import OAI.Combinatorics.HadwigerCounterexample.FreeBlockFourier

namespace OAI

/-! # Quadratic Fourier -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Module LinearMap Submodule Function Finset
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem phase_trans (t : Vec I) (f : Wgt (Vec I)) :
    avg unif (fun y => f (y+t))=avg unif f := by
  let E : Vec I ≃ Vec I := ⟨(·+t),(·+t),add_polar t,add_polar t⟩
  exact avg_bij E unif f

theorem half_power (x a : ℝ) (ha : x^2 ≤ bp a) : |x|≤ bp (a/2) :=
  le_of_pow_le_pow_left₀ (by decide : 2≠0) (bp_pos _).le (by
    rw [sq_abs,pow_two (bp _),←bp_add,show a/2+a/2=a by ring]; exact ha)

def polarize (f : Vec I→F) (M : Mat I I) :=
  ∀ x y,f (x+y)+f x=f y+f 0+dotProduct y (M *ᵥ x)

set_option maxHeartbeats 600000 in
theorem flare_rank (f : Vec I→F) (M : Mat I I) (h : polarize f M) :
    |avg unif (fun x => wsign (f x))| ≤ bp (-(M.rank:ℝ)/2) := by
  classical
  let g (x : Vec I) := wsign (f x)
  have hh :
      avg unif g ^ 2 = avg unif (fun x : Vec I => avg unif (fun y : Vec I =>
        g (x+y)*g y)) := by
    have hi (i : Vec I) : avg unif (fun x => g (x+i)*g i)=avg unif g*g i := by
      rw [avg_mul,phase_trans]
    rw [avg_avg]; simp_rw [hi,avg_mul']
    ring
  let L := Mᵀ
  have hg x y : g (x+y)*g y= wsign (f x+f 0)*wsign (dotL (L *ᵥ x) y) := by
    unfold g; rw [← wsign_add,← wsign_add,add_comm x y,h y x]
    unfold L
    congr 2
    change dotProduct x (M *ᵥ y)=dotProduct _ y
    rw [dotProduct_comm _ y,dotProduct_transpose_mulVec]
  have hi (x : Vec I) :
      avg unif (fun y : Vec I => g (x+y)*g y) ≤ ind ((L *ᵥ x)=0) := by
    simp_rw [hg x,avg_mul',wsign_lin]
    have he : dotL (L *ᵥ x)=0 ↔ L *ᵥ x=0 := by
      constructor
      · exact fun h => dot_ext_zero fun y => by rw [dotProduct_comm]; exact LinearMap.congr_fun h y
      intro h; rw [h]; exact LinearMap.ext (fun x => zero_dotProduct x)
    rw [he]
    exact (mul_le_mul_of_nonneg_right ((le_abs_self _).trans_eq (wsign_abs _))
      (ind_nonneg _)).trans_eq (one_mul _)
  refine half_power _ _ (?_)
  change avg unif g^2≤_
  rw [hh]
  refine (avg_mono unif_law.nz hi).trans_eq ?_
  have he : pr unif (fun x => L.mulVecLin x=0) = _ := pr_unif_lin L.mulVecLin 0
  rw [ind_one (LinearMap.range L.mulVecLin).zero_mem,one_mul] at he
  change pr unif _=_
  exact he.trans (by change bp (-(L.rank:ℝ))=_; rw [show L=Mᵀ from rfl,Matrix.rank_transpose])

omit [DecidableEq I] [DecidableEq J] in
theorem flare_affine (M : Mat J J) (P : Mat J I) (k : Vec J) (a : F) (i : Vec I) :
    let Q := fun x => dotProduct i x + (a + evmat M (P *ᵥ x+k) (P *ᵥ x+k))
    polarize Q (pullM P P (M+Mᵀ)) := by
  intro Q x y
  have he : dotProduct y ((pullM P P (M+Mᵀ)) *ᵥ x)=
      evmat M (P *ᵥ y) (P *ᵥ x) + evmat M (P *ᵥ x) (P *ᵥ y) := by
    change evmat _ _ _=_
    rw [evmat_pull,evmat_addM, evmat_transpose]
  rw [he]
  unfold Q evmat
  simp only [dotProduct_zero,Matrix.mulVec_zero,mulVec_add,dotProduct_add,add_dotProduct,
    zero_add]

  ring_nf
  simp only [mul_two,char_two,add_zero,zero_add]
end HadwigerCounterexample

end

end OAI
