import OAI.Combinatorics.HadwigerCounterexample.CoordinateBlocks
import OAI.Combinatorics.HadwigerCounterexample.TensorIntersections

namespace OAI

/-! # Matrix Quotients -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Submodule Module
open scoped BigOperators
variable {I J K L : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype L]

def box (S : Space (Vec I)) (T : Space (Vec J)) :=
  LinearMap.range (liftM (pack S) (pack T))

theorem box_dim (S : Space (Vec I)) (T : Space (Vec J)) :
    dim (box S T) = dim S*dim T := by
  have h := rk_inj.mp (liftM_inj (pack_inj S) (pack_inj T))
  change dim (box S T)=dim (Mat _ _) at h
  rw [dim_mat, Fintype.card_fin,Fintype.card_fin] at h
  exact h

omit [Fintype K] [Fintype L] in
theorem liftM_transpose (A : Mat I J) (P : Mat K I) (Q : Mat L J) :
    (liftM P Q A)ᵀ = liftM Q P Aᵀ := by
  simp only [liftM_def,transpose_mul,transpose_transpose,Matrix.mul_assoc]

theorem box_mem (M : Mat I J) (S : Space (Vec I)) (T : Space (Vec J)) :
    M∈box S T ↔ colSp M ≤ S ∧ colSp Mᵀ ≤ T := by
  classical
  constructor
  · rintro ⟨A,rfl⟩
    rw [liftM_transpose]
    exact ⟨(colSp_lift_le ..).trans_eq (colSp_pack _),
      (colSp_lift_le ..).trans_eq (colSp_pack _)⟩
  · rintro ⟨h,g⟩
    obtain ⟨X,hX⟩ := mat_left_inv (pack_inj S)
    obtain ⟨Y,hY⟩ := mat_left_inv (pack_inj T)
    have h1 {I J : Type} [Fintype I] [Fintype J] {A : Mat I J} {S : Space (Vec I)}
        (h : colSp A ≤ S) {X : Mat (Fin (dim S)) I} (hx : X*pack S=1) : pack S*(X*A)=A := by
      apply coe_mv_inj
      refine LinearMap.ext fun x => ?_
      have he : A*ᵥx ∈ colSp (pack S) := (colSp_pack S).symm ▸
        h (show A*ᵥx∈colSp A from ⟨x,rfl⟩)
      obtain ⟨y,hy⟩ := he
      change pack S *ᵥ y=A *ᵥ x at hy
      change _ *ᵥ _ = _
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hy, Matrix.mulVec_mulVec y X, hx,
        Matrix.one_mulVec]
      exact hy
    refine ⟨liftM X Y M,?_⟩
    have h2 := congrArg Matrix.transpose (h1 g hY)
    rw [transpose_mul,transpose_mul,transpose_transpose] at h2
    change pack S * (X*M*Yᵀ)*(pack T)ᵀ=M
    rw [← Matrix.mul_assoc (pack S) (X*M),h1 h hX,h2]

theorem box_le {M M' : Space (Vec I)} {N N' : Space (Vec J)} (hm : M ≤ M') (hn : N ≤ N') :
    box M N ≤ box M' N' := fun _ h =>
  have he := (box_mem ..).mp h
  (box_mem ..).mpr ⟨he.1.trans hm,he.2.trans hn⟩

theorem pack_mem_iff (v : Vec I) (S : Space (Vec I)) :
    v∈S ↔ ∃ x, pack S *ᵥ x=v := by
  change _ ↔ v∈colSp (pack S)
  rw [colSp_pack]

theorem outer_in_box (x : Vec I) (y : Vec J) {S : Space (Vec I)} {T : Space (Vec J)}
    (hx : x∈S) (hy : y∈T) : vecMulVec x y ∈ box S T := by
  obtain ⟨a,rfl⟩ := (pack_mem_iff ..).mp hx
  obtain ⟨b,rfl⟩ := (pack_mem_iff ..).mp hy
  exact ⟨vecMulVec a b,liftM_outer ..⟩

theorem lift_mem_box {M : Mat I J} {S : Space (Vec I)} {T : Space (Vec J)}
    (P : Mat K I) (Q : Mat L J) (h : M ∈ box S T) :
    liftM P Q M ∈ box (S.map P.mulVecLin) (T.map Q.mulVecLin) := by
  obtain ⟨A,rfl⟩ := h
  rw [liftM_comp,box_mem,liftM_transpose]
  constructor <;> apply le_trans (colSp_lift_le ..) <;>
    rw [colSp,mulVecLin_mul,LinearMap.range_comp]
  · rw [show LinearMap.range (pack S).mulVecLin=S from colSp_pack _]
  rw [show LinearMap.range (pack T).mulVecLin=T from colSp_pack _]

theorem evmat_transpose (M : Mat I J) (x : Vec I) (y : Vec J) :
    evmat Mᵀ y x=evmat M x y := dotProduct_transpose_mulVec _ _ _
theorem evmat_pull (P : Mat K I) (Q : Mat L J) (A : Mat K L) (x : Vec I) (y : Vec J) :
    evmat (pullM P Q A) x y=evmat A (P *ᵥ x) (Q *ᵥ y) := by
  rw [←mpair_outer,←mpair_outer,← liftM_outer,mpair_liftM]; rfl

theorem evmat_ext {M N : Mat I J} (h : ∀ x y, evmat M x y=evmat N x y) : M=N := by
  classical
  ext i j
  simpa [evmat] using h (Pi.single i 1) (Pi.single j 1)

theorem box_eval_iff (S : Space (Vec I)) (T : Space (Vec J)) (M N : Mat I J) :
    (∀ x∈S,∀ y∈T,evmat M x y=evmat N x y) ↔ (∀ x∈box S T,mpair M x=mpair N x) := by
  constructor
  · intro h x hx
    have hE : pullM (pack S) (pack T) M=pullM (pack S) (pack T) N := by
      refine evmat_ext (fun x y => ?_)
      rw [evmat_pull,evmat_pull]
      exact h _ ((pack_mem_iff ..).mpr ⟨x,rfl⟩) _ ((pack_mem_iff ..).mpr ⟨y,rfl⟩)
    obtain ⟨A,rfl⟩ := hx
    rw [mpair_liftM,mpair_liftM]
    exact congrArg (fun x => mpair x A) hE
  intro h x hx y hy
  rw [← mpair_outer,← mpair_outer]
  exact h _ (outer_in_box _ _ hx hy)

def annih (S : Space (Vec I)) := ker ((pack S)ᵀ.mulVecLin)

theorem annih_dim (S : Space (Vec I)) :
    dim S + dim (annih S) = Fintype.card I := by
  have h := (pack S)ᵀ.mulVecLin.finrank_range_add_finrank_ker
  change ((pack S)ᵀ).rank + dim (annih S)=dim (Vec I) at h
  rwa [Matrix.rank_transpose,mrk_inj.mp (pack_inj _),dim_vec,Fintype.card_fin] at h

theorem dot_ext_zero {x : Vec I} (h : ∀ y, dotProduct y x=0) : x=0 := by
  classical funext i
            simpa using h (Pi.single i 1)

theorem annih_mem (x : Vec I) (S : Space (Vec I)) :
    x ∈ annih S ↔ ∀ y ∈ S,dotProduct x y = 0 := by
  change (pack S)ᵀ *ᵥ x=0 ↔ _
  constructor
  · intro h y hy
    obtain ⟨z,rfl⟩ := (pack_mem_iff ..).mp hy
    rw [← dotProduct_transpose_mulVec,h,dotProduct_zero]
  intro h
  refine dot_ext_zero fun y => ?_
  rw [dotProduct_transpose_mulVec]; exact h _ ((pack_mem_iff ..).mpr ⟨y,rfl⟩)

theorem annih_annih (S : Space (Vec I)) : annih (annih S)=S := by
  symm
  have hh : S ≤ annih (annih S) := by
    intro x hx; rw [annih_mem]
    intro y hy; rw [dotProduct_comm]
    exact (annih_mem ..).mp hy _ hx
  refine Submodule.eq_of_le_of_finrank_eq hh ?_
  have he := annih_dim S
  have hg := annih_dim (annih S)
  change dim S=_

  exact Nat.add_right_cancel ((he.trans hg.symm).trans (Nat.add_comm ..))

def vanish (S : Space (Vec I)) (T : Space (Vec J)) (M : Mat I J) :=
  ∀ x ∈ annih S, ∀ y∈ annih T, evmat M x y=0

/-- A tensor killed by the product of the two factor quotients has bounded rank. -/
theorem rank_vanish {S : Space (Vec I)} {T : Space (Vec J)} {M : Mat I J}
    (h : vanish S T M) : M.rank≤dim S+dim T := by
  let P := pack (annih S)
  let Q := pack (annih T)
  have hh : Pᵀ*M*Q=0 := by
    refine evmat_ext fun x y => ?_
    have he := h _ ((pack_mem_iff ..).mpr ⟨x,rfl⟩) _ ((pack_mem_iff ..).mpr ⟨y,rfl⟩)
    rw [← evmat_pull] at he
    exact he.trans (by simp [evmat])
  have h1 := rank_ge_mul Pᵀ M
  have h2 := rank_ge_mul (Pᵀ*M) Q
  have hi := (mrk_inj.mp (pack_inj (annih S))).trans (Fintype.card_fin _)
  have hj := (mrk_inj.mp (pack_inj (annih T))).trans (Fintype.card_fin _)
  rw [Matrix.rank_transpose] at h1
  change P.rank = _ at hi; change Q.rank = _ at hj
  rw [hi] at h1; rw [hj,hh,Matrix.rank_zero] at h2
  have hx := annih_dim S
  have hy := annih_dim T
  have hv (x y z u v a b r : ℕ) (h : u+x≤r+a) (g : r+v≤0+b) (hx : y+u=a) (hy : z+v=b) :
      x≤y+z := by omega
  exact hv _ _ _ _ _ _ _ _ h1 h2 hx hy

end HadwigerCounterexample

end

end OAI
