import OAI.Combinatorics.HadwigerCounterexample.BilinearCompression

namespace OAI

/-! # Channel Factorization -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Submodule Module
open scoped BigOperators
variable {p : Shape} {n : ℕ}
variable {I J : Type} [Fintype I] [Fintype J]

/-- Pairing rank after imposing orthogonality constraints. -/
theorem biorth_exists (S T : Space (Vec I)) (r : ℕ)
    (h : r+dim S+dim T≤Fintype.card I) :
    ∃ A B : Mat I (Fin r), colSp A≤ annih S ∧ colSp B≤ annih T ∧ Aᵀ*B=1 := by
  classical
  let V := annih S
  let W := annih T
  let M := (pack V)ᵀ * pack W
  let t := M.rank
  have ht : r≤t := by
    have h1 := rank_ge_mul (pack V)ᵀ (pack W)
    rw [Matrix.rank_transpose,mrk_inj.mp (pack_inj V),mrk_inj.mp (pack_inj W),
      Fintype.card_fin,Fintype.card_fin] at h1
    have h2 : dim S+dim V=Fintype.card I := annih_dim S
    have h3 : dim T+dim W=Fintype.card I := annih_dim T
    have he (a b c d t r e : ℕ) (h : r+a+b ≤ e) (hx : a+c=e) (hy : b+d=e) (ht : c+d≤t+e) :
        r≤t := by omega
    exact he _ _ _ _ _ _ _ h h2 h3 h1
  obtain ⟨A,B,hA,hB,hM⟩ := rank_product M
  obtain ⟨L,hL⟩ := mat_left_inv hA
  obtain ⟨R,hR⟩ := mat_left_inv (P:=Bᵀ) (transpose_surj_iff.mp (by rw [Matrix.transpose_transpose]; exact hB))
  let E := embedMat (Fin.castLE ht)
  refine ⟨pack V * (Lᵀ * E),pack W*(Rᵀ*E),?_,?_,?_⟩
  · rintro x ⟨x,rfl⟩
    rw [Matrix.mulVecLin_apply,← Matrix.mulVec_mulVec]
    exact (pack_mem_iff ..).mpr ⟨_,rfl⟩
  · rintro x ⟨x,rfl⟩
    rw [Matrix.mulVecLin_apply,← Matrix.mulVec_mulVec]
    exact (pack_mem_iff ..).mpr ⟨_,rfl⟩
  have he : L*M*Rᵀ=1 := by
    have hg : B*Rᵀ=1 := by
      simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] using
        congrArg Matrix.transpose hR
    refine (congrArg (fun X => L*X*Rᵀ) hM).symm.trans ?_
    rw [← Matrix.mul_assoc L,hL,Matrix.one_mul,hg]
  have heq : Eᵀ * E=1 := embedMat_self (Fin.castLE_injective ht)
  rw [Matrix.transpose_mul,Matrix.transpose_mul,Matrix.transpose_transpose]
  calc _ = Eᵀ*(L*M*Rᵀ)*E := by simp only [M,Matrix.mul_assoc]
       _ = _ := by rw [he,Matrix.mul_one,heq]

/-- split desired respective bounded-rank bilinear form -/
theorem pure_chan_split (M : Mat J J) (S T : Space (Vec I)) (X Y : Space (Vec J))
    (h : M∈box (annih X) (annih Y)) (ht : M.rank+dim S+dim T ≤ Fintype.card I) :
    ∃ A ∈ box (annih S) (annih X),∃ B∈box (annih T) (annih Y), Aᵀ * B=M := by
  classical
  obtain ⟨P,Q,hP,hQ,hM⟩ := rank_product M
  obtain ⟨A,B,hA,hB,he⟩ := biorth_exists S T M.rank ht
  obtain ⟨hx,hy⟩ := box_kill.mp h
  refine ⟨A * Pᵀ,?_,B*Q,?_,?_⟩
  · rw [box_kill]
    constructor
    · intro x hx; rw [Matrix.transpose_mul,← Matrix.mulVec_mulVec,(colSp_kill ..).mp hA x hx,
        Matrix.mulVec_zero]
    intro x hv
    have hv' : Pᵀ *ᵥ x=0 := by
      have hqi := (transpose_surj_iff (P:=Qᵀ)).mp (by rw [Matrix.transpose_transpose]; exact hQ)
      apply hqi
      rw [Matrix.mulVec_mulVec,← Matrix.transpose_mul,hM,hx x hv,Matrix.mulVec_zero]
    rw [←Matrix.mulVec_mulVec,hv',mulVec_zero]
  · rw [box_kill]
    constructor
    · intro x hv; rw [Matrix.transpose_mul,←Matrix.mulVec_mulVec,(colSp_kill ..).mp hB x hv,
        Matrix.mulVec_zero]
    intro y hv
    have hv' : Q *ᵥ y=0 := by
      apply hP
      rw [Matrix.mulVec_mulVec,hM,hy y hv,mulVec_zero]
    rw [←Matrix.mulVec_mulVec,hv',mulVec_zero]
  · rw [Matrix.transpose_mul,Matrix.transpose_transpose,← Matrix.mul_assoc _ B, Matrix.mul_assoc P,
      he,Matrix.mul_one,hM]

/-- The final channel change for fixed B endpoint. -/
theorem chan_factor {f b : Plan p n} {P : PureForms p n} {C : ChanOut p n} {j : Bool}
    (H T K : ℕ) (hc : outSmall H C) (hK : ∀ z,dim (hPin b z j)≤K)
    (hh : T+2*(K+2*H)≤p.h)
    (hP : P∈pureSpace p f) (ht : ∀ e,(P e).rank≤T) :
    ∃ D∈deltaSpace p f b j,obsPair p (chanInner p (C+D) (C+D))=
      obsPair p (chanInner p C C)+obsPair p P := by
  classical
  let S (z : Place p) := hPin b (flipZ p z) j ⊔ priOut p C (flipZ p z)
  have h (z : Place p) : dim (S z) ≤ K+2*H :=
    (Submodule.finrank_add_le_finrank_add_finrank ..).trans
      (add_le_add (hK _) (dim_priOut hc _))
  choose A hA B hB hQ using fun e : Comp p.g =>
    pure_chan_split (P e) (S (e,true)) (S (e,false)) (f (e,true)) (f (e,false))
      ((pureSpace_mem _).mp hP e) ((add_le_add
        (add_le_add (ht e) (h (e,true))) (h (e,false))).trans
        (by
          rw [Fintype.card_fin]
          rwa [two_mul, ← add_assoc] at hh))
  let D : ChanOut p n := fun z => if z.2 then A z.1 else B z.1
  have h1 (z : Place p) : D z∈box (annih (S z)) (annih (f z)) := by
    cases z with | mk e c => cases c; exact hB e; exact hA e
  refine ⟨D,(deltaSpace_mem _).mpr ?_,?_⟩
  · intro z
    refine box_le ?_ le_rfl (h1 z)
    intro x hx
    rw [annih_mem]
    exact fun y hy => (annih_mem ..).mp hx y (Submodule.mem_sup_left hy)
  have hg : chanInner p D D=P := funext (fun e => hQ e)
  have he (z : Place p) (i l : Bool) (x y : Ray p n) :
      dotProduct ((C (flipZ p z)*IP p n i) *ᵥ x) ((D z*IP p n l)*ᵥ y)=0 := by
    have hq : ((C (flipZ p z)*IP p n i) *ᵥ x) ∈ S z :=
      Submodule.mem_sup_right (le_priOut C _ i ⟨x,rfl⟩)
    have hl : ((D z * IP p n l)*ᵥ y) ∈ annih (S z) := by
      rw [←Matrix.mulVec_mulVec]
      exact ((box_mem ..).mp (h1 z)).1 ⟨_,rfl⟩
    rw [dotProduct_comm]
    exact (annih_mem ..).mp hl _ hq
  have hd : obsPair p (chanDeriv p C D)=0 := by
    rw [←obsI_each]
    have hz : eachF p (chanDeriv p C D)=0 := by
      unfold chanDeriv; rw [map_add]
      funext i e
      rw [Pi.add_apply,Pi.add_apply,each_chan_val,each_chan_val]
      refine evmat_ext fun x y => ?_
      rw [evmat_addM,ev_duom,ev_duom]
      have hh1 := he (e,false) i i x y
      have hh2 := he (e,true) i i y x
      simp only [flipZ,Bool.not_false,Bool.not_true] at hh1 hh2
      rw [hh1,
        dotProduct_comm ((D (e,true) * IP p n i) *ᵥ _),hh2]
      simp [evmat]
    rw [hz,map_zero]
  rw [obsPair_chan_change,hd,add_zero,hg]

end HadwigerCounterexample

end

end OAI
