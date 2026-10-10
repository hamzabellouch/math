import OAI.Combinatorics.HadwigerCounterexample.MixerConditions

namespace OAI

/-! # Binary Evaluation Forms -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix
variable {p : Shape} {n : ℕ}

theorem pullT {I J V U : Type} [Fintype V] [Fintype U]
    (A : Mat V U) (P : Mat U I) (Q : Mat V J) :
    pullM P Q Aᵀ = (pullM Q P A)ᵀ := by
  rw [pullM_def,pullM_def,transpose_mul,transpose_mul,transpose_transpose,Matrix.mul_assoc]

theorem indexed_linear {c : Vec (MBits p)} {D D' : Draw p n} :
    indexedSum (drawn (p:=p) (D+D')) c =
      indexedSum (drawn D) c + indexedSum (drawn D') c := by
  have h (i : MBits p) :
      eitherM i.2 (orderedM (drawn (p:=p) (D+D')) i.1) =
        eitherM i.2 (orderedM (drawn D) i.1) + eitherM i.2 (orderedM (drawn D') i.1) := by
    rcases i with ⟨⟨⟨a,b,d⟩,_|_⟩,_|_⟩ <;> rfl
  unfold indexedSum
  simp_rw [h,smul_add,Finset.sum_add_distrib]

def obsZ (p : Shape) (n : ℕ) (s t : Label p.b) (c : Vec (MBits p)) :
    Draw p n →ₗ[F] Mat (Fin n) (Fin n) where
  toFun D := pullM (blockRay p n s Block.Z) (blockRay p n t Block.Z) (indexedSum (drawn D) c)
  map_add' _ _ := by rw [indexed_linear,map_add]
  map_smul' a x := by
    have h (i : MBits p) :
        eitherM i.2 (orderedM (drawn (p:=p) (a•x)) i.1)=
          a • eitherM i.2 (orderedM (drawn x) i.1) := by
      rcases i with ⟨⟨⟨a,b,d⟩,_|_⟩,_|_⟩ <;> rfl
    simp only [indexedSum,h,map_sum,map_smul,RingHom.id_apply,Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

theorem obsZ_self (s t : Label p.b) (f : Vec Bool) (m : Mixer p n) :
    pullM (blockRay p n s Block.Z) (blockRay p n t Block.Z) (selfSum m f) = 0 := by
  rw [selfSum,Fintype.sum_bool,map_add,map_smul,map_smul]
  change _ • pullM _ _ (selfM p n m.mixM) + _ • pullM _ _ (selfM p n m.mixM)ᵀ = 0
  rw [pullT,pull_self_Z,pull_self_Z]
  simp

private theorem two_eval (s t : Label p.b) (hj : 1≤p.j) (hs : s≠t)
    (x : Bool → Mat (Fin n) (Fin n)) :
    ∃ A : Moment p n, ∀ b, pullM (blockRay p n s Block.Z) (blockRay p n t Block.Z)
      (eitherM b A) = x b := by
  let P := blockRay p n s Block.Z
  let Q := blockRay p n t Block.Z
  have hh : Function.Injective (fromCols P Q).mulVec := joined_block_inj hj hs _
  obtain ⟨L,hL⟩ := prescribe_between hh hh
    (fromBlocks (0:Mat (Fin n) (Fin n)) (x true) (x false)ᵀ (0:Mat (Fin n) (Fin n)))
  rw [transpose_fromCols,fromRows_mul,fromRows_mul_fromCols] at hL
  have hx : pullM P Q L = x true := congrArg Matrix.toBlocks₁₂ hL
  have hy : pullM Q P L = (x false)ᵀ := congrArg Matrix.toBlocks₂₁ hL
  refine ⟨L,fun b => ?_⟩
  cases b
  · change pullM P Q Lᵀ=x false
    rw [pullT,hy,transpose_transpose]
  · exact hx

theorem obsZ_surj (s t : Label p.b) (hj : 1≤p.j) (hs : s≠t)
    {c : Vec (MBits p)} (hc : c ≠ 0) : Function.Surjective (obsZ p n s t c) := by
  classical
  simp only [ne_eq,funext_iff,Pi.zero_apply,not_forall] at hc
  obtain ⟨i,hi⟩ := hc
  intro M
  let y (j : MBits p) := if j=i then M else 0
  choose A hA using fun j : MOne p => two_eval s t hj hs (fun b => y (j,b))
  let D : Draw p n := (fun j => A (j,true), fun j => A (j,false), 0)
  have he (j : MBits p) :
      pullM (blockRay p n s Block.Z) (blockRay p n t Block.Z)
        (eitherM j.2 (orderedM (drawn D) j.1)) = y j := by
    rcases j with ⟨⟨j,_|_⟩,x⟩
    · exact hA _ _
    · exact hA _ _
  refine ⟨D,?_⟩
  simp only [obsZ,indexedSum,map_sum,map_smul,he,LinearMap.coe_mk,AddHom.coe_mk]
  rw [Finset.sum_eq_single i]
  · simp [y,(bit_cases (c i)).resolve_left hi]
  · intro j _ hj; simp [y,hj]
  simp

def selfPartial (s t : Label p.b) (f : Vec Bool) (D : Draw p n) : Mat (Fin n) (Fin n) :=
  let A := ∑ a, (s a+t a) • D.2.2 a
  f true • A+f false • Aᵀ

theorem pull_selfPart (s t : Label p.b) (hj : 1 ≤ p.j) (f : Vec Bool) (D : Draw p n) :
    pullM (blockRay p n s Block.sharp) (blockRay p n t Block.sharp) (selfSum (drawn D) f) =
      selfPartial (p:=p) s t f D := by
  rw [selfSum, Fintype.sum_bool,map_add,map_smul,map_smul]
  change _ • pullM _ _ (selfM p n D.2.2) + _ • pullM _ _ (selfM p n D.2.2)ᵀ = _
  rw [pullT,pull_self_sharp _ _ _ hj,pull_self_sharp _ _ _ hj]
  unfold selfPartial
  congr 2
  simp only [add_comm]

def obsHalf (p : Shape) (s t : Label p.b) (f : Vec Bool) (n : ℕ)
    (l r : Fin (n/2)→Fin n) : Draw p n →ₗ[F] Mat (Fin (n/2)) (Fin (n/2)) where
  toFun D := (selfPartial (p:=p) s t f D).submatrix l r
  map_add' _ _ := by
    simp only [selfPartial, Prod.snd_add, Pi.add_apply, smul_add, Finset.sum_add_distrib,
      transpose_add, Matrix.submatrix_add]
    abel
  map_smul' a D := by
    simp only [selfPartial,Prod.smul_snd,Pi.smul_apply,RingHom.id_apply]
    let F (D : Draw p n) := ∑ i, (s i+t i) • D.2.2 i
    have h :
        ∑ i, (s i+t i) • (a • D.2.2 i) = a • F D := by
      unfold F; rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun _ _ => smul_comm _ _ _
    rw [h,Matrix.transpose_smul]
    rw [smul_comm (f true),smul_comm (f false) a, ← smul_add]
    rfl

/-- Uniform off-diagonal block even in transpose-character case. -/
theorem obsHalf_surj (s t : Label p.b) (hs : s≠t) {f : Vec Bool} (hf : f≠0) (n : ℕ)
    {l r : Fin (n/2)→Fin n} (hl : Function.Injective l) (hr : Function.Injective r)
    (h : ∀ i j,l i≠r j) : Function.Surjective (obsHalf p s t f n l r) := by
  classical
  intro M
  obtain ⟨a,ha⟩ : ∃ a,s a+t a=1 := by
    obtain ⟨a,ha⟩ := Function.ne_iff.mp hs
    exact ⟨a,(bit_cases _).resolve_left (fun h => ha
      (add_right_cancel (h.trans (char_two _).symm)))⟩
  let m := n/2
  let P := embedMat l
  let Q := embedMat r
  have hi : Function.Injective (fromCols P Q).mulVec := by
    have he : fromCols P Q = embedMat (Sum.elim l r) := by ext i j; cases j <;> rfl
    rw [he]; apply embedMat_inj
    rintro (x|x) (y|y) g
    · rw [hl g]
    · exact (h _ _ g).elim
    · exact (h _ _ g.symm).elim
    · rw [hr g]
  have hv (x y : Mat (Fin m) (Fin m)) :
      ∃ A : Mat (Fin n) (Fin n), A.submatrix l r=x ∧ Aᵀ.submatrix l r=y := by
    obtain ⟨A,hA⟩ := prescribe_between hi hi (fromBlocks (0:Mat (Fin m) (Fin m)) x yᵀ
      (0:Mat (Fin m) (Fin m)))
    rw [transpose_fromCols,fromRows_mul,fromRows_mul_fromCols] at hA
    have h1 : Pᵀ*A*Q=x := congrArg Matrix.toBlocks₁₂ hA
    have h2 : Qᵀ*A*P=yᵀ := congrArg Matrix.toBlocks₂₁ hA
    unfold P Q at *
    rw [embedMat_mul,mul_embedMat] at h1 h2
    exact ⟨A,h1,congrArg Matrix.transpose h2⟩
  obtain ⟨x,y,hx⟩ : ∃ x y : Mat (Fin m) (Fin m), f true • x+f false • y=M := by
    rcases bit_cases (f true) with g|g
    · have hg : f false≠0 := fun hg => hf (funext fun i => by cases i <;> assumption)
      exact ⟨0,M,by rw [(bit_cases _).resolve_left hg]; simp⟩
    · exact ⟨M,0,by rw [g]; simp⟩
  obtain ⟨A,h1,h2⟩ := hv x y
  let D : Draw p n := (0,0,Pi.single a A)
  have hE :
      ∑ i,(s i+t i) • D.2.2 i=A := by
    rw [Finset.sum_eq_single a]
    · simp [D,ha]
    · intro i _ hi; simp [D,Pi.single_eq_of_ne hi]
    simp
  refine ⟨D,?_⟩
  change (selfPartial (p:=p) s t f D).submatrix l r=M
  unfold selfPartial
  rw [hE]
  change (f true • A + f false • Aᵀ).submatrix l r = _
  change f true • A.submatrix l r + f false • Aᵀ.submatrix l r = M
  rw [h1,h2,hx]

end HadwigerCounterexample

end

end OAI
