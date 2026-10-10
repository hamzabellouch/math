import OAI.Combinatorics.HadwigerCounterexample.MomentCoordinates
import OAI.Combinatorics.HadwigerCounterexample.MatrixFactorization

namespace OAI

/-! # Boolean Labels -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Finset
variable {b : ℕ}

def monoBit (s : Label b) (S : Finset (Fin b)) := ∏ i ∈ S, s i

theorem mono_insert (s : Label b) (S : Finset (Fin b)) (i) :
    monoBit s (insert i S) = s i * monoBit s S := by
  by_cases h : i∈S
  · rw [insert_eq_of_mem h]
    unfold monoBit
    rw [← Finset.mul_prod_erase _ _ h,← mul_assoc,bit_sq]
  · simp [monoBit,h]

theorem mono_union (s : Label b) (S T : Finset (Fin b)) :
    monoBit s (S∪T)= monoBit s S*monoBit s T := by
  induction S using Finset.induction with
  | empty => simp [monoBit]
  | insert i S h ih =>
    rw [insert_union,mono_insert,mono_insert,ih,mul_assoc]

/-- Independence up to degree j for at most j+1 labels, in coefficient form. -/
theorem selector_indep (L : Finset (Label b)) (c : Label b → F) (j : ℕ)
    (h : L.card ≤ j+1) (hf : ∀ S : Finset (Fin b), S.card ≤ j →
      ∑ s ∈ L,c s*monoBit s S=0) : ∀ i∈L,c i=0 := by
  classical
  intro s hs
  induction L using Finset.strongInductionOn generalizing c j with | _ L ih
  by_cases hL : ∃ i∈L,i≠s
  · obtain ⟨t,ht,hst⟩ := hL
    obtain ⟨i,hi⟩ : ∃ i : Fin b,t i≠s i := Function.ne_iff.mp hst
    let d (u : Label b) := (u i-t i) * c u
    have hg : j>0 := by have he := Finset.one_lt_card.mpr ⟨t,ht,s,hs,hst⟩; omega
    have he : (L.erase t).card ≤ (j-1)+1 := by
      have he := card_erase_add_one ht; omega
    have hw (U : Finset (Fin b)) (hu : U.card ≤ j-1) :
        ∑ s ∈ L.erase t,d s*monoBit s U=0 := by
      have heq (s : Label b) :
          d s * monoBit s U = c s * monoBit s (insert i U) - t i*(c s*monoBit s U) := by
        unfold d; rw [mono_insert]; ring
      rw [show ∑ s ∈ L.erase t,d s*monoBit s U = ∑ s ∈ L,d s*monoBit s U by
        conv_rhs => rw [← Finset.add_sum_erase _ _ ht]
        simp [d]]
      simp_rw [heq, Finset.sum_sub_distrib,← Finset.mul_sum]
      have hj : (insert i U).card ≤ j := by
        by_cases hh : i∈U
        · rw [insert_eq_of_mem hh]; omega
        · rw [card_insert_of_notMem hh]; omega
      rw [hf _ hj, hf _ (by omega),mul_zero,sub_zero]
    have hu := ih (L.erase t) (erase_ssubset ht) d (j-1) he hw
      (Finset.mem_erase.mpr ⟨hst.symm,hs⟩)
    exact (mul_eq_zero.mp hu).resolve_left (sub_ne_zero.mpr hi.symm)
  · have he : L={s} := by
      ext x; constructor
      · intro hx; exact mem_singleton.mpr (Classical.byContradiction fun h => hL ⟨x,hx,h⟩)
      intro hx; rwa [mem_singleton.mp hx]
    have hh := hf ∅ (by simp)
    simpa [he,monoBit] using hh

variable {p : Shape} {n : ℕ}

def hankel (M : Moment p n) :=
  ∀ (i k : AIdx p.g n) (a b c d : SelIdx p.b p.j),
    a.val ∪ b.val = c.val ∪ d.val → M (a,i) (b,k) = M (c,i) (d,k)

def diagBase (M : Moment p n) :=
  ∀ (i : AIdx p.g n) (a b : SelIdx p.b p.j), M (a,i) (b,i) = M (a,none) (b,i)

theorem point_eval (p : Shape) (s : Label p.b) (z : Base p.g n)
    (r : SelIdx p.b p.j) (i : AIdx p.g n) : point p s z (r,i) = monoBit s r.val * baseV z i :=
  rfl

theorem Wspace_hank {M : Moment p n} (h : M∈Wspace p n) : hankel M := by
  intro i k a b c d hab
  unfold Wspace at h
  induction h using Submodule.span_induction with
  | mem M hm =>
    obtain ⟨s,z,rfl⟩ := hm
    have h (a b : SelIdx p.b p.j) :
        mom p s z (a,i) (b,k) = monoBit s (a.val ∪ b.val) * (baseV z i*baseV z k) := by
      simp only [mom,vecMulVec_apply,point_eval,mono_union]; ring
    rw [h,h,hab]
  | zero => rfl
  | add x y _ _ hx hy => simp only [Matrix.add_apply,hx,hy]
  | smul v x _ hx => simp only [Matrix.smul_apply,hx]

theorem Wspace_diag {M : Moment p n} (h : M∈Wspace p n) : diagBase M := by
  intro i a b
  unfold Wspace at h
  induction h using Submodule.span_induction with
  | mem M hm =>
    obtain ⟨s,z,rfl⟩ := hm
    simp only [mom,vecMulVec_apply,point_eval,baseV]
    rw [mul_mul_mul_comm,bit_sq]
    have hn : Option.elim' (1:F) z none = 1 := rfl
    rw [hn]
    ring
  | zero => rfl
  | add x y _ _ hx hy => simp only [Matrix.add_apply,hx,hy]
  | smul v x _ hx => simp only [Matrix.smul_apply,hx]

abbrev BaseMat (p : Shape) (n : ℕ) := Mat (AIdx p.g n) (AIdx p.g n)

def labMat (p : Shape) (n) (s : Label p.b) :
    Mat (Row p n) (AIdx p.g n) :=
  Matrix.of (fun v i => if v.2=i then monoBit s v.1.val else 0)

theorem labMat_act (s) (z : Vec (AIdx p.g n)) :
    labMat p n s *ᵥ z = putLab p n s z := by
  funext i
  simp [Matrix.mulVec,dotProduct,labMat,putLab,monoBit,selV]

def mput (p : Shape) (s : Label p.b) {n} :
    BaseMat p n →ₗ[F] Moment p n := liftM (labMat p n s) (labMat p n s)

theorem mput_apply (s) (Z : BaseMat p n) (i j) : mput p s Z i j =
    monoBit s i.1.val*monoBit s j.1.val*Z i.2 j.2 := by
  classical
  simp [mput,liftM_def,Matrix.mul_apply,transpose_apply,labMat, mul_comm,mul_left_comm,mul_assoc]

theorem mput_hank (s) (Z : BaseMat p n) : hankel (mput p s Z) := by
  intro i j a b c d h
  rw [mput_apply,mput_apply]
  simp_rw [← mono_union,h]

/-- Short label-tagged rays give a direct family of copies of the affine-vector space. -/
theorem ray_indep (L : Finset (Label p.b)) (Z : Label p.b → Vec (AIdx p.g n))
    (hj : L.card ≤ p.j+1) (he : ∑ i∈L, putLab p n i (Z i) = 0) :
    ∀ i∈L, Z i=0 := by
  have hg (u : AIdx p.g n) (i : Label p.b) (hi : i ∈ L) :
      Z i u=0 := by
    refine selector_indep L (fun i => Z i u) p.j hj ?_ i hi
    intro S hS
    have hh := congr_fun he ((⟨S,hS⟩ : SelIdx p.b p.j),u)
    simpa [putLab,Finset.sum_apply,monoBit,selV,mul_comm] using hh
  exact fun i hi => funext (fun u => hg u i hi)

end HadwigerCounterexample

end

end OAI
