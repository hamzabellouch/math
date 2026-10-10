import OAI.Combinatorics.HadwigerCounterexample.OffsetLifting

namespace OAI

/-! # Offset Records -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Finset Function
open scoped BigOperators
variable {p : Shape} {r n N : ℕ}

def fpAt (p : Shape) {n N} (w : Orient p n N) (z : Place p) :=
  primary (takeSign (w z.1) z.2)
def fyAt (p : Shape) {n N} (w : Orient p n N) (z : Place p) :=
  channel (takeSign (w z.1) z.2)
def imageP (p : Shape) {n N} (w : UnitType p n N) (i : Bool) : Cov p N :=
  fun z => colSp (fpAt p (onSide w i) z)

abbrev BMark (p : Shape) (n N : ℕ) := UnitType p n N → Bool → Profile p n
def mrAmbient {p : Shape} {n N} (m : BMark p n N) (x : UnitType p n N) (i : Bool) :=
  Uembed (onSide x i) (m x i)
def delta {p : Shape} {n N} (m : BMark p n N) (x : UnitType p n N) :=
  mrAmbient m x true+mrAmbient m x false

theorem mr_box (m : BMark p n N) (x) (i) (e : Comp p.g) :
    mrAmbient m x i e∈box (imageP p x i (e,true)) (imageP p x i (e,false)) := by
  let P := fpAt p (onSide x i) (e,true)
  let Q := fpAt p (onSide x i) (e,false)
  change liftM P Q _∈box (colSp P) (colSp Q)
  rw [box_mem,liftM_transpose]
  exact ⟨colSp_lift_le .., colSp_lift_le ..⟩

abbrev Wide (p : Shape) (r : ℕ) := Place p → Fin (r+1)
abbrev OffBasis (p : Shape) (r : ℕ) {N} (S : Cov p N) (q : Wide p r) :=
  ∀ z, Mat (Fin (dim (S z))) (Fin (q z).val)
abbrev OffAux (p : Shape) (r : ℕ) (q : Wide p r) :=
  ∀ e : Comp p.g,Mat (Fin (q (e,true)).val) (Fin (q (e,false)).val)
abbrev Atlas (p : Shape) (r : ℕ) {N} (S : Cov p N) :=
  Σ q : Wide p r, OffBasis p r S q × OffAux p r q

instance aFintype (S : Cov p N) : Fintype (Atlas p r S) := by
  classical
  letI : (q : Wide p r) → Fintype (OffBasis p r S q) := fun q => inferInstance
  letI : (q : Wide p r) → Fintype (OffAux p r q) := fun q => inferInstance
  exact inferInstanceAs (Fintype (Atlas p r S))
instance aDefault (S : Cov p N) : Inhabited (Atlas p r S) :=
  ⟨⟨fun _ => (0:Fin (r+1)),0,0⟩⟩

variable {S : Cov p N}

abbrev breadth {p : Shape} {N r} {S : Cov p N} (X : Atlas p r S) := fun z : Place p => (X.1 z).val
def cells {p : Shape} {N r} {S : Cov p N} (X : Atlas p r S) := ∑ z : Place p,breadth X z

abbrev Batch {p : Shape} {N r} {S : Cov p N} (X : Atlas p r S) (n) :=
  DTuple (p:=p) (breadth X) n

def src (X : Atlas p r S) : Batch X N :=
  fun z => pack (S z) * X.2.1 z

def edgeCost (X : Atlas p r S) : Ambient p N :=
  fun e => liftM (src X (e,true)) (src X (e,false)) (X.2.2 e)
def spelled (X : Atlas p r S) (A : Batch X N) : Ambient p N := fun e =>
  src X (e,true)*(A (e,true))ᵀ + A (e,false) * (src X (e,false))ᵀ + edgeCost X e

/-- comp for A play Zplus paired offset+, Zminus paired offset-.
Companion columns at each compared sign in **opposite** sign primal frame.
-/
def compFor (X : Atlas p r S) (A : Batch X N) (C : Cov p N)
    (D : Ambient p N) :=
  (∀ z, Injective (A z).mulVec ∧ colSp (A z) ≤ C (flipZ p z)) ∧ D=spelled X A

def locIndep (X : Atlas p r S) := ∀ z, Injective (src X z).mulVec

def standard (X : Atlas p r S) := cells X ≠ 0 ∧ cells X≤2*r ∧ locIndep X

private theorem join_order (p : Shape) {N r} (g : Ambient p N)
    (q p' : Comp p.g → ℕ) (hyp : ∀ e, q e≤ (g e).rank) (hyp' : ∀ e,p' e ≤ (g e).rank)
    (h : epoch p g≤r) :
    ∃ ω : Wide p r, (∀ e,(ω (e,true)).val=q e) ∧ (∀ e,(ω (e,false)).val=p' e) ∧
      (∑ z,(ω z).val) ≤2*r := by
  classical
  have ht (e) : (g e).rank ≤ r :=
    (Finset.single_le_sum (fun i _ => Nat.zero_le ((g i).rank)) (Finset.mem_univ e)).trans h
  let Q := fun e => (⟨q e,Nat.lt_succ_of_le ((hyp e).trans (ht e))⟩ : Fin (r+1))
  let P := fun e => (⟨p' e,Nat.lt_succ_of_le ((hyp' e).trans (ht e))⟩ : Fin (r+1))
  let ω : Wide p r := fun x => if x.2 then Q x.1 else P x.1
  refine ⟨ω,fun _ => rfl, fun _ => rfl,?_⟩
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool,Finset.sum_add_distrib]
  rw [two_mul]
  exact Nat.add_le_add ((Finset.sum_le_sum fun i _ => hyp i).trans h)
    ((Finset.sum_le_sum fun i _ => hyp' i).trans h)

set_option maxHeartbeats 800000 in
theorem delta_offset (m : BMark p n N) (x)
    (h : covered p S (delta m x))
    (hz : delta m x ≠0)
    (hs : ∀ i z,Disjoint (S z) (imageP p x i z))
    (hr : epoch p (mrAmbient m x true)≤r) :
    ∃ X : Atlas p r S,standard X ∧ ∀ i,∃ A,compFor X A (imageP p x i) (delta m x) := by
  classical
  choose q p' A B H hT using fun e : Comp p.g =>
    one_offsets (fun i => mrAmbient m x i e) (S (e,true)) (S (e,false))
      (fun i => imageP p x i (e,true)) (fun i => imageP p x i (e,false))
      (fun i => mr_box m x i e)
      ((covered_iff ..).mp h e)
      (fun i => hs i _) (fun i => hs i _)
  obtain ⟨g,hg,hG,hS⟩ := join_order p (mrAmbient m x true) q p'
    (fun i => (hT i).1) (fun i => (hT i).2.1) hr

  have ht (e : Comp p.g) :
      ∃ (A' : Mat (Fin (dim (S (e,true)))) (Fin (g (e,true)).val))
        (B' : Mat (Fin (dim (S (e,false)))) (Fin (g (e,false)).val))
        (H' : Mat (Fin (g (e,true)).val) (Fin (g (e,false)).val)),
        let X := pack (S (e,true)) * A'
        let Y := pack (S (e,false))* B'
        Injective X.mulVec ∧ Injective Y.mulVec ∧
        ∀ i : Bool,∃ (Z : Mat (Fin N) (Fin (g (e,true)).val)) (W : Mat (Fin N) (Fin (g (e,false)).val)),
          Injective Z.mulVec ∧ Injective W.mulVec ∧
          colSp Z≤ imageP p x i (e,false) ∧ colSp W≤ imageP p x i (e,true) ∧
          delta m x e=X*Zᵀ+W*Yᵀ+X*H'*Yᵀ := by
    rw [hg,hG]
    exact ⟨A e,B e,H e,(hT e).2.2⟩
  choose A' B' H' hL hR hyp using fun e => by simpa only using ht e
  let X : Atlas p r S := ⟨g, (fun z => match z with
    | ⟨e,true⟩ => A' e
    | ⟨e,false⟩ => B' e),H'⟩
  have he (i) : ∃ Z,compFor X Z (imageP p x i) (delta m x) := by
    choose Z W hZ hW hC hD hJ using fun e => hyp e i
    refine ⟨(fun z => match z with | ⟨e,true⟩ => Z e | ⟨e,false⟩ => W e),?_,funext fun e => ?_⟩
    · rintro ⟨e,c|c⟩
      · exact ⟨hW e,hD e⟩
      exact ⟨hZ e,hC e⟩
    exact hJ e
  refine ⟨X,⟨?_,hS,?_⟩,he⟩
  · intro hc
    have h1 (z) : breadth X z = 0 := Nat.eq_zero_of_le_zero
      (show _≤0 from le_trans
        (Finset.single_le_sum (fun z _ => Nat.zero_le (breadth X z)) (Finset.mem_univ z))
        hc.le)
    obtain ⟨A,_,hA⟩ := he true
    apply hz
    rw [hA]
    funext e
    let (z : Place p) : IsEmpty (Fin (breadth X z)) := by rw [h1]; infer_instance
    unfold spelled edgeCost
    ext
    simp only [liftM_def,Matrix.add_apply,Matrix.mul_apply]
    change _ = 0

    simp
  · rintro ⟨e,c|c⟩
    · exact hR e
    exact hL e

def offsetCov (X : Atlas p r S) : Cov p N := fun z => colSp (src X z)

theorem offsetCov_dim (p : Shape) {r N} {S : Cov p N} (X : Atlas p r S) :
    cdim p (offsetCov X)≤cells X := Finset.sum_le_sum fun i _ =>
  (src X i).rank_le_card_width.trans_eq (Fintype.card_fin _)

/-- Capturing offsets suffices to cover the tensor. -/
theorem covered_spelled (X : Atlas p r S) (A) (T : Cov p N) (he : offsetCov X ≤ T) :
    covered p T (spelled X A) := by
  apply (cover_mem ..).mpr
  intro e
  let P := src X (e,true)
  let Q := src X (e,false)
  have h : ∀ V : Mat (Fin (breadth X (e,true))) (Fin N), P*V∈box (T (e,true)) ⊤ :=
    fun V => (box_mem ..).mpr ⟨(col_follow ..).trans (he _),le_top⟩
  have h' (V : Mat (Fin N) (Fin (breadth X (e,false)))) :
      V*Qᵀ ∈box ⊤ (T (e,false)) := by
    rw [box_mem,transpose_mul,transpose_transpose]
    exact ⟨le_top,(col_follow ..).trans (he _)⟩
  unfold spelled
  refine Submodule.add_mem _ (add_mem_sup (h _) (h' _)) (Submodule.mem_sup_left ?_)
  unfold edgeCost
  rw [liftM_def,Matrix.mul_assoc]
  exact h _

theorem atlas_size (S : Cov p N) (r : ℕ) :
    num (Atlas p r S) ≤ num (Wide p r) * bp (cdim p S*r+(num (Comp p.g))*r*r) := by
  classical
  change (↑(Fintype.card (Atlas p r S)) : ℝ) ≤ _
  unfold Atlas
  rw [Fintype.card_sigma,Nat.cast_sum]
  have hg (q : Wide p r) :
      (↑(Fintype.card (OffBasis p r S q×OffAux p r q)):ℝ) ≤ bp (cdim p S*r+(num (Comp p.g))*r*r) := by
    rw [card_space]
    apply bp_le
    have ht : dim (OffBasis p r S q)≤ cdim p S*r := by
      unfold dim OffBasis
      rw [finrank_pi_fintype]
      unfold cdim; rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      have h := dim_mat (Fin (dim (S i))) (Fin (q i).val)
      rw [Fintype.card_fin,Fintype.card_fin] at h
      exact h.trans_le (Nat.mul_le_mul_left _ (Nat.lt_add_one_iff.mp (q i).isLt))
    have hu : dim (OffAux p r q) ≤ Fintype.card (Comp p.g)*r*r := by
      unfold dim OffAux
      rw [finrank_pi_fintype]
      refine (Finset.sum_le_sum (g:=fun _ => r*r) fun i _ => ?_).trans_eq ?_
      · refine (dim_mat _ _).trans_le ?_
        rw [Fintype.card_fin,Fintype.card_fin]
        exact Nat.mul_le_mul (Nat.lt_add_one_iff.mp (q _).isLt) (Nat.lt_add_one_iff.mp (q _).isLt)
      simp [mul_assoc]
    unfold dim
    rw [Module.finrank_prod,Nat.cast_add]
    have hsum := add_le_add ht hu
    unfold num
    exact_mod_cast hsum
  exact (Finset.sum_le_sum fun i _ => hg i).trans_eq (by simp [num])

end HadwigerCounterexample

end

end OAI
