import OAI.Combinatorics.HadwigerCounterexample.PinInjectionTests

namespace OAI

/-! # Injection Witnesses -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module Submodule Function Finset
open scoped BigOperators
variable {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
private def moreMatrix {r : ℕ} (A : Mat I (Fin r)) (v : Vec I) : Mat I (Fin (r+1)) :=
  Matrix.of (fun i => Fin.cons (v i) (A i))

omit [Fintype I] in
private theorem moreMatrix_act {r : ℕ} (A : Mat I (Fin r)) (v : Vec I)
    (x : Vec (Fin (r+1))) :
    moreMatrix A v *ᵥ x=x 0 • v + A *ᵥ (fun i => x i.succ) := by
  funext i; simp only [Matrix.mulVec,dotProduct,moreMatrix,Matrix.of_apply,
    Fin.sum_univ_succ,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Fin.cons_zero,Fin.cons_succ]
  congr 1; exact mul_comm _ _

omit [Fintype I] in
private theorem moreMatrix_inj {r : ℕ} (A : Mat I (Fin r)) (v : Vec I)
    (ha : Injective A.mulVec) (h : v∉colSp A) :
    Injective (moreMatrix A v).mulVec := by
  rw [← Matrix.coe_mulVecLin,← LinearMap.ker_eq_bot, Matrix.ker_mulVecLin_eq_bot_iff]
  intro x hx
  rw [moreMatrix_act] at hx
  let b (i : Fin r) := x i.succ
  rcases bit_cases (x 0) with he|he
  · have hh : b=0 := by
      apply ha
      rw [he,zero_smul,zero_add] at hx
      exact hx.trans (Matrix.mulVec_zero _).symm
    funext i
    refine Fin.cases he (fun k => ?_) i
    exact congr_fun hh k
  · rw [he,one_smul] at hx
    have heq : v=A *ᵥ b := add_right_cancel (hx.trans (char_two _).symm)
    exact (h ⟨b,heq.symm⟩).elim

variable {p : Shape} {n N : ℕ}
def pushCost (l : ℝ) (K : ℕ) := l/bp K

set_option maxHeartbeats 800000 in
private theorem booming (b : Fpins p n N) (K k t : ℕ) (hk : k≤t)
    (hK : ∀ x,planRank (b x) ≤ K) (z : Place p) (i j : Bool)
    (w v : Wgt (UnitType p n N)) (hw : IsLaw w) (hv : IsLaw v) {l : ℝ} (hl : 0 < l)
    (hf : ∀ T : Space (Vec (Fin N)),dim T ≤ t →
      pr w (fun x => ¬Disjoint (imageP p x i z) T) ≤ l)
    (Q : UnitType p n N→Prop) (hp : 0 < pr v Q)
    (hQ : ∀ y,Q y→3*l≤ pr w (fun x => fans b z i j x y)) :
    ∃ Y : Mat (Fin N) (Fin k), Injective Y.mulVec ∧
      (pushCost l K)^k * pr v Q ≤ pr v (fun y => Q y ∧ ∀ m,strikeH b z j (Y.col m) y) := by
  classical
  have hx : 0<pushCost l K := div_pos hl (bp_pos _)
  induction k with
  | zero =>
    refine ⟨0,fun a b _ => Subsingleton.elim a b,?_⟩
    simp
  | succ k ih =>
    obtain ⟨Y,hY,hA⟩ := ih (Nat.le_of_succ_le hk)
    let S (y) := Q y∧∀ m,strikeH b z j (Y.col m) y
    have hq : 0 < pr v S := lt_of_lt_of_le (mul_pos (pow_pos hx _) hp) hA
    let P (x : UnitType p n N) := Disjoint (imageP p x i z) (colSp Y)
    obtain ⟨x,hx,hP⟩ :
        ∃ x,P x ∧ l*pr v S<pr v (fun y => S y ∧ fans b z i j x y) := by
      have hg :
          avg w (fun x => ind (P x)*pr v (fun y => S y∧fans b z i j x y))=
          avg v (fun y => ind (S y)*pr w (fun x => fans b z i j x y∧P x)) := by
        unfold pr; simp_rw [← avg_mul',ind_and]
        rw [avg_avg]; apply congrArg; funext y
        apply congrArg; ext; ring
      have he : pr w (fun x => ¬ P x) ≤ l := hf _ ((Y.rank_le_card_width.trans_eq
        (Fintype.card_fin _)).trans (Nat.le_of_succ_le hk))
      let g (x) := ind (P x)*pr v (fun y => S y∧fans b z i j x y)
      have hh : 2*l*pr v S≤avg w g := by
        unfold g; rw [hg]
        unfold pr; rw [← avg_mul']; refine avg_mono hv.nz fun y => ?_
        by_cases ht : S y
        · rw [ind_one ht,mul_one,one_mul]
          refine le_trans ?_ (pr_shield hw.nz (fun x => fans b z i j x y) P)
          have hh := hQ y ht.1; linarith
        rw [ind_zero ht,zero_mul,mul_zero]
      obtain ⟨x,hx⟩ : ∃ x,l*pr v S<g x := by
        by_contra! hn
        have hw := hh.trans (hw.avg_le hn)
        nlinarith
      by_cases hi : P x
      · exact ⟨x,hi,by simpa only [g,ind_one hi,one_mul] using hx⟩
      have he : g x=0 := by simp [g,ind_zero hi]
      rw [he] at hx
      exact (not_lt_of_ge (mul_pos hl hq).le hx).elim
    let R := rootSet b x i z
    let C (v : R) (y : UnitType p n N) := v.val≠0 ∧ S y ∧ strikeH b z j v.val y
    obtain ⟨a,ha⟩ :
        ∃ a : R,pushCost l K*pr v S<pr v (C a) := by
      have h (y) : (S y∧fans b z i j x y) → ∃ a : R,C a y := by
        rintro ⟨h,a,ha,hk,hb⟩; exact ⟨⟨a,ha⟩,hk,h,hb⟩
      have hh := (hP.trans_le (pr_mono hv.nz h)).trans_le (pr_exists_le hv.nz C)
      by_contra! he
      have ht := hh.trans_le (Finset.sum_le_sum fun i _ => he i)
      rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,card_space] at ht
      have hlg : bp (dim R) ≤ bp K := bp_le (by exact_mod_cast ((rootSet_dim ..).trans (hK x)))
      have he' := mul_le_mul_of_nonneg_right hlg (show 0≤pushCost l K*pr v S by
        unfold pushCost; exact mul_nonneg (div_nonneg hl.le (bp_pos _).le) hq.le)
      have hr : bp (K:ℝ)*(pushCost l K*pr v S)=l*pr v S := by
        have hz := bp_pos (K:ℝ)
        unfold pushCost
        field_simp
      exact (lt_irrefl _ (ht.trans_le (he'.trans_eq hr)))
    have hc : a.val≠0 := by
      by_contra hc
      rw [show C a=(fun _ => False) by unfold C; rw [hc]; simp,pr_false] at ha
      have h := div_pos hl (bp_pos (K:ℝ))
      exact (not_lt_of_ge (mul_pos h hq).le ha).elim
    refine ⟨moreMatrix Y a.val,moreMatrix_inj Y _ hY ?_,?_⟩
    · intro h
      exact hc (Submodule.disjoint_def.mp hx a.val ((rootSet_subset ..) a.property) h)
    · have hC y (h : C a y) : Q y ∧ ∀ m,strikeH b z j ((moreMatrix Y a.val).col m) y := by
        refine ⟨h.2.1.1,fun k => Fin.cases h.2.2 (fun m => ?_) k⟩
        have hh : (moreMatrix Y a.val).col m.succ=Y.col m := by
          ext; simp [Matrix.col_apply,moreMatrix]
        rw [hh]; exact h.2.1.2 m
      rw [pow_succ,mul_comm _ (pushCost l K),mul_assoc]
      exact ((mul_le_mul_of_nonneg_left hA (div_pos hl (bp_pos _)).le).trans ha.le).trans
        (pr_mono hv.nz hC)

set_option maxHeartbeats 600000 in
theorem cannon {b : Fpins p n N} (K k : ℕ)
    (hK : ∀ x,planRank (b x) ≤ K) (z : Place p) (i j : Bool)
    (w v : Wgt (UnitType p n N)) (hw : IsLaw w) (hv : IsLaw v)
    {l : ℝ} (hl : 0 < l)
    (m : Mixer p n) {A B : ℝ} (hL : 0≤ A) (hB : 0 ≤ B)
    (he : bySide p w m A) (hf : bySide p v m B)
    (hN : 2*num (Full p n)-N≤ -1)
    (hg : A*2*bp (num (Row p n)+k-N) ≤ l) :
    pr v (fun y => 3*l≤ pr w (fun x => fans b z i j x y)) ≤
      fireBill p k K B / (pushCost l K)^k := by
  classical
  let Q := fun y => 3*l≤pr w (fun x => fans b z i j x y)
  have hx : 0<pushCost l K:= div_pos hl (bp_pos _)
  apply (le_div_iff₀ (pow_pos hx _)).mpr
  rw [mul_comm]
  by_cases h : 0<pr v Q
  · have het (T : Space (Vec (Fin N))) (h : dim T≤k) :
        pr w (fun x => ¬Disjoint (imageP p x i z) T)≤ l := by
      apply le_trans (any_frame_hit m hL he i z hN T) (le_trans ?_ hg)
      have hr : (dim T:ℝ) ≤ k := by exact_mod_cast h
      gcongr
    obtain ⟨Y,hY,hP⟩ := booming b K k k le_rfl hK z i j w v hw hv hl het Q h (fun _ h => h)
    exact (hP.trans (pr_mono hv.nz fun _ => And.right)).trans
      (strikers b K hK Y hY m hB hf hv.sub j z hN)
  exact (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hx.le _) (not_lt.mp h)).trans (by
    unfold fireBill; exact mul_nonneg (by positivity) (bp_pos _).le)
end HadwigerCounterexample

end

end OAI
