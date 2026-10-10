import OAI.Combinatorics.HadwigerCounterexample.OffsetEnergy

namespace OAI

/-! # Probe Point Masses -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Module Submodule LinearMap Finset Function
variable {p : Shape} {n N : ℕ} {q t : Place p→ℕ}

def initCap (p : Shape) {n} (N : ℕ) (m : Mixer p n) (ε : ℝ) :=
  ∀ a : Pin p n N,pr (pairW (raw m N) (raw m N)) a.agree ≤ fee N ε (planRank a.sp)

def bySide (p : Shape) {n N} (w : Wgt (UnitType p n N))
    (m : Mixer p n) (c : ℝ) :=
  ∀ i x, mapW w (fun y => onSide y i) x ≤ c*raw m N x

theorem side_same {A : Type} [Fintype A] (i : Bool) (w : Wgt A) (hw : IsLaw w)
    (v : Wgt (A × A)) {H : ℝ}
    (h : ∀ x,mapW v (fun x => onSide x i) x≤H * w x)
    (P : A×A→Prop) (he : ∀ x y,onSide x i=onSide y i → (P x↔P y)) :
    pr v P ≤ H * pr (pairW w w) P := by
  classical
  let Q := fun x => P (x,x)
  have hq : P=fun x => Q (onSide x i) := by
    funext x; exact propext (he x _ (by cases i <;> rfl))
  rw [hq,←mapW_pr v (fun x => onSide x i) Q]
  refine (pr_cap h Q).trans_eq ?_
  have hh : pr (pairW w w) (fun x => Q (onSide x i)) = pr w Q := by
    cases i
    · change pr (pairW w w) (fun x => Q x.2)=pr w Q
      simpa only [true_and, pr_true,hw.total,one_mul] using pairW_pr w w (fun _ => True) Q
    change pr (pairW w w) (fun x => Q x.1)=pr w Q
    simpa only [and_true,pr_true,hw.total,mul_one] using pairW_pr w w Q (fun _ => True)
  rw [hh]

def basisFrom (p : Shape) {n N} (x : UnitType p n N) (i : Bool)
    {q : Place p→ℕ} (Z : DTuple (p:=p) q N) :=
  ∀ z,Injective (Z z).mulVec ∧ colSp (Z z) ≤ imageP p x i (flipZ p z)

def ctot (p : Shape) (r : Place p→ℕ) := ∑ i,r i
abbrev Among (p : Shape) (n : ℕ) (q : Place p→ℕ) :=
  ∀ z, Mat (Row p n) (Fin (q z))
def csignal (p : Shape) {n} (i : Bool) {q : Place p → ℕ}
    (S : Among p n q) : WTuple (p:=p) q n :=
  fun z => IP p n i * S z

def poke (p : Shape) {n N} {q t : Place p → ℕ}
    (B : WTuple (p:=p) q n) (C : WTuple (p:=p) t n)
    (Z : DTuple (p:=p) q N) (A : DTuple (p:=p) t N)
    (x : UnitType p n N) :=
  ∀ z, images x (flipZ p z) * B z=Z z ∧ images x z * C z = A z

set_option maxHeartbeats 600000 in
theorem poke_cap (B : WTuple (p:=p) q n) (C : WTuple (p:=p) t n)
    (Z : DTuple (p:=p) q N) (A : DTuple (p:=p) t N)
    (m : Mixer p n) {ε : ℝ} (he : initCap p N m ε)
    (hB : ∀ z, Injective (B z).mulVec)
    (hC : ∀ z, Injective (C z).mulVec)
    (hD : ∀ z, Disjoint (colSp (B z)) (colSp (C (flipZ p z)))) :
    pr (pairW (raw m N) (raw m N)) (poke p B C Z A) ≤
      fee N ε (ctot p q+ctot p t) := by
  classical
  let μ := raw m N
  let w := pairW μ μ
  have hw (x) : 0 ≤ w x := mul_nonneg (raw_nonneg m _) (raw_nonneg m _)
  by_cases h : 0 < pr w (poke p B C Z A)
  · obtain ⟨x,hx,_⟩ := exists_of_pr_pos hw h
    let U : Plan p n := fun z => colSp (B (flipZ p z)) ⊔ colSp (C z)
    let V := Pin.make U x
    refine (pr_mono hw (q:=V.agree) fun y hy => ?_).trans ((he V).trans ?_)
    · intro z v hv
      change images y z *ᵥ v=images x z *ᵥ v
      obtain ⟨l,⟨t,rfl⟩,r,⟨u,rfl⟩,rfl⟩ := Submodule.mem_sup.mp
        (show v∈colSp (B (flipZ p z))⊔colSp (C z) from hv)
      have h1 := (hx (flipZ p z)).1.trans (hy (flipZ p z)).1.symm
      simp only [flipZ_flip] at h1
      simp only [mulVecLin_apply, Matrix.mulVec_add, Matrix.mulVec_mulVec,h1,
        (hx z).2,(hy z).2]
    · have hF (z) : dim (U z)=q (flipZ p z)+t z := by
        have hi := Submodule.finrank_sup_add_finrank_inf_eq (colSp (B (flipZ p z))) (colSp (C z))
        have hy := hD (flipZ p z)
        rw [flipZ_flip] at hy
        rw [hy.eq_bot,finrank_bot,add_zero] at hi
        exact hi.trans (congrArg₂ (·+·) ((mrk_inj.mp (hB (flipZ p z))).trans (Fintype.card_fin _))
          ((mrk_inj.mp (hC z)).trans (Fintype.card_fin _)))
      have ht : planRank V.sp=ctot p q+ctot p t := by
        unfold planRank ctot
        change ∑ z,dim (U z)= _
        simp_rw [hF,Finset.sum_add_distrib]
        exact congrArg (fun x => x + ∑ z,t z) (Equiv.sum_comp (flipEquiv p) q)
      rw [ht]
  exact (not_lt.mp h).trans (bp_pos _).le

def heatRate (p : Shape) (n N : ℕ) (ε : ℝ) (x y : ℕ) :=
  bp (num (Row p n)* x+ 2*p.h*y)*fee N ε (x+y)

instance amongFintype (p : Shape) (n : ℕ) (r : Place p→ℕ) : Fintype (Among p n r) := by
  classical exact inferInstanceAs (Fintype (Among p n r))

private theorem format_size :
    num (Among p n q × (Bool → DTuple (p:=p) t p.h)) =
      bp (num (Row p n)*ctot p q+2*p.h*ctot p t) := by
  classical
  unfold num
  rw [card_space,dim,Module.finrank_prod, Nat.cast_add]
  have he : finrank F (Among p n q)=Fintype.card (Row p n)*ctot p q := by
    unfold Among
    rw [finrank_pi_fintype]
    unfold ctot; rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => (dim_mat ..).trans (by rw [Fintype.card_fin])
  have hf :
      finrank F (Bool → DTuple (p:=p) t p.h)=2*p.h*ctot p t := by
    rw [finrank_pi_fintype,Fintype.sum_bool]
    change dim (DTuple ..)+dim (DTuple ..)=_
    rw [tuple_dim]
    unfold ctot; ring
  rw [he,hf]
  push_cast; rfl

set_option maxHeartbeats 800000 in
theorem heat_rate (i : Bool) (S : Party) (hi : S i=1)
    (A : DTuple (p:=p) t N)
    (B : DTuple (p:=p) t N) (Z : DTuple (p:=p) q N)
    (m : Mixer p n) {ε : ℝ} (he : initCap p N m ε) :
    pr (pairW (raw m N) (raw m N)) (fun x =>
      basisFrom p x i Z ∧ glimpse p x i A ∧ thermal p x S A=B)
      ≤ heatRate p n N ε (ctot p q) (ctot p t) := by
  classical
  let M := Among p n q × (Bool → DTuple (p:=p) t p.h)
  let P (v : M) (x : UnitType p n N) :=
    let X := csignal p i v.1
    let Y := hfused p n _ v.2
    (∀ z, Injective (X z).mulVec ∧ Injective (Y z).mulVec) ∧ poke p X Y Z B x
  let w := pairW (raw m N) (raw m N)
  have hw x : 0 ≤ w x := mul_nonneg (raw_nonneg m _) (raw_nonneg m _)
  have h : ∀ x : UnitType p n N,basisFrom p x i Z ∧ glimpse p x i A ∧ thermal p x S A=B →
      ∃ v, P v x := by
    rintro x ⟨hF,hT,hU⟩
    choose A' hA using fun z => pull_cols (fpAt p (onSide x i) (flipZ p z)) (Z z) (hF z).2
    let C := sparks p x S A
    let Y := hfused p n _ C
    let X := csignal p i A'
    have hh z : images x (flipZ p z)*X z=Z z := by
      unfold X csignal
      rw [← Matrix.mul_assoc, images_ip]
      exact hA z
    refine ⟨(A',C),fun z => ⟨?_,hotfused x S A i hi hT z⟩, fun z => ?_⟩
    · have hg := (hF z).1
      rw [← hh z] at hg
      intro p' q he
      apply hg
      change X z *ᵥ p' = X z*ᵥ q at he
      rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,he]
    exact ⟨hh z,(fuse_val x S A z).trans (congr_fun hU z)⟩
  have hg (v : M) :
      pr w (P v) ≤ fee N ε (ctot p q+ctot p t) := by
    let X := csignal p i v.1
    let Y := hfused p n _ v.2
    by_cases hh : ∀ z, Injective (X z).mulVec ∧ Injective (Y z).mulVec
    · refine (pr_mono hw (p:=P v) (q:=poke p X Y Z B) fun x h => h.2).trans
        (poke_cap X Y _ _ m he (fun z => (hh z).1) (fun z => (hh z).2) ?_)
      intro z
      exact (channels_disjoint (p:=p) (n:=n)).mono
        ((col_follow ..).trans (ip_le_primal i)) (fused_support v.2 _)
    have heq : P v=(fun _ => False) := funext fun x => propext (iff_false_intro (fun h => hh h.1))
    rw [heq,pr_false]; exact (bp_pos _).le
  refine ((pr_mono hw h).trans (pr_exists_le hw P)).trans ?_
  refine (Finset.sum_le_sum fun i _ => hg i).trans_eq ?_
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  change num (Among p n q × _) *_= _
  rw [format_size]; rfl

theorem heat_one (i : Bool)
    (A : DTuple (p:=p) t N) (B : DTuple (p:=p) t N)
    (Z : DTuple (p:=p) q N)
    {w : Wgt (UnitType p n N)} {H : ℝ} (hH : 0 ≤ H)
    (m : Mixer p n) {ε : ℝ} (hm : IsLaw (raw m N)) (he : initCap p N m ε)
    (hw : bySide p w m H) :
    pr w (fun x => basisFrom p x i Z ∧ glimpse p x i A ∧ thermal p x (unary i) A=B) ≤
      H*heatRate p n N ε (ctot p q) (ctot p t) := by
  refine (side_same i _ hm w (hw i) _ ?_).trans
    (mul_le_mul_of_nonneg_left (heat_rate i (unary i) (by simp [unary]) A B Z m he) hH)
  intro x y h
  unfold basisFrom glimpse thermal imageP
  simp_rw [heat_unary,h]

theorem heat_none (i : Bool) (Z : DTuple (p:=p) q N)
    {w : Wgt (UnitType p n N)} {H : ℝ} (hH : 0 ≤ H)
    (m : Mixer p n) {ε : ℝ} (hm : IsLaw (raw m N)) (he : initCap p N m ε)
    (hw : bySide p w m H) :
    pr w (fun x => basisFrom p x i Z) ≤ H*heatRate p n N ε (ctot p q) 0 := by
  classical
  let t : Place p→ℕ := fun _ => 0
  let B : DTuple (p:=p) t N := 0
  have hh := heat_one i B B Z hH m hm he hw
  have h1 (x : UnitType p n N) : glimpse p x i B := fun z v v' h => Subsingleton.elim v v'
  have h2 (x : UnitType p n N) : thermal p x (unary i) B=B := Subsingleton.elim _ _
  simp_rw [h1,h2,and_true] at hh
  simpa only [ctot,t,Finset.sum_const_zero] using hh

end HadwigerCounterexample

end

end OAI
