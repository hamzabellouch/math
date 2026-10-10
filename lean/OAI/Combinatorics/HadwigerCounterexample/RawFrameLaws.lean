import OAI.Combinatorics.HadwigerCounterexample.AffineFrames
import OAI.Combinatorics.HadwigerCounterexample.MixedImageBounds

namespace OAI

/-! # Raw Frame Laws -/

noncomputable section
namespace HadwigerCounterexample
open Matrix
open scoped BigOperators

variable {p : Shape} {n N : ℕ}

instance rowDecidableEq (p : Shape) (n : ℕ) : DecidableEq (Row p n) := inferInstance
instance fullDecidableEq (p : Shape) (n : ℕ) : DecidableEq (Full p n) := inferInstance
instance fullFintype (p : Shape) (n : ℕ) : Fintype (Full p n) := inferInstance
instance oframeFintype (p : Shape) (n N : ℕ) : Fintype (Oframe p n N) := inferInstance
instance orientFintype (p : Shape) (n N : ℕ) : Fintype (Orient p n N) := inferInstance

def gramCond (m : Mixer p n) (G : Mat (Full p n) (Full p n)) : Prop :=
  G.toBlocks₁₁ = selfM p n m.mixM ∧ G.toBlocks₂₁ = 0 ∧ G.toBlocks₁₂ = 0

theorem gramCond_exists (m : Mixer p n) : ∃ G, gramCond m G := by
  refine ⟨fromBlocks (selfM p n m.mixM) 0 0 0,?_,?_,?_⟩ <;> rfl

theorem valid_iff (m : Mixer p n) (X : Oframe p n N) :
    valid (selfM p n m.mixM) X ↔ FramesAt (gramCond m) X := by
  have he : (X.1ᵀ*X.2).toBlocks₁₁ = (primary X.1)ᵀ * primary X.2 := by ext; rfl
  have hf : (X.1ᵀ*X.2).toBlocks₂₁ = (channel X.1)ᵀ * primary X.2 := by ext; rfl
  have hg : (X.1ᵀ*X.2).toBlocks₁₂ = (primary X.1)ᵀ * channel X.2 := by ext; rfl
  unfold valid FramesAt gramCond
  rw [he,hf,hg]; tauto

def raw (m : Mixer p n) (N : ℕ) : Wgt (Orient p n N) :=
  prodW (fun (_ : Comp p.g) => unifOn (FramesAt (U := Fin N) (gramCond m)))

theorem raw_law (m : Mixer p n) (hN : 2*num (Full p n)<N) : IsLaw (raw m N) :=
  prodW_law (fun _ => unifOn_law (framesAt_exists (gramCond_exists m)
    (show num (Full p n) + num (Full p n) < num (Fin N) by
      rw [← two_mul]; simpa [num] using hN)))

theorem raw_nonneg (m : Mixer p n) (X : Orient p n N) : 0 ≤ raw m N X :=
  prodW_nonneg (fun _ _ => (unifOn_sub _).nz _) _

theorem raw_carried (m : Mixer p n) (N : ℕ) : carried (raw m N) (frameLaw m) := by
  intro X h
  unfold frameLaw at h
  push Not at h
  obtain ⟨e,he⟩ := h
  unfold raw prodW
  apply Finset.prod_eq_zero (Finset.mem_univ e)
  exact unifOn_carried _ _ ((valid_iff _ _).not.mp he)

abbrev UnitType (p : Shape) (n N : ℕ) := Orient p n N × Orient p n N
abbrev Place (p : Shape) := Comp p.g × Bool
abbrev JointIdx (p : Shape) (n : ℕ) := Full p n ⊕ Full p n

def takeSign (w : Oframe p n N) (b : Bool) := if b then w.1 else w.2

def images (x : UnitType p n N) (z : Place p) : Mat (Fin N) (JointIdx p n) :=
  fromCols (takeSign (x.1 z.1) z.2) (takeSign (x.2 z.1) z.2)

abbrev Dir (p : Shape) (n : ℕ) := Vec (JointIdx p n)
abbrev Plan (p : Shape) (n : ℕ) := Place p → Submodule F (Dir p n)
def planRank (s : Plan p n) := ∑ i, dim (s i)

/-- Pin data: stored subspaces of directions with assigned images. We store a
full linear map for convenience; only its restriction to the pin directions
at each place is used. Counts charge only for the restrictions. -/
structure Pin (p : Shape) (n N : ℕ) where
  sp : Plan p n
  target : Place p → Mat (Fin N) (JointIdx p n)

def Pin.agree (a : Pin p n N) (x : UnitType p n N) :=
  ∀ i, ∀ v ∈ a.sp i, images x i *ᵥ v = a.target i *ᵥ v

theorem Pin.agree_pack {a : Pin p n N} {x : UnitType p n N} :
    a.agree x ↔ ∀ i : Place p, images x i * pack (a.sp i) = a.target i * pack (a.sp i) := by
  have heq {I J L : Type} [Fintype I] [Fintype J] [Fintype L] (P Q : Mat I J) (M : Mat J L) :
      (∀ v ∈ colSp M, P *ᵥ v = Q *ᵥ v) ↔ P*M=Q*M := by
    constructor
    · intro h
      apply coe_mv_inj
      exact LinearMap.ext fun v => by
        change (P*M) *ᵥ v=(Q*M) *ᵥ v
        rw [← mulVec_mulVec,← mulVec_mulVec]
        exact h _ ⟨v,rfl⟩
    · rintro h x ⟨v,rfl⟩
      change P *ᵥ (M *ᵥ v) = Q *ᵥ (M *ᵥ v)
      rw [mulVec_mulVec,mulVec_mulVec,h]
  unfold Pin.agree
  apply forall_congr'; intro i
  have hh := heq (images x i) (a.target i) (pack (a.sp i))
  rw [colSp_pack] at hh
  exact hh

theorem bp_sum {A : Type*} (s : Finset A) (f : A → ℝ) :
    bp (∑ i ∈ s, f i) = ∏ i ∈ s, bp (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha hi => rw [Finset.sum_insert ha, Finset.prod_insert ha,bp_add,hi]

/-- Image cap under two independent raw orientations. Uniform over all
simultaneous exact-image specifications. -/
theorem reference_cap (m : Mixer p n) (a : Pin p n N) {δ : ℝ} (hd : 0 < δ)
    (hu : 2*num (Full p n) - N ≤ -1)
    (hδ : 2*num (Full p n) ≤ δ/2 * N)
    (hA : 4*num (Comp p.g) ≤ δ/2 * N) :
    pr (pairW (raw m N) (raw m N)) a.agree ≤ bp (-(1-δ)*(planRank a.sp)*N) := by
  let s := a.sp
  let μ := raw m N
  have hn : 2*num (Full p n)<N := by linarith only [hu]
  have hh := raw_law m hn
  by_cases he : planRank s = 0
  · change _ ≤ bp (_ * (planRank s) * _)
    rw [he]
    simp only [Nat.cast_zero,mul_zero,zero_mul,bp_zero]
    exact le_trans (pr_le_tot (pairW_law hh hh).nz) (pairW_law hh hh).total.le
  let g (e : Comp p.g) := unifOn (FramesAt (U:=Fin N) (gramCond m))
  let D (e : Place p) := pack (s e)
  let rankval (e : Place p) := (dim (s e) : ℝ)
  let f (e : Comp p.g) (w : Oframe p n N × Oframe p n N) :=
    mixImage (D (e,true)) (w.1.1,w.2.1) = a.target (e,true) * D (e,true) ∧
    mixImage (D (e,false)) (w.1.2,w.2.2) = a.target (e,false) * D (e,false)
  have hf : pr (pairW μ μ) a.agree = ∏ e, pr (pairW (g e) (g e)) (f e) := by
    have hfun : a.agree = (fun x => ∀ e, f e (x.1 e,x.2 e)) := by
      funext x; apply propext
      rw [Pin.agree_pack]
      constructor
      · intro hi e
        exact ⟨hi (e,true),hi (e,false)⟩
      · rintro h ⟨e,b⟩; cases b
        · exact (h e).2
        · exact (h e).1
    rw [hfun]
    exact prodW_pair_pr g g f
  let y := fun e : Comp p.g => 4 - (1-δ/2) * (rankval (e,true)+rankval (e,false))*N
  have hb (e) : pr (pairW (g e) (g e)) (f e) ≤ bp (y e) := by
    have h1 := comp_image_cap (gramCond_exists m)
      (show 2*num (Full p n)-num (Fin N) ≤ -1 by simpa [num] using hu)
      _ _ (pack_inj (s (e,true))) (pack_inj (s (e,false))) (a.target (e,true)*D (e,true))
      (a.target (e,false)*D (e,false))
    have hnum (n : ℕ) : num (Fin n)=(n:ℝ) := by simp [num]
    change pr _ _ ≤ _
    apply le_trans h1
    rw [show (16:ℝ)=bp 4 by
      have hh := bp_nat 4; norm_num at hh ⊢; linarith,← bp_add,hnum,hnum,hnum]
    apply bp_le
    let rp := rankval (e,true)
    let rm := rankval (e,false)
    change 4+(-((N:ℝ))*rp-(_-2*num (Full p n))*rm) ≤ 4 - _ * (rp+rm)*_
    have hp := mul_nonneg (show 0 ≤ rp from Nat.cast_nonneg _) (mul_nonneg hd.le
      (show (0:ℝ) ≤ N from Nat.cast_nonneg _))
    have hg := mul_le_mul_of_nonneg_right hδ (show 0 ≤ rm from Nat.cast_nonneg _)
    linarith only [hp,hg]
  have hg : pr (pairW μ μ) a.agree ≤ bp (∑ i, y i) := by
    rw [hf,bp_sum]
    apply Finset.prod_le_prod₀ _ fun i _ => hb i
    exact fun i _ => pr_nonneg
      (subLaw_pair (unifOn_sub _) (unifOn_sub _)).nz
  apply hg.trans
  apply bp_le
  have ht : (planRank s : ℝ) = ∑ i : Comp p.g, (rankval (i,true) + rankval (i,false)) := by
    rw [planRank,Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, Nat.cast_sum,Nat.cast_add,rankval]
  have h1 : ∑ i, y i = 4*num (Comp p.g) - (1-δ/2)*(planRank s)*N := by
    dsimp only [y]
    rw [Finset.sum_sub_distrib,← Finset.sum_mul, ← Finset.mul_sum, ← ht]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,num]
    ring
  have hk : 1 ≤ (planRank s : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr he
  rw [h1]
  change _ ≤ -(1-δ)*(planRank s)*N
  have he := mul_le_mul_of_nonneg_right hk
    (mul_nonneg hd.le (show (0:ℝ) ≤ N from Nat.cast_nonneg _))
  linarith only [hA,he]

end HadwigerCounterexample

end

end OAI
