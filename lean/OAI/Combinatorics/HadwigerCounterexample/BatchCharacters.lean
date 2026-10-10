import OAI.Combinatorics.HadwigerCounterexample.CrossPatternCounting

namespace OAI

/-! # Batch Characters -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Module LinearMap Function Finset
variable {I J A B : Type} [Fintype I] [Fintype J] [Fintype A] [Fintype B]
variable [DecidableEq I] [DecidableEq J] [DecidableEq A] [DecidableEq B]
variable {n N t : ℕ}

def led (i : I) (x : Rack (I×J) N) := sectionR (fun j => (i,j)) x
def relay (I J : Type) [Fintype I] [Fintype J] (N) :
    Rack (I×J) N ≃ (I → Rack J N) where
  toFun x i := led i x
  invFun x := (Matrix.of (fun i j => (x j.1).1 i j.2), Matrix.of (fun i j => (x j.1).2 i j.2))
  left_inv x := by apply Prod.ext <;> rfl
  right_inv x := funext fun _ => Prod.ext rfl rfl

theorem led_uniform (F : Wgt (I→Rack J N)) :
    avg (unif : Wgt (Rack (I×J) N)) (fun x => F (fun i => led i x))=
    avg (draws I unif) F := by
  change avg unif (fun x => F (relay I J N x))=_
  rw [← mapW_avg,unif_equiv,← draws_unif]

theorem led_piece (T : Finset I) (p : I→Rack J N→Prop) :
    avg unif (fun x => ∏ i∈T,ind (p i (led i x))) =
      ∏ i∈T,pr unif (p i) := by
  classical
  let F (i : I) (z) := if i∈T then ind (p i z) else 1
  let H : Wgt (I→ Rack J N) := prodW F
  have he x : (∏ i∈T,ind (p i (led i x))) = H (fun i => led i x) := by
    unfold H F prodW
    rw [← Finset.prod_filter]; simp
  have hf i : avg unif (F i) = if i∈T then pr unif (p i) else 1 := by
    by_cases hh : i∈T <;> simp [F,pr,hh,unif_law.avg_const]
  simp_rw [he]; rw [led_uniform]
  unfold H draws
  rw [prodW_avg]; simp_rw [hf]; rw [← Finset.prod_filter]; simp

def heard (T : A → I×J) := Finset.univ.image (Prod.fst ∘ T)

omit [Fintype I] [Fintype J] [DecidableEq A] in
theorem heard_fresh {T : A→I × J} {i : I} (B : PlusRack A N) (h : i∉heard T) (j : J) (k) :
    upliftR T B k (i,j)=0 := by
  classical
  unfold upliftR
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun x _ => ?_
  have he : (i,j)≠T x := fun e => h (mem_image.mpr
    ⟨x,mem_univ _, (congrArg Prod.fst e).symm⟩)
  simp [embedMat,he]

omit [Fintype I] [Fintype J] [DecidableEq A] in
private theorem led_off_r (x : Rack (I×J) N) {T : A→I×J} {i : I} (B : PlusRack A N)
    (h : i∉heard T) :
    led i (x+(0,upliftR T B)) = led i x := by
  apply Prod.ext
  · ext; simp [led,sectionR]
  ext
  simp only [led,sectionR,Prod.snd_add,Matrix.add_apply,Matrix.submatrix_apply,
    heard_fresh B h,add_zero]

omit [Fintype I] [Fintype J] [DecidableEq A] in
private theorem led_off_l (x : Rack (I×J) N) {T : A→I×J} {i : I} (B : PlusRack A N)
    (h : i∉heard T) :
    led i (x+(upliftR T B,0)) = led i x := by
  apply Prod.ext
  · ext
    simp only [led,sectionR,Prod.fst_add,Matrix.add_apply,Matrix.submatrix_apply,
      heard_fresh B h,add_zero]
  ext; simp [led,sectionR]

def phot (P : I→Rack J N→Prop) (x : Rack (I×J) N) :=
  ∏ i:I,ind (P i (led i x))

set_option maxHeartbeats 800000 in
theorem light_bound (M : Avenue I J) (P : I→Rack J N→Prop) (u : ℝ) (hu : 0 ≤ u)
    (hp : ∀ i,bp (-u) ≤ pr unif (P i)) :
    |avg unif (fun x => phasedBy M x*phot P x)| ≤
      bp ((-(N:ℝ)/2+2*u)*(peak M:ℝ)) * ∏ i,pr unif (P i) := by
  classical
  obtain ⟨T,U,hTU,hA⟩ := real_peak M
  let t := peak M
  let L := heard T
  let R := heard U
  let D := L∪R
  let S := Finset.univ \ D
  have hd : Disjoint L R := by
    refine Finset.disjoint_left.mpr ?_
    intro x hx hy
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j,_,he⟩ := Finset.mem_image.mp hy
    exact hTU i j he.symm
  let f (Z : Finset I) (x : Rack (I×J) N) := ∏ i∈Z,ind (P i (led i x))
  have hs (V : Finset I) x : |f V x|=f V x := abs_of_nonneg (Finset.prod_nonneg (fun i _ =>
    ind_nonneg _))
  have heq (V : Finset I) x : |f V x|≤1 := (hs V x).trans_le
    ((Finset.prod_le_prod₀ (fun _ _ => ind_nonneg _) (fun _ _ => ind_le_one _)).trans_eq (by simp))
  have h1 :
      (∏ i,pr unif (P i))=(∏ i∈D,pr unif (P i))*(∏ i∈S,pr unif (P i)) := by
    rw [←Finset.prod_union (show Disjoint D S from disjoint_sdiff),
      Finset.union_sdiff_of_subset (Finset.subset_univ D)]
  have hf x : phot P x=f L x*f R x*f S x := by
    unfold phot f
    rw [←Finset.prod_union hd,←Finset.prod_union (show Disjoint D S from disjoint_sdiff),
      Finset.union_sdiff_of_subset (Finset.subset_univ D)]
  have hl :
      |avg unif (fun x => phasedBy M x*phot P x)| ≤ bp (-(N:ℝ)*t/2) * avg unif (fun x => |f S x|) := by
    have he x : phasedBy M x*phot P x=phasedBy M x*f L x*f R x*f S x := by rw [hf]; ring
    simp_rw [he]
    rw [←show (M.submatrix T U).rank=t from
      (mrk_inj.mp hA).trans (Fintype.card_fin _)]

    refine layerLeak M (f L) (f R) (f S) T U (heq _) (heq _) (fun x y => ?_)
      (fun x y => ?_) (fun x y z => ?_)
    · refine Finset.prod_congr rfl fun i hi => ?_
      rw [led_off_r x y (fun h => Finset.disjoint_left.mp hd hi h)]
    · refine Finset.prod_congr rfl fun i hi => ?_
      rw [led_off_l x y (fun h => Finset.disjoint_left.mp hd h hi)]
    · refine Finset.prod_congr rfl fun i hi => ?_
      have hr := (Finset.mem_sdiff.mp hi).2
      rw [show x+(upliftR T y,upliftR U z)=x+(0,upliftR U z)+(upliftR T y,0) from
        by rw [add_assoc]; apply congrArg; apply Prod.ext <;> simp,
        led_off_l _ y (fun h => hr (mem_union_left _ h)),
        led_off_r _ z (fun h => hr (mem_union_right _ h))]
  apply hl.trans
  simp_rw [hs]
  rw [show avg unif (fun x => f S x)= _ from led_piece S P,h1,← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun _ _ => pr_nonneg unif_law.nz)
  have hc : D.card ≤ 2*t := by
    apply le_trans (Finset.card_union_le ..)
    have hi (T : Fin t→ I × J) : (heard T).card≤t :=
      Finset.card_image_le.trans_eq (by simp)
    rw [two_mul]; exact add_le_add (hi T) (hi U)
  have hQ : bp (-u*(2*(t:ℝ))) ≤ ∏ i∈D,pr unif (P i) := by
    refine le_trans ?_ (Finset.prod_le_prod₀ (fun i _ => (bp_pos _).le) fun i _ => hp i)
    rw [Finset.prod_const,←bp_mul_nat]
    apply bp_le
    apply mul_le_mul_of_nonpos_left
    · exact_mod_cast hc
    exact neg_nonpos.mpr hu
  calc bp _
    _ = bp ((-(N:ℝ)/2+2*u)*(peak M:ℝ)) * bp (-u*(2*t)) := by rw [←bp_add]; congr 1; unfold t; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hQ (bp_pos _).le
end HadwigerCounterexample

end

end OAI
