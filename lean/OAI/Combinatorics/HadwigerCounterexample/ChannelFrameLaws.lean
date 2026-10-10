import OAI.Combinatorics.HadwigerCounterexample.SumRankBounds

namespace OAI

/-! # Channel Frame Laws -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Finset Function
open scoped BigOperators

variable {A B : Type} [Fintype A] [Fintype B]

theorem map_pair_law {C D : Type} [Fintype C] [Fintype D]
    (w : Wgt A) (v : Wgt B) (f : A→C) (g : B→D) :
    mapW (pairW w v) (Prod.map f g)=pairW (mapW w f) (mapW v g) := by
  funext x
  unfold mapW pairW
  simp only [Prod.ext_iff]
  exact pairW_pr w v (fun y => f y=x.1) (fun y => g y=x.2)

theorem mapW_nested {C : Type} (w : Wgt A) (f : A→B) (g : B→C) :
    mapW (mapW w f) g=mapW w (g ∘ f) :=
  funext fun _ => mapW_pr _ _ _

omit [Fintype B] in
theorem mapW_repeat {I : Type} [Fintype I] [DecidableEq I]
    (w : I→ Wgt A) (f : I→ A→B) :
    mapW (prodW w) (fun x i => f i (x i))=prodW (fun i => mapW (w i) (f i)) := by
  funext x
  unfold mapW
  simp_rw [funext_iff]
  exact prodW_pr _ (fun i y => f i y=x i)

omit [Fintype B] in
theorem mapW_pr_eq (e : A≃A) (f : A→B) (u : B≃B) (h : ∀ x,f (e x)=u (f x))
    (w : Wgt A) (hw : ∀ x, w (e x)=w x) (x : B) : mapW w f (u x)=mapW w f x := by
  have he := avg_bij e w (fun y => ind (f y=u x))
  simp_rw [hw,h,u.injective.eq_iff] at he
  exact he.symm

private theorem pmax_test {x : A} (p : A → Prop) {w : Wgt A} (hw : SubLaw w)
    (h : ∀ y, p y → w y=w x) {m : ℝ} (hm : 0 < m)
    (hp : m ≤ pr unif p) [Nonempty A] :
    w x ≤ m⁻¹ * unif x := by
  have hh : pr w p=w x*nbr p := by
    simp only [pr,avg,nbr,tot,Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases he : p i
    · rw [h i he]
    rw [ind_zero he,mul_zero,mul_zero]
  have h1 := (pr_le_tot (p:=p) hw.nz).trans hw.total
  rw [hh] at h1
  have hU : 0 < (Fintype.card A : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [pr_unif (A:=A)] at hp
  have hi := (le_div_iff₀ hU).mp hp
  rw [unif_apply]
  field_simp
  nlinarith only [h1,hi,mul_le_mul_of_nonneg_left hi (hw.nz x)]

theorem gram_norm_quarter {I J L : Type} [Fintype I] [Fintype J] [Fintype L]
    [DecidableEq I] [DecidableEq J] [DecidableEq L] (G : Mat I J)
    (h : num I + num J-num L ≤ -1) :
    bp (-num I * num J)/4 ≤ pr unif (gramGood (U:=L) G) := by
  have hn := (gram_norm G (by linarith : num I+num J≤num L)).2
  rw [pair_unif]
  refine le_trans ?_ hn
  have he {x : ℝ} (hx : x ≤ -1) : (1/2 : ℝ)≤ 1-bp x := by
    have ht := bp_le hx
    rw [bp_neg,bp_one] at ht
    linarith only [ht]
  let d := bp (-num I*num J)
  change d/4 ≤ d* _ * _
  have hk : 0 < d := bp_pos _
  have h1 := he (x:= num I-num L) (by
    have hg : 0≤num J := Nat.cast_nonneg _
    linarith)
  calc d/4 = d*(1/2)*(1/2) := by ring
       _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left h1 hk.le) (he h) (by norm_num)
         (mul_nonneg hk.le (le_trans (by norm_num) h1))

variable {I J U : Type} [Fintype I] [Fintype J] [Fintype U]
variable [DecidableEq I] [DecidableEq J] [DecidableEq U]

theorem gramObsCap {C : Mat (I⊕J) (I⊕J) → Prop}
    (hc : ∃ x : Mat U (I⊕J) × _, FramesAt C x)
    (T : Mat (I⊕J) J) (ht : Function.Injective T.mulVec)
    (hN : 2*num J-num U≤ -1) :
    let w := unifOn (FramesAt C)
    ∀ x : Mat U J × Mat U J,
      mapW w (observe T T) x ≤ (4*bp (num J*num J))*pairW unif unif x := by
  classical
  let w := unifOn (FramesAt (U:=U) C)
  have hw := unifOn_law hc
  let f := observe T T (U:=U)
  let v := mapW w f
  have hv : IsLaw v := mapW_law hw f
  have hg :
      carried v (fun x : Mat U J × _ => Injective x.1.mulVec ∧ Injective x.2.mulVec) := by
    refine mapW_carried (unifOn_carried _) (fun x hx => ?_)
    exact ⟨inj_comp_mat _ _ hx.2.1 ht,inj_comp_mat _ _ hx.2.2 ht⟩
  dsimp only
  intro x
  rw [← pair_unif]
  by_cases h : v x≠0
  · let G := (x.1ᵀ*x.2 : Mat J J)
    have hx : gramGood G x := ⟨rfl,Classical.byContradiction fun he => h (hg x he)⟩
    let m := bp (-num J*num J)/4
    have he (y : Mat U J × Mat U J) (hy : gramGood G y) : v y=v x := by
      obtain ⟨L,hL⟩ := move_exists G x y hx hy
      let e := L.perm (I⊕J) (I⊕J)
      have hl (y) : f (e y)=(L.perm J J) (f y) :=
        Prod.ext (Matrix.mul_assoc ..) (Matrix.mul_assoc ..)
      have hp y : w (e y)=w y := by
        unfold w; rw [unifOn_val, unifOn_val]
        congr 2
        exact propext (L.invar C y).symm
      exact hL ▸ mapW_pr_eq e f (L.perm J J) hl w hp x
    have hi := pmax_test (gramGood (U:=U) G) hv.sub he (m:=m)
      (div_pos (bp_pos _) (by norm_num)) (gram_norm_quarter G (by linarith only [hN]))
    apply hi.trans
    unfold m; rw [neg_mul,bp_neg]; field_simp
    exact le_rfl
  · change v x ≤ _
    rw [not_ne_iff.mp h]
    exact mul_nonneg (mul_nonneg (by norm_num) (bp_pos _).le) (unif_subLaw.nz _)

variable {p : Shape} {n N : ℕ}
abbrev HMat (p : Shape) (N : ℕ) := Mat (Fin N) (Chan p)
abbrev HFrame (p : Shape) (N : ℕ) := HMat p N × HMat p N
abbrev HCube (p : Shape) (N : ℕ) := Comp p.g → HFrame p N

def hchan (p : Shape) {n N} (x : Oframe p n N) : HFrame p N :=
  (channel x.1,channel x.2)
def hcube (p : Shape) {n N} (x : Orient p n N) : HCube p N := fun z => hchan p (x z)
def lawH (p : Shape) (N : ℕ) : Wgt (HCube p N) :=
  prodW (fun (_ : Comp p.g) => pairW unif unif)

def intoChan (p : Shape) (n) : Mat (Full p n) (Chan p) := embedMat (.inr ·)

theorem intoChan_inj : Injective (intoChan p n).mulVec :=
  embedMat_inj Sum.inr_injective
theorem intoChan_val (p : Shape) {n N} (x : Mat (Fin N) (Full p n)) :
    x * intoChan p n=channel x := by rw [intoChan,mul_embedMat]; rfl
theorem hchan_val (p : Shape) {n N} :
    hchan p (n:=n) (N:=N) = observe (intoChan p n) (intoChan p n) := by
  funext x
  exact Prod.ext (intoChan_val ..).symm (intoChan_val ..).symm

def chanPrice (p : Shape) : ℝ :=
  (4*bp ((p.h:ℝ)*p.h))^(Fintype.card (Comp p.g))

theorem hchan_cap (m : Mixer p n) (hN : 2*num (Full p n)-N≤ -1) :
    let w := unifOn (FramesAt (U:=Fin N) (gramCond m))
    ∀ x : HFrame p N,mapW w (hchan p) x≤(4*bp ((p.h:ℝ)*p.h))*pairW unif unif x := by
  classical
  have he : 2*num (Full p n)-num (Fin N)≤ -1 := by simpa [num] using hN
  have hh : ∃ x : Oframe p n N, FramesAt (gramCond m) x :=
    framesAt_exists (gramCond_exists m) (by linarith only [he])
  rw [hchan_val]
  have hr : num (Chan p) ≤ num (Full p n) := by
    have hf : Fintype.card (Row p n) + Fintype.card (Chan p)=Fintype.card (Full p n) :=
      (Fintype.card_sum ..).symm
    exact_mod_cast (show Fintype.card (Chan p)≤Fintype.card (Full p n) by omega)
  have hk := gramObsCap hh (intoChan p n) intoChan_inj (by linarith only [he,hr])
  rw [show num (Chan p)=(p.h:ℝ) from (by simp [num,Chan])] at hk
  exact hk

theorem hcube_cap (m : Mixer p n) (hN : 2*num (Full p n)-N≤ -1)
    (x : HCube p N) : mapW (raw m N) (hcube p) x ≤ chanPrice p*lawH p N x := by
  let w := unifOn (FramesAt (U:=Fin N) (gramCond m))
  have hh i := hchan_cap m hN (x i)
  change mapW (prodW (fun (_ : Comp p.g) => w)) _ x ≤ _
  unfold hcube
  rw [mapW_repeat (w:=fun (_:Comp p.g) => w) (f:=fun i => hchan p (n:=n) (N:=N))]
  refine le_trans (Finset.prod_le_prod₀ ?_ fun i _ => hh i) ?_
  · intro i _
    exact pr_nonneg (unifOn_sub _).nz
  rw [Finset.prod_mul_distrib]
  simp [chanPrice,lawH,prodW]

end HadwigerCounterexample

end

end OAI
