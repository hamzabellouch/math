import OAI.Combinatorics.ThinTrees.CompactPacking

namespace OAI

universe uE uE2 uE3 uE4

section
open scoped Classical
open Matrix

namespace StrongThinTree.Truncation
noncomputable section
open Finset
open scoped Classical
variable {E : Type uE} [DecidableEq E]

omit [DecidableEq E] in

lemma sum_sq_le_card_mul_sum_sq (S : Finset E) (a : E → ℝ) :
    (∑e ∈ S, a e)^2 ≤ (S.card : ℝ)*(∑e ∈ S, (a e)^2) := by
  simpa using Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1:ℝ)) a

lemma two_truncations (S : Finset E) (a d : E → ℝ) {α : ℝ}
    (hα : 0 < α) (_hα1 : α ≤ 1) (hS : S.Nonempty)
    (ha : ∀e ∈ S, 0 ≤ a e) (hsq : ∀e ∈ S, (a e)^2 ≤ d e)
    (hpos : 0 < ∑e ∈ S, a e)
    (hbad : α*(S.card : ℝ)*(∑e ∈ S, d e) ≤ (∑e ∈ S, a e)^2) :
    let μ := (∑e ∈ S, a e)/(S.card : ℝ)
    ∃R : Finset E, R ⊆ S ∧
      (∑e ∈ S, a e)/2 ≤ ∑e ∈ R, a e ∧
      ∀e ∈ R, μ^2/16 ≤ (a e)^2 ∧ (a e)^2 ≤ d e ∧ d e ≤ 16*μ^2/α^2 := by
  let M : ℝ := S.card
  let A : ℝ := ∑e ∈ S, a e
  let μ := A/M
  have hM : 0 < M := by dsimp [M]; exact_mod_cast card_pos.mpr hS
  have hA : 0 < A := hpos
  have hμ : 0 < μ := div_pos hA hM
  have hμM : μ*M = A := div_mul_cancel₀ _ hM.ne'
  have hbad' : α*(∑e ∈ S, d e) ≤ M*μ^2 := by
    apply (mul_le_mul_iff_right₀ hM).mp
    change α*M*(∑e ∈ S, d e) ≤ A^2 at hbad
    nlinarith [sq_nonneg (μ*M-A)]
  let L := S.filter (fun e => a e < μ/4)
  let H := S.filter (fun e => 16*μ^2/α^2 < d e)
  let R := S\(L∪H)
  have hd : ∀e ∈ S, 0 ≤ d e := fun e he => (sq_nonneg _).trans (hsq e he)
  have hLsum : (∑e ∈ L, a e) ≤ A/4 := by
    calc
      _ ≤ ∑_e ∈ L, μ/4 := sum_le_sum (fun e he => (mem_filter.mp he).2.le)
      _ = (L.card : ℝ)*μ/4 := by simp; ring
      _ ≤ M*μ/4 := by
        have hh : (L.card : ℝ) ≤ M := by
          change (L.card : ℝ) ≤ (S.card : ℝ)
          exact_mod_cast card_le_card (show L ⊆ S from filter_subset _ _)
        nlinarith
      _ = A/4 := by rw [mul_comm M,hμM]
  have hHmass : (H.card : ℝ)*(16*μ^2/α^2) ≤ ∑e ∈ S, d e := by
    calc
      _ = ∑_e ∈ H, 16*μ^2/α^2 := by simp
      _ ≤ ∑e ∈ H, d e := sum_le_sum (fun e he => (mem_filter.mp he).2.le)
      _ ≤ ∑e ∈ S, d e := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun e he _ => hd e he)
  have hHcard : (H.card : ℝ) ≤ α*M/16 := by
    have hc := mul_le_mul_of_nonneg_left hHmass hα.le
    have hμ2 : 0 < μ^2 := sq_pos_of_pos hμ
    have heq : α*(H.card : ℝ)*(16*μ^2/α^2) = (H.card : ℝ)*16*μ^2/α := by field_simp
    have hh : (H.card : ℝ)*16*μ^2/α ≤ M*μ^2 := by
      calc
        _ = α*((H.card : ℝ)*(16*μ^2/α^2)) := by rw [←mul_assoc,heq]
        _ ≤ α*(∑e ∈ S, d e) := hc
        _ ≤ M*μ^2 := hbad'
    have hh' := (div_le_iff₀ hα).mp hh
    nlinarith
  have hHsq : (∑e ∈ H, a e)^2 ≤ (A/4)^2 := by
    have hcs := sum_sq_le_card_mul_sum_sq H a
    have hs : ∑e ∈ H, (a e)^2 ≤ ∑e ∈ S, d e :=
      (sum_le_sum (fun e he => hsq e (mem_filter.mp he).1)).trans
        (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun e he _ => hd e he))
    have hD0 : 0 ≤ ∑e ∈ S, d e := sum_nonneg hd
    have hh := mul_le_mul_of_nonneg_right hHcard hD0
    have hh' := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg H.card : (0:ℝ) ≤ _)
    have hb := mul_le_mul_of_nonneg_left hbad' hM.le
    nlinarith [sq_nonneg (μ*M-A)]
  have hHsum : (∑e ∈ H, a e) ≤ A/4 := by nlinarith [sum_nonneg (s := H) (fun e he => ha e (mem_filter.mp he).1)]
  have hU : L∪H ⊆ S := union_subset (filter_subset _ _) (filter_subset _ _)
  have hsum : ∑e ∈ S, a e = (∑e ∈ R, a e)+(∑e ∈ L∪H, a e) := (sum_sdiff hU).symm
  have hUH : ∑e ∈ L∪H, a e ≤ (∑e ∈ L, a e)+(∑e ∈ H, a e) := by
    have he := sum_union_inter (s₁ := L) (s₂ := H) (f := a)
    have hi : 0 ≤ ∑e ∈ L∩H, a e := sum_nonneg (fun e he => ha e (hU (mem_union_left _ (mem_inter.mp he).1)))
    linarith
  refine ⟨R,sdiff_subset,?_,?_⟩
  · change A/2 ≤ _
    change A = _ at hsum
    linarith
  · intro e he
    obtain ⟨heS,heU⟩ := mem_sdiff.mp he
    have hle : μ/4 ≤ a e := le_of_not_gt (fun hh => heU (mem_union_left _ (mem_filter.mpr ⟨heS,hh⟩)))
    have hde : d e ≤ 16*μ^2/α^2 := le_of_not_gt (fun hh => heU (mem_union_right _ (mem_filter.mpr ⟨heS,hh⟩)))
    exact ⟨by change μ^2/16 ≤ _; nlinarith [ha e heS],hsq e heS,hde⟩

end
end StrongThinTree.Truncation

namespace StrongThinTree.Truncation
noncomputable section
open Finset
open scoped Classical
variable {E : Type uE2} [DecidableEq E]

def dyadicIndex (L x : ℝ) : ℕ := ⌊Real.logb 2 (x/L)⌋₊

lemma dyadic_interval {L x : ℝ} (hL : 0 < L) (hx : L ≤ x) :
    (2:ℝ)^(dyadicIndex L x : ℝ)*L ≤ x ∧
      x < 2*((2:ℝ)^(dyadicIndex L x : ℝ)*L) := by
  have hratio : 1 ≤ x/L := (le_div_iff₀ hL).mpr (by simpa)
  have hp : 0 < x/L := lt_of_lt_of_le zero_lt_one hratio
  have hg : 0 ≤ Real.logb 2 (x/L) := Real.logb_nonneg (by norm_num) hratio
  constructor
  · exact (le_div_iff₀ hL).mp ((Real.le_logb_iff_rpow_le (by norm_num) hp).mp (Nat.floor_le hg))
  · have hh := (Real.logb_lt_iff_lt_rpow (by norm_num) hp).mp (Nat.lt_floor_add_one (Real.logb 2 (x/L)))
    rw [Real.rpow_add (by norm_num),Real.rpow_one] at hh
    have hh' := (div_lt_iff₀ hL).mp hh
    dsimp [dyadicIndex]
    nlinarith

lemma dyadicIndex_lt {L U x : ℝ} {J : ℕ} (hL : 0 < L) (hx : L ≤ x) (hU : x ≤ U)
    (hJ : Real.logb 2 (U/L) < J) : dyadicIndex L x < J := by
  have hr : 1 ≤ x/L := (le_div_iff₀ hL).mpr (by simpa)
  apply (Nat.floor_lt (Real.logb_nonneg (by norm_num) hr)).mpr
  exact (Real.logb_le_logb_of_le (by norm_num) (lt_of_lt_of_le zero_lt_one hr)
    ((div_le_div_iff_of_pos_right hL).mpr hU)).trans_lt hJ

lemma same_dyadic_ratio {L x y : ℝ} (hL : 0 < L) (hx : L ≤ x) (hy : L ≤ y)
    (heq : dyadicIndex L x = dyadicIndex L y) : x < 2*y := by
  have hh := (dyadic_interval hL hx).2
  rw [heq] at hh
  exact hh.trans_le (mul_le_mul_of_nonneg_left (dyadic_interval hL hy).1 (by norm_num))

omit [DecidableEq E] in

lemma dyadic_pair (R : Finset E) (a b w : E → ℝ) {L U : ℝ} {J : ℕ}
    (hL : 0 < L) (hJ : 0 < J) (hj : Real.logb 2 (U/L) < J)
    (ha : ∀e ∈ R, L ≤ a e ∧ a e ≤ U) (hb : ∀e ∈ R, L ≤ b e ∧ b e ≤ U)
    (hpos : 0 < ∑e ∈ R, w e) :
    ∃B : Finset E, B.Nonempty ∧ B ⊆ R ∧
      (∑e ∈ R, w e)/(J:ℝ)^2 ≤ ∑e ∈ B, w e ∧
      ∀e ∈ B, ∀f ∈ B, a e < 2*a f ∧ b e < 2*b f := by
  let f := fun e => (dyadicIndex L (a e),dyadicIndex L (b e))
  let T := (range J)×ˢ(range J)
  have hT : T.Nonempty := ⟨(0,0),mem_product.mpr ⟨mem_range.mpr hJ,mem_range.mpr hJ⟩⟩
  have hf : ∀e ∈ R, f e ∈ T := by
    intro e he
    exact mem_product.mpr ⟨mem_range.mpr (dyadicIndex_lt hL (ha e he).1 (ha e he).2 hj),
      mem_range.mpr (dyadicIndex_lt hL (hb e he).1 (hb e he).2 hj)⟩
  have hJ0 : (0:ℝ) < J := by exact_mod_cast hJ
  obtain ⟨i,hi,hgain⟩ := exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum (w := w) hf hT
    (b := (∑e ∈ R, w e)/(J:ℝ)^2) (by
      have hh : (T.card : ℝ) = (J:ℝ)^2 := by simp [T,pow_two]
      rw [nsmul_eq_mul,hh,mul_div_cancel₀ _ (ne_of_gt (sq_pos_of_pos hJ0))])
  refine ⟨R.filter (fun e => f e=i),?_,filter_subset _ _,hgain,?_⟩
  · apply card_pos.mp
    by_contra hh
    have he : (R.filter (fun e => f e=i)) = ∅ := card_eq_zero.mp (by omega)
    rw [he,sum_empty] at hgain
    exact (not_le_of_gt (div_pos hpos (sq_pos_of_pos hJ0))) hgain
  · intro e he g hg
    obtain ⟨he,hfe⟩ := mem_filter.mp he
    obtain ⟨hg,hfg⟩ := mem_filter.mp hg
    have heq := hfe.trans hfg.symm
    exact ⟨same_dyadic_ratio hL (ha e he).1 (ha g hg).1 (congrArg Prod.fst heq),
      same_dyadic_ratio hL (hb e he).1 (hb g hg).1 (congrArg Prod.snd heq)⟩

end
end StrongThinTree.Truncation

namespace StrongThinTree.Truncation
noncomputable section
open Finset
open scoped Classical
variable {E : Type uE3} [DecidableEq E]

lemma homogeneous_subset (S : Finset E) (a d : E → ℝ) {α : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hS : S.Nonempty)
    (ha : ∀e ∈ S, 0 ≤ a e) (hsq : ∀e ∈ S, (a e)^2 ≤ d e)
    (hpos : 0 < ∑e ∈ S, a e)
    (hbad : α*(S.card : ℝ)*(∑e ∈ S, d e) ≤ (∑e ∈ S, a e)^2) :
    let J := 1+⌈Real.logb 2 (256/α^2)⌉₊
    ∃B : Finset E, B.Nonempty ∧ B ⊆ S ∧
      (∑e ∈ S, a e)^2/(4*(J:ℝ)^4) ≤ (∑e ∈ B, a e)^2 ∧
      (∀e ∈ B, 0 < (a e)^2) ∧
      ∀e ∈ B, ∀f ∈ B, (a e)^2 < 2*(a f)^2 ∧ d e < 2*d f := by
  let J := 1+⌈Real.logb 2 (256/α^2)⌉₊
  let A := ∑e ∈ S, a e
  let μ := A/(S.card : ℝ)
  have hM : (0:ℝ) < S.card := by exact_mod_cast card_pos.mpr hS
  have hμ : 0 < μ := div_pos hpos hM
  obtain ⟨R,hRS,hRsum,hR⟩ := two_truncations S a d hα hα1 hS ha hsq hpos hbad
  have hRpos : 0 < ∑e ∈ R, a e := by linarith
  have hJ : 0 < J := by dsimp [J]; omega
  have hJr : (0:ℝ) < J := by exact_mod_cast hJ
  have hj : Real.logb 2 ((16*μ^2/α^2)/(μ^2/16)) < J := by
    have he : (16*μ^2/α^2)/(μ^2/16) = 256/α^2 := by field_simp; ring
    rw [he]
    have hh := Nat.le_ceil (Real.logb 2 (256/α^2))
    dsimp [J]
    push_cast
    linarith
  obtain ⟨B,hB,hBR,hgain,hratio⟩ := dyadic_pair R (fun e => (a e)^2) d a
    (show 0 < μ^2/16 by positivity) hJ hj
    (fun e he => ⟨(hR e he).1,(hR e he).2.1.trans (hR e he).2.2⟩)
    (fun e he => ⟨(hR e he).1.trans (hR e he).2.1,(hR e he).2.2⟩) hRpos
  refine ⟨B,hB,hBR.trans hRS,?_,?_,hratio⟩
  · change A^2/(4*(J:ℝ)^4) ≤ _
    have hbound : A/(2*(J:ℝ)^2) ≤ ∑e ∈ B, a e := by
      have hh := div_le_div_of_nonneg_right hRsum (sq_nonneg (J:ℝ))
      have he : (A/2)/(J:ℝ)^2 = A/(2*(J:ℝ)^2) := by ring
      change (A/2)/(J:ℝ)^2 ≤ _ at hh
      rw [he] at hh
      exact hh.trans hgain
    have hA : 0 < A := hpos
    have hnonneg : 0 ≤ A/(2*(J:ℝ)^2) := by positivity
    have hh := pow_le_pow_left₀ hnonneg hbound 2
    have he : (A/(2*(J:ℝ)^2))^2 = A^2/(4*(J:ℝ)^4) := by ring
    rw [he] at hh
    exact hh
  · intro e he
    exact lt_of_lt_of_le (by positivity : 0 < μ^2/16) (hR e (hBR he)).1

end
end StrongThinTree.Truncation

namespace StrongThinTree.Truncation
noncomputable section
open Finset
open scoped Classical
variable {E : Type uE4} [DecidableEq E]

lemma scaled_subset (O : Finset E) (a d : E → ℝ) {α : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hO : O.Nonempty)
    (ha : ∀e ∈ O, 0 ≤ a e) (hsq : ∀e ∈ O, (a e)^2 ≤ d e)
    (hpos : 0 < ∑e ∈ O, a e)
    (hbad : α*(O.card : ℝ)*(∑e ∈ O, d e) ≤ (∑e ∈ O, a e)^2)
    {L : ℕ} (hL : Real.logb 2 (16/(α*(1/(4*((1+⌈Real.logb 2 (256/α^2)⌉₊:ℕ):ℝ)^4))))+1 < L) :
    let J := 1+⌈Real.logb 2 (256/α^2)⌉₊
    let γ := 1/(4*(J:ℝ)^4)
    ∃B : Finset E, ∃idx : ℤ, ∃off : Fin L,
      B.Nonempty ∧ B ⊆ O ∧ γ*(∑e ∈ O, a e)^2 ≤ (∑e ∈ B, a e)^2 ∧
      (∀e ∈ B, 2^(idx:ℝ) ≤ (a e)^2) ∧
      (∀e ∈ B, (a e)^2 ≤ 4*2^(idx:ℝ)) ∧
      (∀e ∈ B, 2^((idx:ℝ)+off.val) ≤ d e) ∧
      (∀e ∈ B, d e ≤ 4*2^((idx:ℝ)+off.val)) := by
  let J := 1+⌈Real.logb 2 (256/α^2)⌉₊
  let γ := 1/(4*(J:ℝ)^4)
  have hJ : (0:ℝ) < J := by dsimp [J]; positivity
  have hγ : 0 < γ := by dsimp [γ]; positivity
  obtain ⟨B,hBn,hBO,hgain,hapos,hratio⟩ := homogeneous_subset O a d hα hα1 hO ha hsq hpos hbad
  obtain ⟨e₀,he₀,hmin₁⟩ := exists_min_image B (fun e => (a e)^2) hBn
  obtain ⟨f₀,hf₀,hmin₂⟩ := exists_min_image B d hBn
  let c₁ := (a e₀)^2
  let c₂ := d f₀
  have hc₁ : 0 < c₁ := hapos e₀ he₀
  have hc₁₂ : c₁ ≤ c₂ := (hmin₁ f₀ hf₀).trans (hsq f₀ (hBO hf₀))
  have hc₂ : 0 < c₂ := hc₁.trans_le hc₁₂
  have hdom : γ*(∑e ∈ O, a e)^2 ≤ (∑e ∈ B, a e)^2 := by
    simpa only [γ,one_div,inv_mul_eq_div] using hgain
  have hmax₁ : ∀e ∈ B, (a e)^2 ≤ 4*c₁ := by
    intro e he
    have hh := (hratio e he e₀ he₀).1.le
    dsimp [c₁]
    nlinarith only [hh,sq_nonneg (a e₀)]
  have hmin₂' : ∀e ∈ B, c₂/4 ≤ d e := by
    intro e he
    have hh : c₂ ≤ d e := hmin₂ e he
    linarith only [hh,hc₂]
  have hden := BagDensity.local_density O B a d hBO hBn hα hγ
    (fun e he => (sq_nonneg (a e)).trans (hsq e he)) hmax₁ hmin₂' hbad hdom
  have hcard : (B.card:ℝ) ≤ O.card := by exact_mod_cast card_le_card hBO
  have hOpos : (0:ℝ) < O.card := by exact_mod_cast card_pos.mpr hO
  have hscale : c₂ ≤ (16/(α*γ))*c₁ := by
    have hm := mul_le_mul_of_nonneg_left hcard (show 0 ≤ 16*c₁ by positivity)
    have hh : α*γ*c₂ ≤ 16*c₁ := by
      apply (mul_le_mul_iff_right₀ hOpos).mp
      nlinarith only [hden,hm]
    calc
      c₂ ≤ 16*c₁/(α*γ) := (le_div_iff₀ (mul_pos hα hγ)).mpr (by nlinarith only [hh])
      _ = (16/(α*γ))*c₁ := by ring
  let i := ⌊Real.logb 2 c₁⌋
  let j := ⌊Real.logb 2 c₂⌋
  have hoff := ScaleSelection.integer_scale_offset hc₁ hc₁₂ hscale hL
  let o : Fin L := ⟨(j-i).toNat, by dsimp [i,j] at *; omega⟩
  have hj : ((j:ℤ):ℝ)=(i:ℝ)+(o.val:ℝ) := by
    have hh : (o.val:ℤ)=j-i := Int.toNat_of_nonneg hoff.1
    have hh' := congrArg (fun x : ℤ => (x:ℝ)) hh
    push_cast at hh'
    linarith only [hh']
  have hi := ScaleSelection.integer_dyadic hc₁
  have hj' := ScaleSelection.integer_dyadic hc₂
  refine ⟨B,i,o,hBn,hBO,hdom,?_,?_,?_,?_⟩
  · intro e he
    exact hi.1.trans (hmin₁ e he)
  · intro e he
    have hh := (hratio e he e₀ he₀).1
    have hh' : (a e)^2 < 2*c₁ := hh
    have hhi : c₁ < 2*2^(i:ℝ) := hi.2
    nlinarith only [hh',hhi]
  · intro e he
    rw [←hj]
    exact hj'.1.trans (hmin₂ e he)
  · intro e he
    rw [←hj]
    have hh := (hratio e he f₀ hf₀).2
    have hh' : d e < 2*c₂ := hh
    have hjj : c₂ < 2*2^(j:ℝ) := hj'.2
    nlinarith only [hh',hjj]
end
end StrongThinTree.Truncation

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry StrongThinTree.Geometry.RadialShell
open scoped Classical
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ}

def truncationBins (α : ℝ) : ℕ := 1+⌈Real.logb 2 (256/α^2)⌉₊
def truncationGain (α : ℝ) : ℝ := 1/(4*(truncationBins α:ℝ)^4)

lemma truncationGain_pos (α : ℝ) : 0 < truncationGain α := by
  dsimp [truncationGain,truncationBins]
  positivity

lemma diagonal_sq_le (Y : Fin n → EuclideanSpace ℝ (Fin m))
    (hcontract : ∀u v, ‖Y u-Y v‖^2 ≤ l1dist (X u) (X v)) (e : Fin m) :
    ((Y (G.left e)-Y (G.right e)).ofLp e)^2 ≤ l1dist (X (G.left e)) (X (G.right e)) := by
  have hh := pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le (Y (G.left e)-Y (G.right e)) e) 2
  have he : ((Y (G.left e)-Y (G.right e)).ofLp e)^2 ≤ ‖Y (G.left e)-Y (G.right e)‖^2 := by
    simpa only [Real.norm_eq_abs,sq_abs] using hh
  exact he.trans (hcontract _ _)

lemma positive_bad_bound {q L R : ℕ} (hq : 0 < q) (hL : 0 < L) (hR : 0 < R)
    (hk : G.EdgeConnected q) (hX : ∀v, binary (X v))
    (hconn : H.LocallyConnectedReal G q)
    (T : Finset (Finset (Fin n))) (Y : Fin n → EuclideanSpace ℝ (Fin m))
    (hT : T ⊆ H.nodes) (hroot : ∀t ∈ T, t ≠ univ)
    {α ε ρ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (he : 0 < ε) (he1 : ε < 1/3)
    (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/1536)
    (hcontract : ∀u v, ‖Y u-Y v‖^2 ≤ l1dist (X u) (X v))
    (hpositive : ∀e, 0 ≤ (Y (G.left e)-Y (G.right e)).ofLp e)
    (hpos : ∀t ∈ T, 0 < ∑e ∈ H.parentBoundary G t, (Y (G.left e)-Y (G.right e)).ofLp e)
    (hbad : ∀t ∈ T, α*((H.parentBoundary G t).card : ℝ)*
      (∑e ∈ H.parentBoundary G t, l1dist (X (G.left e)) (X (G.right e))) ≤
      (∑e ∈ H.parentBoundary G t, (Y (G.left e)-Y (G.right e)).ofLp e)^2)
    (hsmall : (α*truncationGain α/32)^ε ≤ 1/(1728*(1024/ε^2)))
    (hassign : (6144:ℝ)/q ≤ (α*truncationGain α/32)^(1+2*ε))
    (hratio : ∀t ∈ T, (q:ℝ)*ρ*((G.cut univ t).card : ℝ) ≤ (H.parentBoundary G t).card)
    (hlogL : Real.logb 2 (16/(α*truncationGain α))+1 < L)
    (hlogR : Real.logb 2 (24/(ρ*(α*truncationGain α/32)^2)) < R) :
    let γ := truncationGain α
    let s := α*γ/32
    let N := ∑t ∈ T, (∑e ∈ H.parentBoundary G t, (Y (G.left e)-Y (G.right e)).ofLp e)^2/
      ((H.parentBoundary G t).card : ℝ)
    ((q:ℝ)/8192)*(s^ε/(6912*(1024/ε^2)))*(γ*N/(L:ℝ)) ≤
      2*R*(∑e : Fin m, l1dist (X (G.left e)) (X (G.right e))) := by
  let γ := truncationGain α
  let s := α*γ/32
  let a : Fin m → ℝ := fun e => (Y (G.left e)-Y (G.right e)).ofLp e
  let d : Fin m → ℝ := fun e => l1dist (X (G.left e)) (X (G.right e))
  let O := H.parentBoundary G
  have hγ : 0 < γ := truncationGain_pos α
  have hs : 0 < s := by dsimp [s]; positivity
  have hex : ∀t : Finset (Fin n), ∃B : Finset (Fin m), ∃i : ℤ, ∃o : Fin L,
      t ∈ T → B.Nonempty ∧ B ⊆ O t ∧ γ*(∑e ∈ O t, a e)^2 ≤ (∑e ∈ B, a e)^2 ∧
      (∀e ∈ B, 2^(i:ℝ) ≤ (a e)^2) ∧
      (∀e ∈ B, (a e)^2 ≤ 4*2^(i:ℝ)) ∧
      (∀e ∈ B, 2^((i:ℝ)+o.val) ≤ d e) ∧
      (∀e ∈ B, d e ≤ 4*2^((i:ℝ)+o.val)) := by
    intro t
    by_cases ht : t ∈ T
    · have hOn : (O t).Nonempty := by
        by_contra hh
        have heq : O t=∅ := not_nonempty_iff_eq_empty.mp hh
        have hp := hpos t ht
        change 0 < ∑e ∈ O t, a e at hp
        simp only [heq,sum_empty,lt_self_iff_false] at hp
      obtain ⟨B,i,o,hB⟩ := Truncation.scaled_subset (O t) a d hα hα1 hOn
        (fun e _ => hpositive e) (fun e _ => diagonal_sq_le Y hcontract e) (hpos t ht) (hbad t ht) hlogL
      exact ⟨B,i,o,fun _ => hB⟩
    · exact ⟨∅,0,⟨0,hL⟩,fun hh => (ht hh).elim⟩
  choose F idx off hf using hex
  have hh := homogeneous_scale_bound hq hL hR hk hX hconn T F idx off Y hT hroot
    (fun t ht => (hf t ht).2.1) (fun t ht => (hf t ht).1) hα hγ he he1 hρ hρsmall
    hcontract hpositive (fun t ht => (hf t ht).2.2.2.1)
    (fun t ht => (hf t ht).2.2.2.2.1) (fun t ht => (hf t ht).2.2.2.2.2.1)
    (fun t ht => (hf t ht).2.2.2.2.2.2) hbad (fun t ht => (hf t ht).2.2.1)
    hsmall hassign hratio hlogR
  have hsum : γ*(∑t ∈ T, (∑e ∈ O t, a e)^2/((O t).card:ℝ)) ≤
      ∑t ∈ T, (∑e ∈ F t, a e)^2/((O t).card:ℝ) := by
    rw [mul_sum]
    apply sum_le_sum
    intro t ht
    rw [←mul_div_assoc]
    exact div_le_div_of_nonneg_right (hf t ht).2.2.1 (Nat.cast_nonneg _)
  have hgain := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg L : (0:ℝ)≤L)
  have hc : 0 ≤ ((q:ℝ)/8192)*(s^ε/(6912*(1024/ε^2))) := by positivity
  exact (mul_le_mul_of_nonneg_left hgain hc).trans hh
lemma weighted_boundary_sum (M : Finset (Finset (Fin n)))
    (hM : M ⊆ H.nodes) (hroot : ∀t ∈ M, t ≠ univ)
    (d : Fin m → ℝ) (hd : ∀e, 0 ≤ d e) :
    (∑t ∈ M, ∑e ∈ H.parentBoundary G t, d e) ≤ 2*∑e, d e := by
  have heq : (∑t ∈ M, ∑e ∈ H.parentBoundary G t, d e) =
      ∑e, ((M.filter (fun t => e ∈ H.parentBoundary G t)).card : ℝ)*d e := by
    calc
      _ = ∑t ∈ M, ∑e : Fin m, if e ∈ H.parentBoundary G t then d e else 0 := by
        apply sum_congr rfl
        intro t ht
        rw [←sum_filter]
        simp
      _ = ∑e : Fin m, ∑t ∈ M, if e ∈ H.parentBoundary G t then d e else 0 := sum_comm
      _ = _ := by
        apply sum_congr rfl
        intro e he
        rw [←sum_filter, sum_const,nsmul_eq_mul]
  rw [heq,mul_sum]
  apply sum_le_sum
  intro e _
  apply mul_le_mul_of_nonneg_right _ (hd e)
  exact_mod_cast H.parentBoundary_multiplicity G M hM hroot e

lemma hierarchy_numerator_bound {q L R : ℕ} (hq : 0 < q) (hL : 0 < L) (hR : 0 < R)
    (hk : G.EdgeConnected q) (hX : ∀v, binary (X v))
    (hconn : H.LocallyConnectedReal G q)
    (M : Finset (Finset (Fin n))) (Y : Fin n → EuclideanSpace ℝ (Fin m))
    (hM : M ⊆ H.nodes) (hroot : ∀t ∈ M, t ≠ univ)
    {α ε ρ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (he : 0 < ε) (he1 : ε < 1/3)
    (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/1536)
    (hcontract : ∀u v, ‖Y u-Y v‖^2 ≤ l1dist (X u) (X v))
    (hpositive : ∀e, 0 ≤ (Y (G.left e)-Y (G.right e)).ofLp e)
    (hsmall : (α*truncationGain α/32)^ε ≤ 1/(1728*(1024/ε^2)))
    (hassign : (6144:ℝ)/q ≤ (α*truncationGain α/32)^(1+2*ε))
    (hratio : ∀t ∈ M, (q:ℝ)*ρ*((G.cut univ t).card : ℝ) ≤ (H.parentBoundary G t).card)
    (hlogL : Real.logb 2 (16/(α*truncationGain α))+1 < L)
    (hlogR : Real.logb 2 (24/(ρ*(α*truncationGain α/32)^2)) < R) :
    let γ := truncationGain α
    let s := α*γ/32
    (∑t ∈ M, (∑e ∈ H.parentBoundary G t, (Y (G.left e)-Y (G.right e)).ofLp e)^2/
      ((H.parentBoundary G t).card : ℝ)) ≤
      (2*α+2*(R:ℝ)*(L:ℝ)/(((q:ℝ)/8192)*(s^ε/(6912*(1024/ε^2)))*γ))*
        (∑e : Fin m, l1dist (X (G.left e)) (X (G.right e))) := by
  let O := H.parentBoundary G
  let a : Fin m → ℝ := fun e => (Y (G.left e)-Y (G.right e)).ofLp e
  let d : Fin m → ℝ := fun e => l1dist (X (G.left e)) (X (G.right e))
  let N : Finset (Fin n) → ℝ := fun t => (∑e ∈ O t, a e)^2/((O t).card:ℝ)
  let T := M.filter (fun t => 0 < ∑e ∈ O t, a e ∧
    α*((O t).card:ℝ)*(∑e ∈ O t, d e) ≤ (∑e ∈ O t, a e)^2)
  have hTM : T ⊆ M := filter_subset _ _
  have hgood : ∀t ∈ M\T, N t ≤ α*∑e ∈ O t, d e := by
    intro t ht
    have htM := (mem_sdiff.mp ht).1
    have htT := (mem_sdiff.mp ht).2
    have hd : 0 ≤ α*∑e ∈ O t, d e := mul_nonneg hα.le (sum_nonneg (fun e _ => l1dist_nonneg _ _))
    by_cases hp : 0 < ∑e ∈ O t, a e
    · have hn : ¬α*((O t).card:ℝ)*(∑e ∈ O t, d e) ≤ (∑e ∈ O t, a e)^2 := by
        intro hh; exact htT (mem_filter.mpr ⟨htM,hp,hh⟩)
      have hc : 0 < ((O t).card:ℝ) := by
        by_contra h
        have hz : (O t).card=0 := by exact_mod_cast le_antisymm (le_of_not_gt h) (Nat.cast_nonneg _)
        have hz' : O t=∅ := card_eq_zero.mp hz
        simp [hz'] at hp
      apply (div_le_iff₀ hc).mpr
      nlinarith only [lt_of_not_ge hn]
    · have hz : ∑e ∈ O t, a e=0 := le_antisymm (le_of_not_gt hp) (sum_nonneg (fun e _ => hpositive e))
      simpa [N,hz] using hd
  have hg : (∑t ∈ M\T, N t) ≤ 2*α*∑e, d e := by
    calc
      (∑t ∈ M\T, N t) ≤ ∑t ∈ M\T, α*∑e ∈ O t, d e := sum_le_sum hgood
      _ = α*∑t ∈ M\T, ∑e ∈ O t, d e := (mul_sum _ _ _).symm
      _ ≤ α*(2*∑e, d e) := mul_le_mul_of_nonneg_left
        (weighted_boundary_sum (M\T) (fun _ ht => hM (mem_sdiff.mp ht).1)
          (fun t ht => hroot t (mem_sdiff.mp ht).1) d (fun _ => l1dist_nonneg _ _)) hα.le
      _ = 2*α*∑e, d e := by ring
  have hb := positive_bad_bound hq hL hR hk hX hconn T Y (hTM.trans hM)
    (fun t ht => hroot t (hTM ht)) hα hα1 he he1 hρ hρsmall hcontract hpositive
    (fun t ht => (mem_filter.mp ht).2.1) (fun t ht => (mem_filter.mp ht).2.2)
    hsmall hassign (fun t ht => hratio t (hTM ht)) hlogL hlogR
  let γ := truncationGain α
  let s := α*γ/32
  let c := ((q:ℝ)/8192)*(s^ε/(6912*(1024/ε^2)))*γ
  have hγ : 0 < γ := truncationGain_pos α
  have hs : 0 < s := by dsimp [s]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hL' : 0 < (L:ℝ) := Nat.cast_pos.mpr hL
  have hb' : (∑t ∈ T, N t) ≤ (2*(R:ℝ)*(L:ℝ)/c)*(∑e, d e) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hc).mpr
    have hh := (div_le_iff₀ hL').mp (show c*(∑t ∈ T, N t)/L ≤ 2*(R:ℝ)*∑e, d e by
      convert hb using 1 ; dsimp [c,N,γ,s,O,a,d] ; ring)
    nlinarith only [hh]
  change (∑t ∈ M, N t) ≤ (2*α+2*(R:ℝ)*(L:ℝ)/c)*(∑e, d e)
  rw [←sum_sdiff hTM]
  nlinarith only [hg,hb']
end
end StrongThinTree.MultiGraph.Hierarchy

end

end OAI
