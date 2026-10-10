import OAI.Combinatorics.FiniteCircle.CircleWords

namespace OAI

namespace FiniteCircle

open scoped BigOperators List

abbrev MaskResidues (h : ℕ) (p : ℕ → ℕ → ℕ) (l : ℕ) := (k : Fin h) → ZMod (p l k)

noncomputable def maskPhaseHom (h : ℕ) (p : ℕ → ℕ → ℕ) (M l : ℕ)
    (hd : ∀ k : Fin h, p l k ∣ M) : MaskResidues h p l →+ (MaskTag h p l → ZMod M) where
  toFun z j := (∑ k, subcircle (hd k) (z k)) + j.2.val • subcircle (hd j.1) (z j.1)
  map_zero' := by funext j; simp
  map_add' z u := by
    funext j
    simp only [Pi.add_apply, map_add, Finset.sum_add_distrib, nsmul_add]
    abel

 theorem maskPhaseHom_natCast (h : ℕ) (p : ℕ → ℕ → ℕ) (M l a : ℕ)
    (hd : ∀ k : Fin h, p l k ∣ M) (hn : ∀ k : Fin h, 0 < p l k) :
    maskPhaseHom h p M l hd (fun k => (a : ZMod (p l k))) = maskGamma h p M l a := by
  funext j
  change (∑ k, subcircle (hd k) (a : ZMod (p l k))) +
    j.2.val • subcircle (hd j.1) (a : ZMod (p l j.1)) = _
  have he (k : Fin h) : subcircle (hd k) (a : ZMod (p l k)) =
    ((M/p l k*(a%p l k) : ℕ) : ZMod M) := by
    let : NeZero (p l k) := ⟨(hn k).ne'⟩
    rw [subcircle_val, ZMod.val_natCast]
  simp_rw [he]
  simp only [maskGamma, nsmul_eq_mul, Nat.cast_mul]
  ring

 theorem sum_fin_zmod {p : ℕ} [NeZero p] (g : ZMod p → ℝ) :
    ∑ b : Fin p, g (b.val : ZMod p) = ∑ b : ZMod p, g b := by
  refine Fintype.sum_equiv (ZMod.finEquiv p).toEquiv _ _ ?_
  intro b
  congr 1
  cases p with
  | zero => exact Fin.elim0 b
  | succ p =>
    change (b.val : ZMod (p+1)) = b
    exact ZMod.natCast_zmod_val (show ZMod (p+1) from b)

noncomputable def maskCost (h : ℕ) (p : ℕ → ℕ → ℕ) (M : ℕ)
    (hd : ∀ l (k : Fin h), p l k ∣ M) (hn : ∀ l (k : Fin h), 0 < p l k) :
    ℕ → PhaseCost (ZMod M)
  | 0 => circlePhaseCost M
  | l+1 => by
    let : ∀ k : Fin h, NeZero (p (l+1) k) := fun k => ⟨(hn _ k).ne'⟩
    exact (maskCost h p M hd hn l).step (maskPhaseHom h p M (l+1) (hd _))

 theorem maskCost_le_half {h M : ℕ} {p : ℕ → ℕ → ℕ} [NeZero M]
    (hh : 0 < h) (hd : ∀ l (k : Fin h), p l k ∣ M) (hn : ∀ l (k : Fin h), 0 < p l k)
    (l : ℕ) (x : ZMod M) : maskCost h p M hd hn l x ≤ 1/2 := by
  induction l with
  | zero => exact circleCost_le_half x
  | succ l ih =>
    let : ∀ k : Fin h, NeZero (p (l+1) k) := fun k => ⟨(hn _ k).ne'⟩
    let : Nonempty (MaskTag h p (l+1)) := ⟨⟨⟨0,hh⟩,⟨0,hn _ ⟨0,hh⟩⟩⟩⟩
    exact ((maskCost h p M hd hn l).infAverage_le_self _ x).trans ih

 theorem card_maskTag (h : ℕ) (p : ℕ → ℕ → ℕ) (l : ℕ) :
    Fintype.card (MaskTag h p l) = ∑ k : Fin h, p l k := by
  simp only [MaskTag, Fintype.card_sigma, Fintype.card_fin]

 theorem mask_average_formula {h M l : ℕ} {p : ℕ → ℕ → ℕ}
    (hd : ∀ k : Fin h, p l k ∣ M) (hn : ∀ k : Fin h, 0 < p l k)
    (f : PhaseCost (ZMod M)) (x : ZMod M) (z : MaskResidues h p l) :
    f.average (maskPhaseHom h p M l hd) x z =
      (∑ k : Fin h, ∑ b : Fin (p l k),
        f (x+(∑ k,subcircle (hd k) (z k))+b.val • subcircle (hd k) (z k))) /
          (∑ k : Fin h, (p l k : ℝ)) := by
  let : ∀ k : Fin h, NeZero (p l k) := fun k => ⟨(hn k).ne'⟩
  simp only [PhaseCost.average, card_maskTag, Nat.cast_sum, Fintype.sum_sigma]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  change x+((∑ k,subcircle (hd k) (z k))+b.val • subcircle (hd k) (z k)) = _
  abel

theorem mask_active_average_lower {h M l : ℕ} {p : ℕ → ℕ → ℕ}
    (hh : 0 < h) (hd : ∀ k : Fin h, p l k ∣ M)
    (hp : ∀ k : Fin h, (p l k).Prime)
    (hlo : ∀ k : Fin h, h^3 ≤ p l k) (hhi : ∀ k : Fin h, p l k ≤ 2*h^3)
    (f : PhaseCost (ZMod M)) (x : ZMod M) (z : MaskResidues h p l)
    (Q : ℝ) (hQ : 0 ≤ Q)
    (hq : ∀ k : Fin h, z k ≠ 0 → Q ≤ f (subcircle (hd k) 1)) :
    (((Finset.univ.filter (fun k : Fin h => z k ≠ 0)).card : ℝ)/(4*h))*Q ≤
      f.average (maskPhaseHom h p M l hd) x z := by
  classical
  let : ∀ k : Fin h, NeZero (p l k) := fun k => ⟨(hp k).ne_zero⟩
  let S := Finset.univ.filter (fun k : Fin h => z k ≠ 0)
  let T : ℝ := ∑ k : Fin h, (p l k : ℝ)
  let B (k : Fin h) : ℝ := ∑ b : Fin (p l k),
    f (x+(∑ j,subcircle (hd j) (z j))+b.val • subcircle (hd k) (z k))
  have hB (k : Fin h) : 0 ≤ B k := Finset.sum_nonneg (fun _ _ => f.nonneg _)
  have hT : 0 < T := by
    apply Finset.sum_pos
    · intro k _; exact_mod_cast (hp k).pos
    · exact Finset.univ_nonempty_iff.mpr ⟨⟨0,hh⟩⟩
  have hTu : T ≤ 2*(h:ℝ)^4 := by
    calc
      T ≤ ∑ _k : Fin h, (2:ℝ)*h^3 := Finset.sum_le_sum (fun k _ => by exact_mod_cast hhi k)
      _ = _ := by simp; ring
  have hkb (k : Fin h) (hk : k ∈ S) : (h:ℝ)^3*Q ≤ 2*B k := by
    have ha := f.prime_grid_bound (hp k) (subcircle (hd k))
      (x+∑ j,subcircle (hd j) (z j)) (z k) ((Finset.mem_filter.mp hk).2)
    have he : B k = ∑ b : ZMod (p l k),
        f (x+(∑ j,subcircle (hd j) (z j))+b.val • subcircle (hd k) (z k)) := by
      symm
      rw [← sum_fin_zmod]
      apply Finset.sum_congr rfl
      intro b _
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt b.isLt]
    rw [← he] at ha
    calc
      (h:ℝ)^3*Q ≤ (p l k : ℝ)*Q := mul_le_mul_of_nonneg_right (by exact_mod_cast hlo k) hQ
      _ ≤ (p l k : ℝ)*f (subcircle (hd k) 1) := mul_le_mul_of_nonneg_left (hq k ((Finset.mem_filter.mp hk).2)) (by positivity)
      _ ≤ _ := ha
  have hsum : (S.card : ℝ)*(h:ℝ)^3*Q ≤ 2*∑ k : Fin h, B k := by
    calc
      _ = ∑ _k ∈ S, (h:ℝ)^3*Q := by simp; ring
      _ ≤ ∑ k ∈ S, 2*B k := Finset.sum_le_sum hkb
      _ ≤ ∑ k : Fin h, 2*B k := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun k _ _ => mul_nonneg (by norm_num) (hB k))
      _ = _ := (Finset.mul_sum ..).symm
  rw [mask_average_formula hd (fun k => (hp k).pos)]
  change (S.card : ℝ)/(4*h)*Q ≤ (∑ k : Fin h, B k)/T
  rw [le_div_iff₀ hT]
  have hh' : (0:ℝ) < h := by exact_mod_cast hh
  have hb : 0 ≤ (S.card : ℝ)/(4*h)*Q := by positivity
  calc
    _ ≤ ((S.card : ℝ)/(4*h)*Q)*(2*(h:ℝ)^4) := mul_le_mul_of_nonneg_left hTu hb
    _ = ((S.card : ℝ)*(h:ℝ)^3*Q)/2 := by field_simp; ring
    _ ≤ _ := by linarith

theorem mask_inactive_average_lower {h M l : ℕ} {p : ℕ → ℕ → ℕ}
    (hh : 0 < h) (hd : ∀ k : Fin h, p l k ∣ M)
    (hp : ∀ k : Fin h, (p l k).Prime)
    (hlo : ∀ k : Fin h, h^3 ≤ p l k) (hhi : ∀ k : Fin h, p l k ≤ 2*h^3)
    (f : PhaseCost (ZMod M)) (x : ZMod M) (z : MaskResidues h p l)
    (hs : 2*(Finset.univ.filter (fun k : Fin h => z k ≠ 0)).card ≤ h) :
    (1/4:ℝ)*f (x+∑ k,subcircle (hd k) (z k)) ≤
      f.average (maskPhaseHom h p M l hd) x z := by
  classical
  let N := Finset.univ.filter (fun k : Fin h => z k = 0)
  let T : ℝ := ∑ k : Fin h, (p l k : ℝ)
  let B (k : Fin h) : ℝ := ∑ b : Fin (p l k),
    f (x+(∑ j,subcircle (hd j) (z j))+b.val • subcircle (hd k) (z k))
  let Q := f (x+∑ k,subcircle (hd k) (z k))
  have hQ : 0 ≤ Q := f.nonneg _
  have hB (k : Fin h) : 0 ≤ B k := Finset.sum_nonneg (fun _ _ => f.nonneg _)
  have hT : 0 < T := by
    apply Finset.sum_pos
    · intro k _; exact_mod_cast (hp k).pos
    · exact Finset.univ_nonempty_iff.mpr ⟨⟨0,hh⟩⟩
  have hTu : T ≤ 2*(h:ℝ)^4 := by
    calc
      T ≤ ∑ _k : Fin h, (2:ℝ)*h^3 := Finset.sum_le_sum (fun k _ => by exact_mod_cast hhi k)
      _ = _ := by simp; ring
  have hN : (h:ℝ) ≤ 2*N.card := by
    have hc := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun k : Fin h => z k = 0)
    simp only [Finset.card_univ, Fintype.card_fin] at hc
    change N.card + (Finset.univ.filter (fun k : Fin h => z k ≠ 0)).card = h at hc
    exact_mod_cast (show h ≤ 2*N.card by omega)
  have hkb (k : Fin h) (hk : k ∈ N) : (h:ℝ)^3*Q ≤ B k := by
    have hz := (Finset.mem_filter.mp hk).2
    have he : B k = (p l k : ℝ)*Q := by
      simp [B, Q, hz]
    rw [he]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hlo k) hQ
  have hsum : (N.card : ℝ)*(h:ℝ)^3*Q ≤ ∑ k : Fin h, B k := by
    calc
      _ = ∑ _k ∈ N, (h:ℝ)^3*Q := by simp; ring
      _ ≤ ∑ k ∈ N, B k := Finset.sum_le_sum hkb
      _ ≤ ∑ k : Fin h, B k := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun k _ _ => hB k)
  rw [mask_average_formula hd (fun k => (hp k).pos)]
  change (1/4:ℝ)*Q ≤ (∑ k : Fin h, B k)/T
  rw [le_div_iff₀ hT]
  calc
    _ ≤ ((1/4:ℝ)*Q)*(2*(h:ℝ)^4) := mul_le_mul_of_nonneg_left hTu (by positivity)
    _ = ((h:ℝ)/2)*h^3*Q := by ring
    _ ≤ (N.card : ℝ)*h^3*Q := by gcongr; linarith
    _ ≤ _ := hsum

theorem mask_minimizer_options {h M l : ℕ} {p : ℕ → ℕ → ℕ}
    [∀ k : Fin h, NeZero (p l k)]
    (hh : 0 < h) (hd : ∀ k : Fin h, p l k ∣ M)
    (hp : ∀ k : Fin h, (p l k).Prime)
    (hlo : ∀ k : Fin h, h^3 ≤ p l k) (hhi : ∀ k : Fin h, p l k ≤ 2*h^3)
    (f : PhaseCost (ZMod M)) (x : ZMod M) :
    ∃ z : MaskResidues h p l,
      (let S := Finset.univ.filter (fun k : Fin h => z k ≠ 0)
       (∀ Q : ℝ, 0 ≤ Q → (∀ k ∈ S, Q ≤ f (subcircle (hd k) 1)) →
        (S.card : ℝ)/(4*h)*Q ≤ f.infAverage (maskPhaseHom h p M l hd) x) ∧
       (2*S.card ≤ h → (1/4:ℝ)*f (x+∑ k,subcircle (hd k) (z k)) ≤
         f.infAverage (maskPhaseHom h p M l hd) x)) := by
  classical
  let : ∀ k : Fin h, NeZero (p l k) := fun k => ⟨(hp k).ne_zero⟩
  obtain ⟨z,hz⟩ := f.exists_average_eq (maskPhaseHom h p M l hd) x
  refine ⟨z, ?_⟩
  dsimp only
  rw [hz]
  constructor
  · intro Q hQ hq
    exact mask_active_average_lower hh hd hp hlo hhi f x z Q hQ
      (fun k hk => hq k (by simp [hk]))
  · exact mask_inactive_average_lower hh hd hp hlo hhi f x z

 theorem deficit_cast {β : Type*} (x y : List β) : (deficit x y : ℝ) = (x.length:ℝ) - lcs x y := by
  exact Nat.cast_sub (lcs_le_length_left x y)

 theorem deficit_taggedRow_lower {J β : Type*} [Fintype J] [DecidableEq J]
    (js : List J) (hn : js.Nodup) (hall : ∀ j, j ∈ js) (W U : J → List β) :
    (∑ j : J, (deficit (W j) (U j) : ℝ)) ≤
      deficit (taggedRow js W) (taggedRow js U) := by
  have hc := lcs_taggedRow_le js hn hall W U
  have hcr : (lcs (taggedRow js W) (taggedRow js U) : ℝ) ≤ ∑ j : J, (lcs (W j) (U j) : ℝ) := by exact_mod_cast hc
  simp_rw [deficit_cast]
  rw [Finset.sum_sub_distrib, length_taggedRow js hn hall W, Nat.cast_sum]
  linarith

 theorem maskLength_pos {h M R : ℕ} {p : ℕ → ℕ → ℕ}
    (hh : 0 < h) (hM : 0 < M) (hR : 0 < R) (hn : ∀ l (k : Fin h), 0 < p l k)
    (l : ℕ) : 0 < maskLength h p R M l := by
  induction l with
  | zero => exact hM
  | succ l ih =>
    unfold maskLength
    apply Nat.mul_pos (Nat.mul_pos hR (Finset.prod_pos (fun k _ => hn _ k)))
    apply Nat.mul_pos _ ih
    rw [length_maskTags]
    exact Finset.sum_pos (fun k _ => hn _ k) (Finset.univ_nonempty_iff.mpr ⟨⟨0,hh⟩⟩)

theorem mask_separation {h M R : ℕ} {p : ℕ → ℕ → ℕ} [NeZero M]
    (he : M = 2*(M/2)) (hh : 0 < h) (hR : 0 < R)
    (hd : ∀ l (k : Fin h), p l k ∣ M) (hn : ∀ l (k : Fin h), 0 < p l k)
    (ht : ∀ l, 4 ≤ (maskTags h p l).length)
    (l : ℕ) (v : MaskState h p M l) (θ : ZMod M) :
    (1/((2:ℝ)^l*4))*(maskLength h p R M l)*maskCost h p M hd hn l θ ≤
      (deficit (maskWord h p R M l v)
        (maskWord h p R M l (shiftMaskState h p M l v θ)) : ℝ) := by
  classical
  induction l generalizing θ with
  | zero =>
    change ZMod M at v
    change (1/((2:ℝ)^0*4))*M*circleCost θ ≤
      (deficit (maskWord h p R M 0 v) (maskWord h p R M 0 (v+θ)) : ℝ)
    rw [maskWord_zero_eq, maskWord_zero_eq]
    calc
      _ = (M:ℝ)*circleCost θ/4 := by norm_num; ring
      _ ≤ _ := halfCircle_separation he v θ
  | succ l ih =>
    let : ∀ k : Fin h, NeZero (p (l+1) k) := fun k => ⟨(hn _ k).ne'⟩
    let L := maskLength h p R M l
    let t := (maskTags h p (l+1)).length
    let N := R*period h p (l+1)
    let f := maskCost h p M hd hn l
    let σ := maskPhaseHom h p M (l+1) (hd _)
    let ρ := (1/((2:ℝ)^l*4))*maskCost h p M hd hn (l+1) θ
    have hL : 0 < L := maskLength_pos hh (NeZero.pos M) hR hn l
    have hp2 : 1 ≤ (2:ℝ)^l := one_le_pow₀ (by norm_num)
    have hρ : ρ ≤ 1/2 := by
      have hc := maskCost_le_half hh hd hn (l+1) θ
      have hc0 := (maskCost h p M hd hn (l+1)).nonneg θ
      dsimp [ρ]
      have hi : 1/((2:ℝ)^l*4) ≤ 1 := (div_le_one (by positivity)).mpr (by nlinarith)
      calc
        _ ≤ 1*maskCost h p M hd hn (l+1) θ := mul_le_mul_of_nonneg_right hi hc0
        _ ≤ _ := by simpa using hc
    have hx : (maskWord h p R M (l+1) v).length = (t*L)*N := by
      rw [length_maskWord]
      change N*(t*L) = (t*L)*N
      exact Nat.mul_comm _ _
    have hy : (maskWord h p R M (l+1) (shiftMaskState h p M (l+1) v θ)).length = (t*L)*N := by
      rw [length_maskWord]
      change N*(t*L) = (t*L)*N
      exact Nat.mul_comm _ _
    have hr := row_separation hL (ht (l+1)) hx hy
      (fun x => (maskTags h p (l+1)).idxOf x.1)
      (tag_get_maskWord h p R M l v hL (by have := ht (l+1); omega))
      (tag_get_maskWord h p R M l _ hL (by have := ht (l+1); omega)) ρ hρ
    have hrows : ∀ i j : Fin N, ρ*(t*L) ≤
        (deficit (segment (maskWord h p R M (l+1) v) (i.val*(t*L)) (t*L))
          (segment (maskWord h p R M (l+1) (shiftMaskState h p M (l+1) v θ))
            (j.val*(t*L)) (t*L)) : ℝ) := by
      intro a b
      rw [segment_maskWord, segment_maskWord]
      let z : MaskResidues h p (l+1) := fun k => (b.val : ZMod (p (l+1) k)) - (a.val : ZMod (p (l+1) k))
      have hz (j : MaskTag h p (l+1)) : σ z j =
          maskGamma h p M (l+1) b j - maskGamma h p M (l+1) a j := by
        change σ ((fun k : Fin h => (b.val : ZMod (p (l+1) k))) - (fun k : Fin h => (a.val : ZMod (p (l+1) k)))) j = _
        rw [map_sub, Pi.sub_apply]
        exact congrArg₂ (·-·) (congrFun (maskPhaseHom_natCast h p M (l+1) b (hd _) (hn _)) j)
          (congrFun (maskPhaseHom_natCast h p M (l+1) a (hd _) (hn _)) j)
      have hind (j : MaskTag h p (l+1)) := ih
        (shiftMaskState h p M l (v j) (maskGamma h p M (l+1) a j)) (θ+σ z j)
      have hstate (j : MaskTag h p (l+1)) :
          shiftMaskState h p M l (shiftMaskState h p M l (v j) (maskGamma h p M (l+1) a j)) (θ+σ z j) =
          shiftMaskState h p M l (shiftMaskState h p M l (v j) θ) (maskGamma h p M (l+1) b j) := by
        rw [shiftMaskState_add, shiftMaskState_add, hz]
        congr 1
        abel
      simp_rw [hstate] at hind
      have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hind j)
      have hdef := deficit_taggedRow_lower (maskTags h p (l+1)) (nodup_maskTags ..)
        (mem_maskTags h p (l+1))
        (fun j => maskWord h p R M l (shiftMaskState h p M l (v j) (maskGamma h p M (l+1) a j)))
        (fun j => maskWord h p R M l (shiftMaskState h p M l (shiftMaskState h p M l (v j) θ) (maskGamma h p M (l+1) b j)))
      apply le_trans _ (hsum.trans hdef)
      rw [← Finset.mul_sum]
      have hcost : maskCost h p M hd hn (l+1) θ ≤ f.average σ θ z := f.infAverage_le σ θ z
      have htpos : (0:ℝ) < t := by exact_mod_cast (show 0 < t by have := ht (l+1); omega)
      have hcard : (Fintype.card (MaskTag h p (l+1)) : ℝ) = t := by rw [card_maskTag]; exact_mod_cast (length_maskTags h p (l+1)).symm
      rw [PhaseCost.average, hcard, le_div_iff₀ htpos] at hcost
      dsimp only [ρ]
      calc
        _ = ((1/((2:ℝ)^l*4))*(L:ℝ)) * ((maskCost h p M hd hn (l+1) θ)*t) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hcost (by positivity)
    have hfinal := hr hrows
    rw [length_maskWord] at hfinal
    dsimp only [ρ] at hfinal
    calc
      _ = ((1/((2:ℝ)^l*4))*maskCost h p M hd hn (l+1) θ)/2 * maskLength h p R M (l+1) := by rw [pow_succ]; ring
      _ ≤ _ := hfinal

end FiniteCircle

end OAI
