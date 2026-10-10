import OAI.Combinatorics.EditDistance.CutModels
import OAI.Combinatorics.EditDistance.DyadicScales
import OAI.Combinatorics.EditDistance.Windows

namespace OAI

/-!
# Dyadic-window recursion and insertion bounds
-/

namespace EditUpper
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open Finset EditDistortion EditWindow EditCutModel

variable {A : Type*}

def samples (x : List A) (start l s : ℕ) : Fin s → List (Option A) :=
  fun i => window x (start+i.val) (l-s+1)

noncomputable def piece (M : Model (List (Option A))) (x y : List A) (start l s : ℕ) : ℝ :=
  EditCutHash.meanHistogram M.weight (EditCutHash.rate s) M.cut
    (samples x start l s) (samples y start l s)

lemma piece_nonneg (M : Model (List (Option A))) (x y : List A) (start l s : ℕ) (hs : 0 < s) :
    0 ≤ piece M x y start l s :=
  EditCutHash.meanHistogram_nonneg M.nonneg (EditCutHash.rate_nonneg hs) _ _ _

noncomputable def lift (M : Model (List (Option A))) (b l : ℕ) : Model (List A) :=
  (Model.total (fun j : Fin b × Fin (Nat.log 2 l+1) =>
    (M.histogram (2^j.2.val) (EditCutHash.rate (2^j.2.val))
      (EditCutHash.rate_nonneg (pow_pos (by omega) _))).pullback
        (fun x => samples x (j.1.val*l) l (2^j.2.val)))).scale 16 (by norm_num)

lemma lift_dist (M : Model (List (Option A))) (b l : ℕ) (x y : List A) :
    (lift M b l).dist x y =
      16 * ∑ j : Fin b, ∑ r : Fin (Nat.log 2 l+1), piece M x y (j.val*l) l (2^r.val) := by
  rw [lift,Model.scale_dist,Model.total_dist,Fintype.sum_prod_type]
  congr 1
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro r _
  rw [Model.pullback_dist,Model.histogram_dist]
  rfl

lemma block_indel_bound (x y : List A) (start l : ℕ) :
    indel (window x start l) (window y start l) ≤ 2*l := by
  have h : indel (window x start l) (window y start l) ≤
      (window x start l).length+(window y start l).length := by
    exact cost_le ((Script.to_nil (s := false) _).trans (Script.to_nil _).symm)
  simpa only [window_length,two_mul] using h

lemma block_lower (M : Model (List (Option A))) (l : ℕ) (hl : 0 < l)
    (hM : ∀ u v : List (Option A), u.length ≤ l → v.length ≤ l →
      (indel u v : ℝ) ≤ M.dist u v) (x y : List A) (start : ℕ) :
    (indel (window x start l) (window y start l) : ℝ) ≤
      16 * ∑ r : Fin (Nat.log 2 l+1), piece M x y start l (2^r.val) := by
  let delta := indel (window x start l) (window y start l)
  have hnn (r : Fin (Nat.log 2 l+1)) : 0 ≤ piece M x y start l (2^r.val) :=
    piece_nonneg _ _ _ _ _ _ (pow_pos (by omega) _)
  by_cases hd : delta = 0
  · change (delta : ℝ) ≤ _
    rw [hd,Nat.cast_zero]
    exact mul_nonneg (by norm_num) (sum_nonneg (fun r _ => hnn r))
  · obtain ⟨r,hs,hsl,hds,hsd⟩ := EditDyadic.scale hl (Nat.pos_of_ne_zero hd) (block_indel_bound x y start l)
    have hcross (i j : Fin (2^r.val)) : ((2^r.val : ℕ) : ℝ) ≤
        EditCutHash.distance M.weight M.cut (samples x start l (2^r.val) i) (samples y start l (2^r.val) j) := by
      rw [Model.distance_eq]
      have htri := segment_cross (fun k => x[k]?) (fun k => y[k]?) start l (2^r.val) hs hsl i j
      change delta ≤ 2*(2^r.val-1)+indel (samples x start l (2^r.val) i)
        (samples y start l (2^r.val) j) at htri
      have hloss : 2^r.val ≤ indel (samples x start l (2^r.val) i)
          (samples y start l (2^r.val) j) := by omega
      calc
        _ ≤ (indel (samples x start l (2^r.val) i) (samples y start l (2^r.val) j) : ℝ) := by exact_mod_cast hloss
        _ ≤ _ := hM _ _ (by simp only [samples,window_length]; omega) (by simp only [samples,window_length]; omega)
    have hh := EditCutHash.meanHistogram_separated (by omega : 0 < 2^r.val) M.nonneg M.cut
      (samples x start l (2^r.val)) (samples y start l (2^r.val)) hcross
    change ((2^r.val : ℕ) : ℝ) ≤ piece M x y start l (2^r.val) at hh
    have hsum := single_le_sum (fun j _ => hnn j) (mem_univ r)
    have hdsr : (delta : ℝ) ≤ 16*((2^r.val : ℕ) : ℝ) := by exact_mod_cast hds
    change (delta : ℝ) ≤ _
    nlinarith

lemma lift_lower (M : Model (List (Option A))) (b l : ℕ) (hl : 0 < l)
    (hM : ∀ u v : List (Option A), u.length ≤ l → v.length ≤ l →
      (indel u v : ℝ) ≤ M.dist u v) (x y : List A)
    (hx : x.length ≤ b*l) (hy : y.length ≤ b*l) :
    (indel x y : ℝ) ≤ (lift M b l).dist x y := by
  have h1 := indel_le_window x y (b*l) hx hy
  have h2 := indel_segment_blocks (fun k => x[k]?) (fun k => y[k]?) l b
  change indel (window x 0 (b*l)) (window y 0 (b*l)) ≤ _ at h2
  have h3 : (indel x y : ℝ) ≤
      ∑ j : Fin b, (indel (window x (j.val*l) l) (window y (j.val*l) l) : ℝ) := by
    rw [Fin.sum_univ_eq_sum_range (fun j => (indel (window x (j*l) l) (window y (j*l) l) : ℝ)) b]
    exact_mod_cast h1.trans h2
  rw [lift_dist,mul_sum]
  apply h3.trans
  apply sum_le_sum
  intro j _
  exact block_lower M l hl hM x y (j.val*l)

lemma piece_insert_general (M : Model (List (Option A))) {D : ℝ} (hD : 0 ≤ D)
    (hM : ∀ u v, M.dist u v ≤ D*(indel u v : ℝ))
    (p q : List A) (a : A) (start l s : ℕ) (hs : 0 < s) :
    piece M (p++q) (p++a::q) start l s ≤ 4*Real.log (2*(s : ℝ)^2)*D := by
  have hup := EditCutHash.meanHistogram_upper M.nonneg (EditCutHash.rate_nonneg hs) M.cut
    (samples (p++q) start l s) (samples (p++a::q) start l s)
  have hsum : (∑ i : Fin s, EditCutHash.distance M.weight M.cut
      (samples (p++q) start l s i) (samples (p++a::q) start l s i)) ≤ (s : ℝ)*(2*D) := by
    calc
      _ ≤ ∑ _i : Fin s, 2*D := by
        apply sum_le_sum
        intro i _
        rw [Model.distance_eq]
        have hcost := window_insert_cost p q a (start+i.val) (l-s+1)
        have hcr : (indel (samples (p++q) start l s i) (samples (p++a::q) start l s i) : ℝ) ≤ 2 := by exact_mod_cast hcost
        exact (hM _ _).trans (by nlinarith)
      _ = _ := by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hr := EditCutHash.rate_nonneg hs
  have h := hup.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
  change piece M (p++q) (p++a::q) start l s ≤ _ at h
  apply h.trans_eq
  unfold EditCutHash.rate
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hs)
  field_simp
  ring

lemma piece_before (M : Model (List (Option A))) (p q : List A) (a : A)
    (start l s : ℕ) (_hs : 0 < s) (hsl : s ≤ l) (hp : start+l ≤ p.length) :
    piece M (p++q) (p++a::q) start l s = 0 := by
  have he : samples (p++q) start l s = samples (p++a::q) start l s := by
    funext i
    exact (window_before p q a (by omega)).symm
  unfold piece
  rw [←he,EditCutHash.meanHistogram_self]

lemma piece_after (M : Model (List (Option A))) (p q : List A) (a : A)
    (start l s : ℕ) (hs : 0 < s) (hp : p.length ≤ start) :
    piece M (p++q) (p++a::q) start l s ≤ 2 := by
  apply EditCutHash.meanHistogram_shift hs M.nonneg (EditCutHash.rate_nonneg hs)
  intro i
  exact (window_after p q a (by omega)).symm

end EditUpper

namespace EditUpper
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open Finset EditDistortion EditWindow EditCutModel
variable {A : Type*}

lemma sum_block_insert (M : Model (List (Option A))) {D : ℝ} (hD : 0 ≤ D)
    (hM : ∀ u v, M.dist u v ≤ D*(indel u v : ℝ))
    (p q : List A) (a : A) (b l s : ℕ) (hl : 0 < l) (hs : 0 < s) (hsl : s ≤ l) :
    (∑ j : Fin b, piece M (p++q) (p++a::q) (j.val*l) l s) ≤
      2*(b : ℝ)+4*Real.log (2*(s : ℝ)^2)*D := by
  let K := 4*Real.log (2*(s : ℝ)^2)*D
  have hK : 0 ≤ K := by
    dsimp [K]
    have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
    exact mul_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by nlinarith))) hD
  have hj (j : Fin b) : piece M (p++q) (p++a::q) (j.val*l) l s ≤
      2+(if j.val = p.length/l then K else 0) := by
    by_cases he : j.val = p.length/l
    · rw [ite_eq_left he]
      have hh := piece_insert_general M hD hM p q a (j.val*l) l s hs
      change _ ≤ K at hh
      linarith
    · rw [ite_eq_right he,add_zero]
      by_cases hlt : j.val < p.length/l
      · have hp : j.val*l+l ≤ p.length := by
          have h1 := Nat.mul_le_mul_right l (show j.val+1 ≤ p.length/l by omega)
          have h2 := Nat.div_mul_le_self p.length l
          nlinarith
        rw [piece_before M p q a (j.val*l) l s hs hsl hp]
        norm_num
      · have hp : p.length ≤ j.val*l := by
          have h1 := Nat.mul_le_mul_right l (show p.length/l+1 ≤ j.val by omega)
          have h2 := Nat.lt_mul_div_succ p.length hl
          nlinarith
        exact piece_after M p q a (j.val*l) l s hs hp
  have hsum := sum_le_sum (fun j (_ : j ∈ (univ : Finset (Fin b))) => hj j)
  rw [sum_add_distrib] at hsum
  have hc : (∑ j : Fin b, (if j.val = p.length/l then K else 0)) ≤ K := by
    rw [Fin.sum_univ_eq_sum_range (fun j => if j = p.length/l then K else 0) b,sum_ite_eq']
    split <;> linarith
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  dsimp [K] at hc hsum
  linarith

lemma lift_insert_raw (M : Model (List (Option A))) {D : ℝ} (hD : 0 ≤ D)
    (hM : ∀ u v, M.dist u v ≤ D*(indel u v : ℝ))
    (p q : List A) (a : A) (b l : ℕ) (hl : 0 < l) :
    (lift M b l).dist (p++q) (p++a::q) ≤
      16*(Nat.log 2 l+1 : ℕ)*(2*(b : ℝ)+4*Real.log (2*(l : ℝ)^2)*D) := by
  rw [lift_dist,sum_comm]
  have hscale (r : Fin (Nat.log 2 l+1)) : (∑ j : Fin b,
      piece M (p++q) (p++a::q) (j.val*l) l (2^r.val)) ≤
      2*(b : ℝ)+4*Real.log (2*(l : ℝ)^2)*D := by
    have hr := EditDyadic.scale_le hl r
    have hp : 0 < 2^r.val := pow_pos (by omega) _
    have h := sum_block_insert M hD hM p q a b l (2^r.val) hl hp hr
    apply h.trans
    have hrr : ((2^r.val : ℕ) : ℝ) ≤ l := by exact_mod_cast hr
    have hlog : Real.log (2*(((2^r.val : ℕ) : ℝ))^2) ≤ Real.log (2*(l : ℝ)^2) := by
      apply Real.log_le_log (by positivity)
      gcongr
    nlinarith
  calc
    _ ≤ 16 * ∑ _r : Fin (Nat.log 2 l+1), (2*(b : ℝ)+4*Real.log (2*(l : ℝ)^2)*D) :=
      mul_le_mul_of_nonneg_left (sum_le_sum (fun r _ => hscale r)) (by norm_num)
    _ = _ := by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

lemma model_indel_lipschitz (M : Model (List A)) {D : ℝ}
    (hstep : ∀ (p q : List A) (a : A), M.dist (p++q) (p++a::q) ≤ D) :
    ∀ x y, M.dist x y ≤ D*(indel x y : ℝ) := by
  have he {x y : List A} (h : Step false x y) : M.dist x y ≤ D := by
    cases h with
    | insert p q a => exact hstep p q a
    | delete p q a => rw [Model.dist_symm]; exact hstep p q a
    | substitute h => contradiction
  have hs {n : ℕ} {x y : List A} (h : Script false n x y) : M.dist x y ≤ D*(n : ℝ) := by
    induction h with
    | nil x => simp
    | @cons n x y z e h ih =>
      have ht := M.dist_triangle x y z
      have hh := he e
      push_cast
      nlinarith
  intro x y
  exact hs (cost_spec x y)

end EditUpper

end OAI
