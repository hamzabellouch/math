import OAI.Analysis.FourierLLogL.Thermal.Shrink
import OAI.Analysis.FourierLLogL.Thermal.Bias

/-! # Gap of a metric ball -/
open Function Set Filter
open scoped Topology BigOperators ComplexConjugate Pointwise
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic.Thermal
open Law Node Real Period

variable {M l : ℕ}
open scoped Classical

def gap (A : Form M) (r : ℝ) := F A - log ((ball A r).card)

lemma ball_pos (A : Form M) {r : ℝ} (hr : 0 ≤ r) : (0:ℝ) < (ball A r).card := by
  exact_mod_cast Finset.card_pos.mpr ⟨0,(mem_ball A r 0).mpr (by rw [delta_zero]; exact hr)⟩

lemma gap_zero {r : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1) :
    gap (0:Form M) r = 0 := by
  have H : ball (0:Form M) r = {0} := by
    ext x; simp only [mem_ball,Finset.mem_singleton]
    constructor
    · intro hx
      by_contra hh
      have HE := delta_sq (0:Form M) x
      have HQ : q (0:Form M) x = 0 := by
        unfold q fc
        simp_rw [boltz,form_zero,neg_zero,exp_zero,Complex.ofReal_one,one_mul,expU_chi]
        simp [hh]
      rw [cred,HQ,zero_div] at HE
      have h1 : 0 ≤ delta (0:Form M) x := sqrt_nonneg _
      nlinarith
    · rintro rfl; rw [delta_zero]; exact hr
  simp [gap,F_zero,H]

lemma half_q_ball (A : Form M) (x : Grid M) (h : delta A x ≤ 1) :
    q A 0 /2 ≤ q A x := by
  have hi : (1/2:ℝ) ≤ cred A x := by
    have hx : 0 ≤ delta A x := sqrt_nonneg _
    nlinarith [delta_sq A x]
  nth_rw 2 [q_express]
  rw [F_origin]
  nlinarith [q_origin_pos A]

lemma gap_lower {A : Form M} (hA : 0 ≤ A) {r : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1) :
    -2 ≤ gap A r := by
  let s := ball A r
  have hi : s.card * q A 0 /2 ≤ 1 := calc
    _ = ∑ _u∈s, q A 0 /2 := by simp; ring
    _ ≤ ∑ u∈s, q A u := Finset.sum_le_sum fun i hi => half_q_ball A i (((mem_ball _ _ _).mp hi).trans hr')
    _ ≤ ∑ u : Grid M, q A u := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun _ _ _ => q_nonneg hA _)
    _ = 1 := q_total _
  have hp : 0 < (s.card:ℝ) := ball_pos _ hr
  have hh := Real.log_le_log (mul_pos hp (q_origin_pos A)) (y:=2) (by linarith)
  rw [log_mul hp.ne' (q_origin_pos A).ne'] at hh
  change -2 ≤ -log (q A 0)-log (s.card:ℝ)
  linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]

private lemma overlap_bound (U D : Finset (Grid M)) :
    U.card*D.card ≤ (U+D).card*((U-U)∩(D-D)).card := by
  classical
  let V := U ×ˢ D
  let f : Grid M × Grid M → Grid M := fun v => v.1+v.2
  have hV : MapsTo f V (↑(U+D):Set (Grid M)) := fun i hi =>
    Finset.add_mem_add (Finset.mem_product.mp hi).1 (Finset.mem_product.mp hi).2
  let L := (U-U)∩(D-D)
  have hi (i : Grid M) (hh : i ∈ U+D) : (V.filter fun v => f v=i).card ≤ L.card := by
    obtain ⟨x,hx,y,hy,rfl⟩ := Finset.mem_add.mp hh
    let g : Grid M × Grid M → Grid M := fun i => i.1-x
    apply Finset.card_le_card_of_injOn g
    · rintro ⟨t,v⟩ ht
      obtain ⟨hh,h⟩ := Finset.mem_filter.mp ht
      obtain ⟨hh1,hh2⟩ := Finset.mem_product.mp hh
      change t+v=x+y at h
      have he : t-x=y-v := by linear_combination h
      exact Finset.mem_inter.mpr ⟨Finset.sub_mem_sub hh1 hx,by dsimp [g]; rw [he]; exact Finset.sub_mem_sub hy hh2⟩
    · rintro ⟨t,v⟩ ht ⟨b,c⟩ hs H
      have H1 := (Finset.mem_filter.mp ht).2
      have H2 := (Finset.mem_filter.mp hs).2
      change t-x=b-x at H
      dsimp only [f] at H1 H2
      have hh : t=b := sub_left_inj.mp H
      have he : v=c := add_left_cancel (hh ▸ H1.trans H2.symm)
      rw [hh,he]
  rw [← Finset.card_product]
  change V.card ≤ _
  calc
    _ = ∑ i ∈ U+D, (V.filter (fun v => f v=i)).card := Finset.card_eq_sum_card_fiberwise hV
    _ ≤ ∑ _i∈U+D, L.card := Finset.sum_le_sum hi
    _ = _ := by simp [L]

lemma delta_diff {A : Form M} {r : ℝ} {x y : Grid M} (hx : x∈ball A r)
    (hy : y∈ball A r) : delta A (x-y) ≤ 2*r := by
  rw [sub_eq_add_neg]; apply le_trans (delta_triangle _ _ _)
  rw [delta_even _ y]
  linarith [(mem_ball _ _ _).mp hx,(mem_ball _ _ _).mp hy]
lemma rad_diff {r : ℝ} {x y : Grid M} (hx : x∈arc M r) (hy : y∈arc M r) :
    rad (x-y) ≤ 2*r := by
  rw [sub_eq_add_neg]; apply le_trans (rad_add _ _)
  rw [rad_even]
  linarith [(mem_arc _ _).mp hx,(mem_arc _ _).mp hy]

private lemma log_pair {p : Node} (hp : p.ok M) {r σ : ℝ} (hr : 0 ≤ r) (hr' : 2*r ≤ 1)
    (hs : 0 < σ) (hs' : σ ≤ 1/4) {A : Form M} (hA : 0 ≤ A) :
    let U := ball A r
    let D := arc M (σ*p.invlen/10)
    F (A+place p M)-F A + log (U.card:ℝ) ≤ log ((U+D).card:ℝ) + 130 - log σ := by
  intro U D
  let R := p.invlen; let d := σ*R/10
  let B := place p M
  let L := (U-U)∩(D-D)
  have hR : 0 < R := p.invlen_pos
  have hd : 0 < d := by unfold d; positivity
  have hDD : d ≤ ↑D.card := by
    have HE := loc_scale hp.2
    change R ≤ _ at HE
    apply arc_card_lo M _ hd.le
    unfold d; nlinarith
  have h₁ : (0:ℝ)< U.card := ball_pos _ hr
  have h₂ : (0:ℝ)< D.card := hd.trans_le hDD
  have hU : 0∈U := (mem_ball _ _ _).mpr (by rw [delta_zero]; exact hr)
  have hD : 0∈D := by
    apply (mem_arc _ _).mpr
    simpa only [rad, ZMod.val_zero,neg_zero,min_self,Nat.cast_zero] using hd.le
  have hL : (0:Grid M)∈L :=
    Finset.mem_inter.mpr ⟨by simpa using Finset.sub_mem_sub hU hU,
      by simpa using Finset.sub_mem_sub hD hD⟩
  have h₃ : (0:ℝ) < L.card := by exact_mod_cast Finset.card_pos.mpr ⟨0,hL⟩
  have h₄ : (0:ℝ) < (U+D).card := by
    exact_mod_cast Finset.card_pos.mpr ⟨_,Finset.add_mem_add hU hD⟩
  have hi (x : Grid M) (hi : x∈L) :
      q A 0 * ((1/120)/R) ≤ q A x * q B (-x) := by
    obtain ⟨hx,hy⟩ := Finset.mem_inter.mp hi
    have h1 : delta A x ≤ 1 := by
      obtain ⟨u,hu,v,hv,rfl⟩ := Finset.mem_sub.mp hx
      exact (delta_diff hu hv).trans hr'
    have h2 : rad x ≤ R/20 := by
      obtain ⟨u,hu,v,hv,rfl⟩ := Finset.mem_sub.mp hy
      have hh : rad (u-v) ≤ 2*d := rad_diff hu hv
      unfold d at hh; nlinarith
    calc
      _ = q A 0 /2 * ((1/60:ℝ)/R) := by ring
      _ ≤ q A x * q B x := mul_le_mul (half_q_ball _ _ h1)
        (q_short R p.invlen_ge (loc_scale hp.2) x h2)
        (by positivity) (q_nonneg hA _)
      _ = _ := by rw [q_even _ _]
  have H : L.card * (q A 0 * ((1/120:ℝ)/R)) ≤ q (A+B) 0 := calc
    _ = ∑ i∈L, q A 0*((1/120:ℝ)/R) := by simp
    _ ≤ ∑ i∈L, q A i*q B (-i) := Finset.sum_le_sum hi
    _ ≤ ∑ i, q A i*q B (-i) := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun _ _ _ => mul_nonneg (q_nonneg hA _) (q_nonneg (place_valid _ _) _))
    _ = _ := by simp_rw [q_add,zero_sub]
  have HH : (U.card:ℝ)*D.card ≤ (U+D).card*(L.card:ℝ) := by exact_mod_cast overlap_bound U D
  have H₁ := log_le_log (mul_pos h₁ h₂) HH
  have H₂ := log_le_log (show 0 < (L.card:ℝ)*(q A 0*((1/120:ℝ)/R)) by
    have := q_origin_pos A; positivity) H
  have H₃ := log_le_log hd hDD
  rw [Real.log_mul h₁.ne' h₂.ne',Real.log_mul h₄.ne' h₃.ne'] at H₁
  rw [Real.log_mul h₃.ne' (by have := q_origin_pos A; positivity),
    Real.log_mul (q_origin_pos _).ne' (by positivity), Real.log_div (by norm_num) hR.ne',
    Real.log_div (by norm_num) (by norm_num), Real.log_one] at H₂
  unfold d at H₃
  rw [Real.log_div (by positivity) (by norm_num),Real.log_mul hs.ne' hR.ne'] at H₃
  unfold F; change -log (q (A+B) 0) - _ + _ ≤ _
  linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<120),
    log_le_sub_one_of_pos (by norm_num : (0:ℝ)<10)]

lemma gap_packing {p : Node} (hp : p.ok M) {r σ η : ℝ} (hr : 0 ≤ r) (hr' : 2*r ≤ 1)
    (hs : 0 < σ) (hs' : σ ≤ 1/4) (he : 4*σ ≤ η) {A C : Form M} (hA : 0 ≤ A)
    (hC : A+place p M ≤ C) (f : Grid l → Grid M) (s : Finset (Grid l)) (hn : s.Nonempty)
    (h : separated f A (2*r) (σ*p.invlen/2) s)
    (hc : ∀ x∈s, delta C (f x) ≤ η/2) :
    gap C (r+η) - gap A r ≤ F C - F (A+place p M) + 130 - log σ - log (s.card:ℝ) := by
  let U := ball A r; let R := p.invlen; let d := σ*R/10; let D := arc M d
  have he' : 0 < η := by linarith
  let W := U+D
  have hR : 0 < R := p.invlen_pos
  have hD : 0 ∈ D := by
    apply (mem_arc _ _).mpr
    simp [rad]
    unfold d; positivity
  have hU : 0∈U := (mem_ball _ _ _).mpr (by rw [delta_zero]; exact hr)
  have hW : 0 ∈ W := by simpa using Finset.add_mem_add hU hD
  have hB := ball_pos C (show 0 ≤ r+η by linarith)
  have hsW : 0 < (W.card:ℝ) := by exact_mod_cast Finset.card_pos.mpr ⟨_,hW⟩
  have hC1 : place p M ≤ C := (le_add_of_nonneg_left hA).trans hC
  have hC2 : A ≤ C := (le_add_of_nonneg_right (place_valid _ _)).trans hC
  let F' : Grid l × Grid M → Grid M := fun i => f i.1+i.2
  have ha : s.card*W.card ≤ (ball C (r+η)).card := by
    rw [← Finset.card_product]
    apply Finset.card_le_card_of_injOn F'
    · rintro ⟨i,j⟩ hi
      obtain ⟨hi,hj⟩ := Finset.mem_product.mp hi
      obtain ⟨u,hu,v,hv,rfl⟩ := Finset.mem_add.mp hj
      apply (mem_ball _ _ _).mpr
      have h1 := hc i hi
      have hV : delta C u ≤ r := (delta_mono hA hC2 _).trans ((mem_ball _ _ _).mp hu)
      have hV' : delta C v ≤ η/2 := by
        have ht := delta_S R p.invlen_ge (loc_scale hp.2) _ hC1 v
        have hQ := (mem_arc _ _).mp hv
        exact ht.trans (by
          calc
            _ ≤ d * (20/R) := mul_le_mul_of_nonneg_right hQ (by positivity)
            _ = 2*σ := by unfold d; field_simp; ring
            _ ≤ _ := by linarith)
      change delta C (f i + (u+v)) ≤ _
      linarith [delta_triangle C u v,delta_triangle C (f i) (u+v)]
    · rintro ⟨i,j⟩ hi ⟨x,y⟩ hj HH
      obtain ⟨hi,hv⟩ := Finset.mem_product.mp hi
      obtain ⟨hx,hy⟩ := Finset.mem_product.mp hj
      change f i + j=f x+y at HH
      have Hx : i=x := by
        by_contra hh
        apply h i hi x hx hh
        obtain ⟨u,hu,t,ht,rfl⟩ := Finset.mem_add.mp hv
        obtain ⟨v,hv,q,hq,rfl⟩ := Finset.mem_add.mp hy
        refine ⟨v-u,delta_diff hv hu,?_⟩
        rw [show f i-f x-(v-u)=q-t by linear_combination HH]
        change _ ≤ σ*R/2
        have hE : rad (q-t) ≤ 2*d := rad_diff hq ht
        unfold d at hE; nlinarith
      subst x; rw [add_right_inj] at HH
      simp [HH]
  have h1 : (s.card:ℝ)*W.card ≤ (ball C (r+η)).card := by exact_mod_cast ha
  have hV : (0:ℝ) < s.card := by exact_mod_cast Finset.card_pos.mpr hn
  have H := log_le_log (mul_pos hV hsW) h1
  rw [log_mul hV.ne' hsW.ne'] at H
  have H' := log_pair hp hr hr' hs hs' hA
  change _ + log (U.card:ℝ) ≤ log (W.card:ℝ)+130-_ at H'
  unfold gap; change F C-_-(F A-log (U.card:ℝ)) ≤ _
  linarith

end FourierLLogL.Dyadic.Thermal

end OAI
