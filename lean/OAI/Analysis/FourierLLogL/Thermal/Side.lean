import OAI.Analysis.FourierLLogL.Thermal.Bias

/-! # Accounting for the side label -/
open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic.Thermal
open Law Node Real Period

variable {M l : ℕ}

lemma cert_S_energy {n : ℕ} {p : Node} {h err : ℝ} {A : Form M} (H : Certified h err n p A) :
    (label A).Ex (form (place p M)) ≤ 100 := by
  rcases H.prev with ⟨he,_⟩ | he
  · subst p
    refine le_trans (b:=(label A).Ex (fun _ => 2)) (Ex_mono _ fun x => ?_)
      (by rw [Ex_const]; norm_num)
    rw [place, invlen_top, form_S]; simp [(cost_bounds 1 x).2]
  exact S_energy _ p.invlen_ge (loc_scale H.fits.2) A he

lemma local_channel_energy {n : ℕ} {p : Node} {h err : ℝ} {A : Form M}
    (H : Certified h err n p A) (x : Grid M) (hx : x ∈ p.block M) :
    (channel A x).Ex (fun z => form (place p M) (z-start p M)) ≤ 264 := by
  let P := label A
  let B := place p M
  let t := start p M
  rw [ch_ex]
  change P.Ex (fun z => form B (x+z-t)) ≤ _
  calc
    _ ≤ P.Ex (fun z => 2*(form B z+form B (x-t))) := Ex_mono _ fun z => by
      rw [show x+z-t=z+(x-t) by ring]
      exact form_triangle (place_valid _ _) _ _
    _ ≤ _ := by
      rw [Ex_lmul,Ex_add (g:=fun _ => form B (x-t)),Ex_const]
      have hh : P.Ex (form B) ≤ 100 := cert_S_energy H
      have he : form B (x-t) ≤ 32 := place_internal hx (start_mem H.fits.1 H.fits.2)
      linarith

/-- Absolute information cap wrt a fixed comparison law on z. -/
lemma side_entropy {n : ℕ} {p : Node} {h err : ℝ} {A : Form M}
    (H : Certified h err n p A) (x : Grid M) (hx : x ∈ p.block M) :
    (channel A x).Ex (fun z => log (channel A x z) -
      log (channel (place p M) (p.start M) z)) ≤ F A-log p.invlen+300 := by
  let B := place p M
  let t := start p M
  let P := channel A x
  refine le_trans (b:=P.Ex (fun z => F A-F B+form B (z-t))) (Ex_mono _ fun z => ?_) ?_
  · change log (channel A x z) - log (channel B t z) ≤ _
    rw [ch_K,ch_K, log_mul (side_pos _).ne' (K_pos _ _).ne',
      log_mul (side_pos _).ne' (K_pos _ _).ne', K_eq, K_eq,log_exp,log_exp]
    linarith [form_nonneg H.nonneg (z-x)]
  · rw [Ex_add,Ex_const]
    have he := local_channel_energy H x hx
    have hi : log p.invlen-12 ≤ F B :=
      F_S_lower _ p.invlen_pos (loc_scale H.fits.2)
    unfold P B t at *; linarith

lemma log_input_bound {p : Node} (hp : p.ok M) {a : Grid M → ℝ}
    {P : Law (Grid M)} (h : PieceLaw p a P) {d : ℝ} (h1 : ∀ x, a x ≤ exp d)
    (hm : exp (-d) ≤ p.avg a) (x : Grid M) (hx : 0 < P x) :
    log (P x) ≤ 2*d+log (side M)+log p.invlen := by
  have Hi := piece_support hp h _ hx
  have H := log_le_log hx (piece_density h h1 hm x)
  rw [dice_apply hp,ite_eq_left Hi,← rinv] at H
  rw [log_mul (exp_pos _).ne' (by have := side_pos M; have := p.invlen_pos; positivity),
    log_mul (side_pos _).ne' p.invlen_pos.ne', log_exp] at H
  linarith

open scoped Classical

private lemma cut_sum_bound (hp : l ≤ M) {p : Node} (hv : p.ok M) (hh : M-l ≤ p.lev)
    (f : Grid l → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ p.group M, f (cut hp x) ≤ ∑ x, f x := by
  rw [← Finset.sum_image (s:=p.group M)]
  · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => hf x)
  intro x hx y hy he
  exact cut_injOn hp hv.2 hh ((mem_group _ _).mp hx) ((mem_group _ _).mp hy) he

lemma log_side_ratio (hl : l ≤ M) : log (side M)-log (side l) = -log ((2:ℝ)^(M-l)) := by
  simp_rw [side_pow_two, Real.log_inv]
  simp_rw [Real.log_pow]
  rw [Nat.cast_sub hl]
  ring

/-- General positive-product estimate. The extra factor of two in the testing volume
allows a predictable child mask. -/
lemma product_entropy_bound {p p' : Node} {a : Grid M → ℝ} (hp : p.ok M) (hv : p.below p')
    {n : ℕ} {h err : ℝ} {A : Form M} (H : Certified h err n p' A)
    {P : Law (Grid M)} (ht : PieceLaw p a P) (hl : l ≤ M) (hh : M-l ≤ p.lev)
    {d : ℝ} (h1 : ∀ x, a x ≤ exp d) (hm : exp (-d) ≤ p.avg a) (B : Bool)
    (Q : Grid l → Grid M → ℝ) (hQ : ∀ x z, 0 < Q x z)
    (hQ' : ∀ z, expU (fun x => Q x z) ≤ 1) :
    (P.withNext (channel A)).Ex (fun xz => if xz.1∈(p.child B).block M then
      log (Q (cut hl xz.1) xz.2) else 0) ≤
        2*d + log p.invlen - log ((2:ℝ)^(M-l)) + F A - log p'.invlen + 301 := by
  classical
  let C (x : Grid M) : Prop := x ∈ (p.child B).block M
  let T (x z : Grid M) := if C x then Q (cut hl x) z else 1
  have hT (x z) : 0 < T x z := by unfold T; split_ifs; exact hQ _ _; norm_num
  let L := channel (place p' M) (p'.start M)
  let v (xz : Grid M × Grid M) := if xz.1∈p.block M then side l * (L xz.2 * T xz.1 xz.2)/2 else 0
  have hvL (z) : 0 < L z := ch_pos _ _ _
  have hvV (xz) : 0 ≤ v xz := by
    unfold v; split_ifs
    · have := side_pos l; have := hvL xz.2; have := hT xz.1 xz.2; positivity
    · exact le_rfl
  have hcV : ∑ xz, v xz ≤ 1 := by
    rw [Fintype.sum_prod_type,Finset.sum_comm,← L.total]
    refine Finset.sum_le_sum fun z _ => ?_
    have he : ∑ x ∈ p.group M, side l * T x z ≤ 2 :=
      calc
        _ ≤ ∑ x ∈ p.group M, side l * (1+Q (cut hl x) z) :=
          Finset.sum_le_sum fun x hx => by
            apply mul_le_mul_of_nonneg_left _ (side_pos _).le
            unfold T; split_ifs
            · linarith
            · linarith [hQ (cut hl x) z]
        _ ≤ ∑ x, side l * (1+Q x z) := cut_sum_bound hl hp hh (fun x => side l*(1+Q x z))
          (fun x => by have := side_pos l; have := hQ x z; positivity)
        _ ≤ _ := by
          rw [← Finset.mul_sum]
          change expU (fun x => 1+Q x z) ≤ _
          rw [expU_ex,Ex_add,Ex_const,← expU_ex]
          linarith [hQ' z]
    have hA : (p.group M)=Finset.univ.filter fun x => x∈p.block M := by ext x; simp [mem_group]
    calc
      _ = (L z / 2) * (∑ x ∈ p.group M, side l*T x z) := by
        unfold v; rw [Finset.mul_sum,hA,Finset.sum_filter]
        refine Finset.sum_congr rfl fun x _ => ?_
        split_ifs <;> ring
      _ ≤ _ := by nlinarith [hvL z]
  let U := P.withNext (channel A)
  have hUS (x z : Grid M) (hx : 0 < U (x,z)) : 0 < P x := by
    rw [show U (x,z) = P x * channel A x z from rfl] at hx
    exact pos_of_mul_pos_left hx (ch_pos _ _ _).le
  have hhV (xz : Grid M × Grid M) (hx : 0 < U xz) : 0 < v xz := by
    obtain ⟨x,z⟩ := xz
    change 0 < if x∈p.block M then _ else _
    rw [ite_eq_left (piece_support hp ht _ (hUS x z hx))]
    have := side_pos l; have := hvL z; have := hT x z; positivity
  have He := entropy_le_cross_aux U v hvV hcV hhV
  unfold entropy crossE at He
  simp_rw [Ex_neg] at He
  let f := fun xz : Grid M × Grid M => log (P xz.1)
  let g := fun xz : Grid M × Grid M => log (channel A xz.1 xz.2)-log (L xz.2)
  let W := fun xz : Grid M × Grid M => if xz.1∈(p.child B).block M then
    log (Q (cut hl xz.1) xz.2) else 0
  have hE : U.Ex W ≤ U.Ex f + U.Ex g + log 2-log (side l) := by
    have Hx (p0 : Grid M × Grid M) (hx : 0 < U p0) :
      W p0 = f p0+g p0+(log 2-log (side l)) + (log (v p0)-log (U p0)) := by
      obtain ⟨x,z⟩ := p0
      have hx' := hUS x z hx
      unfold W f g v; dsimp
      rw [ite_eq_left (piece_support hp ht _ hx')]
      change (if x∈_ then _ else _) = log (P x)+_+_+(log (side l*(L z*T x z)/2)-log (P x * channel A x z))
      rw [Real.log_div (by have := side_pos l; have := hvL z; have := hT x z; positivity) (by norm_num),
        log_mul (side_pos _).ne' (mul_pos (hvL _) (hT _ _)).ne',
        log_mul (hvL z).ne' (hT _ _).ne',
        log_mul hx'.ne' (ch_pos _ _ _).ne']
      unfold T C; split_ifs
      · ring
      rw [log_one]; ring
    rw [Ex_congr_mem _ Hx]
    simp_rw [Ex_add,Ex_sub,Ex_const]
    linarith
  have Hf : U.Ex f ≤ 2*d+log (side M)+log p.invlen := by
    unfold U f
    simp_rw [Ex_withNext,Ex_const]
    rw [← Ex_const P (2*d+log (side M)+log p.invlen)]
    exact Ex_mono_mem _ (log_input_bound hp ht h1 hm)
  have Hg : U.Ex g ≤ F A-log p'.invlen+300 := by
    unfold U g
    rw [Ex_withNext,← Ex_const P (F A-log p'.invlen+300)]
    exact Ex_mono_mem _ fun x hx => side_entropy H x (block_of_below hv M (piece_support hp ht _ hx))
  have Ht := log_side_ratio hl
  change U.Ex W ≤ _
  linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]

end FourierLLogL.Dyadic.Thermal

end OAI
