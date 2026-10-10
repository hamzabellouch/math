import OAI.Analysis.FourierLLogL.Plateau.Thread

/-! # Band-limited cutoffs -/
open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic.Procedure.Capture
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Wire Pulse
variable {M : ℕ}
open scoped Classical

def limit (f : Grid M → ℂ) (r : ℝ) := ∀ x, r < rad x → fc f x=0
def limitR (f : Grid M → ℝ) := limit (fun x => (f x:ℂ))

lemma limit_mul (f g : Grid M → ℂ) (p q : ℝ) (hf : limit f p) (hg : limit g q) :
    limit (fun x => f x*g x) (p+q) := by
  intro x hx; rw [fc_prod]; apply Finset.sum_eq_zero; intro i _
  by_cases hh : p < rad i
  · rw [hf i hh,zero_mul]
  have H : q < rad (x-i) := by
    have Hh := rad_add (x-i) i; rw [sub_add_cancel] at Hh
    linarith
  rw [hg _ H,mul_zero]
lemma limit_scale (f : Grid M → ℂ) (c : ℂ) (p : ℝ) (hf : limit f p) :
    limit (fun x => c*f x) p := by intro x hx; rw [fc_lmul,hf x hx,mul_zero]
lemma limit_const (p : ℝ) (hp : 0 ≤ p) : limit (M:=M) (fun _ => 1) p := by
  intro x hx; rw [← funext chi_zero_left,fc_chi,ite_eq_right]
  intro h; subst x; simp [rad] at hx; linarith

lemma limit_pow (f : Grid M → ℂ) (p : ℝ) (hf : limit f p) (k : ℕ) :
    limit (fun x => f x^k) (k*p) := by
  induction k with
  | zero => simpa only [Nat.cast_zero,zero_mul,pow_zero] using limit_const (M:=M) 0 le_rfl
  | succ k ih =>
    simp_rw [pow_succ,Nat.cast_add_one,add_mul,one_mul]
    exact limit_mul _ _ _ p ih hf
lemma limit_star (f : Grid M → ℂ) (p : ℝ) (hf : limit f p) :
    limit (fun x => conj (f x)) p := by
  intro x hx
  have hh : fc (fun x => conj (f x)) x = conj (fc f (-x)) := by
    unfold fc
    simp_rw [expU_cx,← Cx_conj,chi_neg', map_mul]
    simp
  rw [hh,hf _ (by rw [rad_even]; exact hx),map_zero]

/-- Dirichlet factor normalized to one. -/
private def tile (M d : ℕ) (x : Grid M) := (d:ℂ)⁻¹ * ∑ i∈Finset.range d, chi (i:Grid M) x
def slab (M d : ℕ) (x : Grid M) := ‖tile M d x‖^2

private lemma tile_limit (M d : ℕ) : limit (tile M d) d := by
  intro x hx
  unfold tile; rw [fc_lmul,fc_sum _ (fun i : ℕ => chi (i:Grid M))]
  suffices H : ∀ i ∈ Finset.range d, fc (chi (i:Grid M)) x=0 by simp [Finset.sum_eq_zero H]
  intro i hi; rw [fc_chi,ite_eq_right]
  intro h; subst x
  have H := rad_le_nat (M:=M) i
  have hi : (i:ℝ) < d := Nat.cast_lt.mpr (Finset.mem_range.mp hi)
  linarith

lemma slab_limit (M d : ℕ) : limitR (slab M d) (2*d) := by
  have hi (x : Grid M) : (↑(slab M d x):ℂ) =
      tile M d x * conj (tile M d x) := by rw [slab,Complex.mul_conj,Complex.sq_norm]
  have h := tile_limit M d
  unfold limitR; simp_rw [hi, two_mul]
  exact limit_mul _ _ _ _ h (limit_star _ _ h)

lemma slab_nonneg (M d : ℕ) (x : Grid M) : 0 ≤ slab M d x := by unfold slab; positivity

lemma slab_total (M : ℕ) (d : ℕ) (h : 0 < d) (he : d ≤ 2^M) :
    expU (slab M d) = (d:ℝ)⁻¹ := by
  change expU (fun x => ‖tile M d x‖^2) = _
  rw [← fc_parseval]
  have H (x : Grid M) : fc (tile M d) x = if x∈Dyadic.first M d then (d:ℂ)⁻¹ else 0 := by
    unfold tile; rw [fc_lmul,fc_sum _ (fun i : ℕ => chi (i:Grid M))]
    simp_rw [fc_chi]
    by_cases hx : x∈Dyadic.first M d
    · rw [ite_eq_left hx]
      rw [Finset.sum_eq_single x.val, ite_eq_left (ZMod.natCast_zmod_val _),mul_one]
      · intro j hj he'; rw [ite_eq_right]
        intro H
        have hi := ZMod.val_natCast_of_lt ((Finset.mem_range.mp hj).trans_le he)
        rw [H] at hi; exact he' hi.symm
      · exact fun HH => (HH (Finset.mem_range.mpr ((mem_first _ _).mp hx))).elim
    rw [first_eq_range d he] at hx
    rw [first_eq_range d he,ite_eq_right hx,Finset.sum_eq_zero,mul_zero]
    intro i hi; rw [ite_eq_right]; intro H; exact hx (Finset.mem_image.mpr ⟨_,hi,H⟩)
  simp_rw [H]
  calc
    _ = ∑ _x ∈ Dyadic.first M d, ((d:ℝ)⁻¹)^2 := by
      classical
      have hi (x : Grid M) :
          ‖(if x∈Dyadic.first M d then (d:ℂ)⁻¹ else 0)‖^2 =
            if x∈Dyadic.first M d then ((d:ℝ)⁻¹)^2 else 0 := by split_ifs <;> simp
      simp_rw [hi]; rw [← Finset.sum_filter]
      simp
    _ = _ := by simp [first_card d he]; field_simp

private lemma tile_lower (M d : ℕ) (h : 0 < d) (x : Grid M)
    (hx : Dyadic.diam x ≤ (1/16:ℝ)/d) :
    1/2 ≤ ‖tile M d x‖ := by
  have hp : 0 < (d:ℝ) := by positivity
  have hh := norm_phase_sq 1 x
  have ha : ‖1-chi 1 x‖ ≤ 8*Dyadic.diam x := by nlinarith [(cost_diam x).2,diam_nonneg x]
  have HF (i : ℕ) : ‖1-chi (i:Grid M) x‖ ≤ i*‖1-chi 1 x‖ := by
    induction i with
    | zero => simp [chi_zero_left]
    | succ i ih =>
      push_cast
      have Hx := norm_phase_add x (i:Grid M) 1
      rw [chi_comm x _,chi_comm x _,chi_comm x _] at Hx
      linarith
  have hE (i : ℕ) (hi : i < d) : ‖1-chi (i:Grid M) x‖ ≤ 1/2 := calc
    _ ≤ _ := HF i
    _ ≤ d*(8*Dyadic.diam x) := mul_le_mul (Nat.cast_le.mpr hi.le) ha (norm_nonneg _) hp.le
    _ ≤ _ := by have := (le_div_iff₀ hp).mp hx; linarith
  have hr (i : ℕ) (hi : i < d) : 1/2 ≤ (chi (i:Grid M) x).re := by
    have H := Complex.abs_re_le_norm (1-chi (i:Grid M) x); simp only [Complex.sub_re,Complex.one_re] at H
    linarith [(abs_le.mp (H.trans (hE i hi))).2]
  apply le_trans (b:=(tile M d x).re)
  · unfold tile; rw [show (d:ℂ)⁻¹=(↑((d:ℝ)⁻¹):ℂ) by push_cast; rfl,
       Complex.re_ofReal_mul,Complex.re_sum,← div_eq_inv_mul]
    apply (le_div_iff₀ hp).mpr
    have HH := Finset.sum_le_sum (s:=Finset.range d) fun i hi => hr i (Finset.mem_range.mp hi)
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at HH; linarith
  exact (le_abs_self _).trans (Complex.abs_re_le_norm _)


private lemma tile_upper (M d : ℕ) (h : 0 < d) (x : Grid M) :
    (4*d:ℝ)*Dyadic.diam x * ‖tile M d x‖ ≤ 2 := by
  let z := chi (1:Grid M) x
  have he (i : ℕ) : z ^ i = chi (i:Grid M) x := by unfold z; rw [← chi_nsmul,nsmul_one]
  have H : ‖1-z‖ * (d:ℝ)* ‖tile M d x‖ ≤ 2 := by
    let W := ∑ i∈Finset.range d,z^i
    have HH := geom_sum_mul_neg z d
    have HB : ‖W*(1-z)‖ ≤ 2 := by
      rw [show W*(1-z)=_ from HH]
      apply (norm_sub_le _ _).trans; rw [norm_pow,norm_one,show ‖z‖=1 from norm_chi _ _]; simp
      norm_num
    rw [norm_mul] at HB
    have Hp : 0 < (d:ℝ) := by positivity
    have hz : ‖tile M d x‖ = (d:ℝ)⁻¹*‖W‖ := by
      unfold tile W; simp_rw [he, norm_mul,norm_inv]; simp
    rw [hz]
    apply le_trans _ HB; exact le_of_eq (by field_simp)
  have he₁ := (cost_diam x).1
  have He : 4*Dyadic.diam x ≤ ‖1-z‖ := by unfold z; nlinarith [norm_phase_sq 1 x,norm_nonneg (1-chi 1 x)]
  apply le_trans _ H
  have hp : 0 ≤ (d:ℝ) := by positivity
  rw [mul_right_comm (4:ℝ)]; gcongr

open Node

lemma boosted (M d k : ℕ) (h : 0 < d) (he : d ≤ 2^M) :
    ∃ P : Law (Grid M), limitR P (2*(d:ℝ)*(k+10)) ∧
      P.prob (fun x => 16/d ≤ Dyadic.diam x) ≤ side k := by
  let n := k+10
  let f (x : Grid M) := slab M d x^n
  let a := ∑ x, f x
  have hh : (0:ℝ)<d := Nat.cast_pos.mpr h
  let b := side M
  have hb : 0 < b := side_pos M
  have hf (x) : 0 ≤ f x := pow_nonneg (slab_nonneg _ _ _) _
  let r := ((1/16:ℝ)/d)/b
  have hr : 0 ≤ r := by unfold r; positivity
  have heR : r ≤ 2^M := by
    unfold r; apply (div_le_iff₀ hb).mpr
    rw [show (2:ℝ)^M*b=1 by unfold b; rw [mul_comm,side_card]]
    have H : 1 ≤ (d:ℝ) := by exact_mod_cast h
    apply (div_le_one hh).mpr; linarith
  let D := arc M r
  have Hlow (x) (hx : x∈D) : (1/4:ℝ)^n ≤ f x := by
    apply pow_le_pow_left₀ (by norm_num : 0 ≤ (1/4:ℝ))
    have HI : Dyadic.diam x ≤ (1/16:ℝ)/d := by
      have HI := (mem_arc r _).mp hx
      rw [diam,mul_comm]
      exact (le_div_iff₀ hb).mp HI
    unfold slab
    have HE := tile_lower M d h x HI; nlinarith
  have HD : r ≤ (D.card:ℝ) := arc_card_lo M r hr heR
  have HG : r*(1/4:ℝ)^n ≤ a := calc
    _ ≤ D.card*(1/4:ℝ)^n := by gcongr
    _ = ∑ _i∈D,(1/4:ℝ)^n := by simp
    _ ≤ ∑ i∈D,f i := Finset.sum_le_sum Hlow
    _ ≤ ∑ i,f i := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hf i)
  have ha : 0 < a := lt_of_lt_of_le (by unfold r; positivity) HG
  let P := proportional f hf ha
  refine ⟨P,?_,?_⟩
  · have He : limitR f (n*(2*d):ℝ) := by
      unfold limitR f; simp_rw [Complex.ofReal_pow]; exact limit_pow _ _ (slab_limit M d) _
    unfold limitR
    have HE (x : Grid M) : P x = a⁻¹ * f x := by unfold P; rw [proportional_apply,div_eq_inv_mul]
    simp_rw [HE,Complex.ofReal_mul]
    rw [show 2*(d:ℝ)*(k+10) = n*(2*d) by unfold n; push_cast; ring]
    exact limit_scale _ _ _ He
  · let t (x : Grid M) := (16/d:ℝ) ≤ Dyadic.diam x
    have Ht (x : Grid M) (hx : t x) : slab M d x ≤ 1/16 := by
      unfold slab
      have Hx := tile_upper M d h x
      have HH := (div_le_iff₀ hh).mp hx
      generalize HE : ‖tile M d x‖ = w at *
      have hw : 0 ≤ w := HE ▸ norm_nonneg _
      nlinarith [mul_le_mul_of_nonneg_right HH hw]
    let A := (1/16:ℝ)^(k+9)
    have HI :
        ∑ x, (if t x then f x else 0) ≤ A*(∑ x : Grid M, slab M d x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro i hi
      have hip := slab_nonneg M d i
      split_ifs with H
      · apply le_trans (b:=slab M d i^(k+9)*slab M d i)
        · unfold f n; rw [show k+10=k+9+1 from rfl,pow_succ]
        unfold A; gcongr; exact Ht i H
      unfold A; positivity
    have HT (x : Grid M) : P x=f x/a := proportional_apply f hf ha _
    rw [prob_eq]; simp_rw [HT]
    have HH (i : Grid M) : (if t i then f i/a else 0) = (if t i then f i else 0)/a := by
      split_ifs <;> simp
    change (∑ i, if t i then f i / a else 0) ≤ side k
    simp_rw [HH, ← Finset.sum_div]
    apply (div_le_iff₀ ha).mpr
    have H := slab_total M d h he
    change b* (∑ x : Grid M, slab M d x) = _ at H
    calc
      _ ≤ _ := HI
      _ ≤ side k * (r*(1/4:ℝ)^n) := by
        apply le_of_mul_le_mul_left ?_ hb
        rw [mul_left_comm b, H]
        unfold r n
        have he : b*(side k*(1/16/d/b*(1/4:ℝ)^(k+10))) =
            (d:ℝ)⁻¹*((1/16)*(side k*(1/4:ℝ)^(k+10))) := by field_simp
        rw [he]
        unfold A
        apply le_trans (le_of_eq (mul_comm _ _)) (mul_le_mul_of_nonneg_left ?_ (by positivity))
        unfold side
        rw [pow_add, pow_add]
        have hh : (1/16:ℝ)^k ≤ (1/2:ℝ)^k*(1/4:ℝ)^k := by rw [← mul_pow]; norm_num; gcongr; norm_num
        norm_num at *; nlinarith [show 0 ≤ (1/16:ℝ)^k by positivity]
      _ ≤ _ := mul_le_mul_of_nonneg_left HG (side_pos _).le
end FourierLLogL.Dyadic.Procedure.Capture

end OAI
