import OAI.Analysis.FourierLLogL.Paths.Screen
/-! # The uniform output path -/

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section

namespace OAI

namespace FourierLLogL.Dyadic.Procedure.Paths
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Wire Pulse Thread Capture Chart Snapshot
variable {M j J : ℕ} {s q : Scene M} {f : Grid M → ℝ}
open scoped Classical


namespace Troupe
open Plot

/-- channel perturbation estimate. -/
private lemma ray_channel (A : Form M) (f : Grid M → ℂ) (x : Grid M) :
    (channel A x).Cx f = (label A).Cx fun z => f (x+z) := by
  apply Complex.ext
  · rw [re_Cx,re_Cx,ch_ex]
  · have H (P : Law (Grid M)) (f) : (P.Cx f).im=P.Ex (fun i => (f i).im) := by
      simp [Cx,Ex,Complex.im_sum]
    rw [H,H,ch_ex]

lemma duet_decode (s : Scene M) (v k : Grid M) :
    ∑ z, chi k z*letter s v z = (cred (dye s) k:ℂ)*scalar s (v+k) := by
  let A := dye s
  let L := channel A
  have HE (x : Grid M) :
      ∑ z, (L x z:ℂ)*chi k z=chi k x*(cred A k:ℂ) := by
    change (channel A x).Cx _=_
    rw [ray_channel,cred_eq]
    simp_rw [chi_add,Cx_lmul]
  unfold letter fz scalar; unfold omegaObs
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  let p : ℂ := ante s i
  calc
    _ = p*chi v i*∑ z,(L i z:ℂ)*chi k z := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun z _ => by unfold L p A ante; push_cast; ring
    _ = _ := by rw [HE i,chi_add']; unfold p ante A; ring

lemma gain_decode (s : Scene M) (v k : Grid M) :
    ∑ z, chi k z*factor s v z = (cred (dye s) k:ℂ)*gain s (v+k) := by
  unfold factor
  simp_rw [← mul_div_assoc,mul_sub]; rw [←Finset.sum_div,Finset.sum_sub_distrib,
    duet_decode,duet_decode,gain]
  simp only [dye,smaller]; ring

lemma energy_near_channel (s : Scene M) (h : Fit s) (v k : Grid M) :
    energy s v ≤ 2*energy s (v+k)+2*(share s*delta (dye s) k^2) := by
  let A := dye s; let P := channel A; let f := ante s
  let W (x y : Grid M) := f x * P x y
  let a := letter s v; let b := letter s (v+k)
  let m := matter s
  let T (x y : Grid M) := chi k x-chi k y
  let G (y : Grid M) := ∑ i,W i y* ‖T i y‖^2
  have hw (x y) : 0 ≤ W x y := mul_nonneg (ante_nonneg _ h.ready.2 h.pos.le _) ((P x).nonneg _)
  have H (z : Grid M) :
      b z-chi k z*a z = ∑ x, (W x z:ℂ)*(T x z*chi v x) := by
    unfold a b letter fz; rw [Finset.mul_sum,←Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => by
      rw [chi_add']
      unfold W T f P A ante omegaObs
      ring
  have HI (y) : ‖b y-chi k y*a y‖^2 / m y ≤ G y := by
    have HH : 0 ≤ m y := matter_nonneg h _
    rcases eq_or_lt_of_le HH with HH|HH
    · rw [←HH,div_zero]; exact Finset.sum_nonneg fun _ _ => mul_nonneg (hw _ _) (sq_nonneg _)
    apply (div_le_iff₀ HH).mpr
    rw [H y]
    have hi (x : Grid M) :
        ‖(W x y:ℂ)*(T x y*chi v x)‖= W x y* ‖T x y‖ := by
      rw [norm_scaleC,norm_mul,abs_of_nonneg (hw _ _),norm_chi,mul_one]
    apply le_trans (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) _)
    simp_rw [hi]
    have HX : m y=∑ x,W x y := rfl
    rw [HX]; unfold G
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _
      (fun i _ => mul_nonneg (hw _ _) (sq_nonneg _)) (fun i _ => hw _ _) (fun i _ => ?_)
    exact le_of_eq (by ring)
  have HB (x : Grid M) : ∑ y,P x y* ‖T x y‖^2=delta A k ^ 2 := by
    change (channel A x).Ex _=_
    rw [ch_ex]
    have he (z) : T x (x+z)=chi k x *(1-chi k z) := by unfold T; rw [chi_add]; ring
    simp_rw [he,norm_mul,norm_chi,one_mul]
    exact (sq_sqrt ((label A).Ex_nonneg fun i => sq_nonneg _)).symm
  have HL : ∑ z,G z=share s*delta A k ^ 2 := by
    unfold G; rw [Finset.sum_comm]
    simp_rw [W,mul_assoc,← Finset.mul_sum,HB]
    rw [← Finset.sum_mul,ante_total _ h.ready.1]
  unfold energy energyZ
  change ∑ z, ‖a z‖^2/m z ≤ 2*(∑ z, ‖b z‖^2/m z)+2*(share s*_)
  rw [show dye s=A from rfl,←HL, Finset.mul_sum, Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro z _
  have he : ‖a z‖ ≤ ‖b z‖+‖b z-chi k z*a z‖ := by
    have H := norm_sub_le (b z) (b z-chi k z*a z)
    rw [sub_sub_cancel,norm_mul,norm_chi,one_mul] at H; exact H
  have hev : ‖a z‖^2 ≤ 2*‖b z‖^2+2*‖b z-chi k z*a z‖^2 := by
    have H := pow_le_pow_left₀ (norm_nonneg _) he 2
    nlinarith [sq_nonneg (‖b z‖-‖b z-chi k z*a z‖)]
  apply le_trans (div_le_div_of_nonneg_right hev (matter_nonneg h _))
  rw [add_div,mul_div_assoc,mul_div_assoc]; linarith [HI z]

lemma near_size :
    ∀ᶠ j : ℕ in atTop,
      ∀ i : ℕ, i ≤ mainIx j → sepRad j ≤ side i ∧ 256*sig j ≤ side i^2 := by
  filter_upwards [h_large 1000] with j h i hi
  let a := Thermal.H j
  have H : 1/a^16 ≤ side i :=
    le_trans (bottom_level j).ge (pow_le_pow_of_le_one (by norm_num) (by norm_num) hi)
  have hx : 1000 ≤ a := h
  have hH : 1 ≤ a := by linarith
  change 1/a^30 ≤ _ ∧ 256*(1/a^40) ≤ _
  constructor
  · apply le_trans _ H; gcongr; omega
  · apply le_trans (b:=(1/a^16)^2) _ (pow_le_pow_left₀ (by positivity) H 2)
    have hv : a ≤ a^8 := by simpa using pow_le_pow_right₀ hH (by omega : 1≤8)
    field_simp; nlinarith

lemma node_compress {p q : Node} (h : p.below q) :
    p.len ≤ q.len := pow_le_pow_of_le_one (by norm_num) (by norm_num) h.1

lemma halo_limit {p : Scene M} (s : Scene M) (j i : ℕ) (main : Bool) (d : Grid M)
    (hh : s.here.below p.here) (h : rad d ≤ 2*spotLimit p j i main) :
    s.here.len*rad d ≤ 2*tolerance j i main := by
  calc
    _ ≤ p.here.len*(2*spotLimit p j i main) :=
      mul_le_mul (node_compress hh) h (rad_nonneg _) p.here.len_pos.le
    _ = _ := by rw [spotLimit,rinv]; field_simp [p.here.len_pos.ne']

/-- Combining errors after activation. First main interval may use b=1, then inner always. -/
lemma channel_inner :
    ∀ᶠ j : ℕ in atTop, ∀ (i : ℕ), i ≤ mainIx j → ∀ (M : ℕ)
    (p q : Scene M), q.here.below p.here → dye q=dye p → Climb q →
    ∀ u v k : Grid M, delta (dye p) k ≤ sepRad j →
      rad (u-v-k) ≤ 2*spotLimit p j i true →
        (0 < i → ¬ snag ⟨true,i-1⟩ u (⟨q,q,false⟩:Beat M)) →
        Run.Streak.innerV (rose ⟨true,i⟩ v) q := by
  filter_upwards [near_size] with j hj i hI M p q h1 h2 h u v k hx hk hp

  by_cases hi : i=0
  · subst i
    apply Or.inr; intro b
    let s := q.smaller b
    apply ((energy_small (h.child b) v).2.trans (h.child b).lift).trans
    change (4:ℝ) ≤ 64*side 0^2; norm_num [side]
  let A := rose ⟨true,i⟩ v
  apply or_iff_not_imp_left.mpr
  intro HH
  have hf := hp (Nat.pos_of_ne_zero hi)
  have HV (b : Bool) : energy (q.smaller b) u ≤ (2*side i)^2 := by
    have HH' : ¬ hazard q true (i-1) := fun hh => HH ⟨Nat.pos_of_ne_zero hi, hh⟩
    have Ht : energy (q.smaller b) u < side (i-1)^2 :=
      lt_of_not_ge fun hz => hf ⟨⟨b,hz⟩,HH'⟩
    have hc := side_succ (i-1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ i)] at hc
    rw [hc]; nlinarith
  intro b
  let s := q.smaller b
  have hS : below s.here p.here := below_trans (child_below _ _) h1
  let x := side i
  have HP := h.child b
  have H : energy s (v+k) ≤ energy s u+4*(16*s.here.len*rad (v+k-u)) :=
    magnitude_near true s (v+k) u HP.ready HP.pos.le 4 HP.lift
  rw [show v+k-u= -(u-v-k) by ring,rad_even] at H
  have he₁ : s.here.len*rad (u-v-k) ≤ 2*sig j :=
    halo_limit s j i true _ hS hk
  have hd := hj i hI
  have he₂ : delta (dye s) k^2 ≤ side i^2 := by
    change delta (dye q) k^2 ≤ _
    rw [h2]; exact pow_le_pow_left₀ (sqrt_nonneg _) (hx.trans hd.1) _
  change energy s v ≤ 64*side i^2
  have ht₁ : share s*delta (dye s) k^2 ≤ 4*(side i)^2 := by
    apply le_trans (mul_le_mul_of_nonneg_right HP.lift (sq_nonneg _)); nlinarith
  have hT : energy s u ≤ (2*side i)^2 := HV b
  nlinarith [energy_near_channel s HP v k, hd.2]

lemma gain_point {s : Scene M} (hp : Climb s)
    (u v x : Grid M) (hh : x∈s.here.block M) :
    ‖gain s u-chi (u-v) x*gain s v‖ ≤ 32*(s.here.len*rad (u-v)) := by
  let a B := scalar (s.smaller B) u- chi (u-v) x * scalar (s.smaller B) v
  let k := s.here.len*rad (u-v)
  have H (b : Bool) : ‖a b‖ ≤ 32*k := by
    have he := hp.child b
    apply (scalar_point _ u he.ready he.pos.le (child_below s.here b) x hh v).trans
    rw [mul_assoc 8]
    nlinarith [show 0 ≤ k from mul_nonneg s.here.len_pos.le (rad_nonneg _),he.lift]
  rw [show gain s u-chi (u-v) x*gain s v=(a false-a true)/2 by unfold gain a; ring]
  apply (norm_halfcomplex _ _).trans; linarith [H false,H true]

/-- big unlabelled coefficients force labelled high -/
lemma scalar_energy (s : Scene M) (h : Fit s) (u) :
    ‖scalar s u‖^2 ≤ 4*energy s u := by
  rw [scalar_label]
  apply le_trans (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) _)
  apply le_trans (b:=share s*energy s u)
  · rw [←matter_sum h,sun_energy h]
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun i _ => matter_nonneg h _)
      (fun i _ => (sun_rays h _ _).1) (fun i _ => ?_)
    rw [← (mean_hold _ h _ _).1,norm_scaleC,abs_of_nonneg (matter_nonneg h _)]
    unfold sun; exact le_of_eq (by ring)
  exact mul_le_mul_of_nonneg_right h.lift (energy_small h u).1

end Troupe


end FourierLLogL.Dyadic.Procedure.Paths

end OAI
