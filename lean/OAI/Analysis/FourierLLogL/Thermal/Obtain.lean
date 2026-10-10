import OAI.Analysis.FourierLLogL.Thermal.Levels
import OAI.Analysis.FourierLLogL.Thermal.Tilted
import OAI.Analysis.FourierLLogL.Thermal.Shrink

/-! # Obtaining the compressed set with available volume -/
open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic.Thermal
open Law Node Real Period Compress.Params

variable {M l : ℕ}
open scoped Classical

def reserve (C : ℝ) := C+20
def codeWeight (C : ℝ) := 100000000*reserve C
lemma reserve_ge {C : ℝ} (h : 1 ≤ C) : 1 ≤ reserve C := by unfold reserve; linarith
lemma code_ge {C : ℝ} (h : 1 ≤ C) : 1 ≤ codeWeight C := by unfold codeWeight reserve; linarith

lemma log_mesh (j : ℕ) {p : Node} (hp : p.lev ≤ M) :
    log p.invlen - log ((2:ℝ)^(M-snapGrid j p M)) ≤ 1000*H j := by
  let E : ℝ := 2^(M-snapGrid j p M)
  have hx : p.invlen ≤ 64*H j^40 * E := (step_scale j hp).2.2.1
  have hH := H_pos j
  have he : 0 < E := by unfold E; positivity
  have ht := log_le_log p.invlen_pos hx
  rw [log_mul (by positivity) (by positivity), log_mul (by norm_num) (by positivity),log_pow] at ht
  change log p.invlen-log E ≤ _
  push_cast at ht
  linarith [H_ge j,Real.log_le_sub_one_of_pos hH,log_le_sub_one_of_pos (by norm_num : (0:ℝ)<64)]

private lemma levelcost_scale :
    ∀ᶠ j : ℕ in atTop, ∀ i, i ≤ testIx j →
      5000-log (beta i)+2*sLen j*(1-log (beta i)) ≤ height j := by
  filter_upwards [Tk_bounds,hpoly 20000 1,h_large 2000] with j ⟨he,hT⟩ h0 h1 i hi
  let h := H j; let d := height j
  have hl : -log (beta i) ≤ 200*h := (main_bounds _ hi).2.2
  have hp : 1 ≤ h := H_ge _
  have hi : 402*h ≤ h^6/2 := by
    have ht : h^2 ≤ h^6 := pow_le_pow_right₀ hp (by omega)
    change 2000 ≤ h at h1
    nlinarith
  change _ ≤ d
  have ht : 0 ≤ (sLen j:ℝ) := by positivity
  change (sLen j:ℝ)*h^6=d at he
  change _*h^1 ≤ d at h0; rw [pow_one] at h0
  nlinarith

private lemma span_scale (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ j : ℕ in atTop, ∀ B : ℝ, 0 ≤ B → ∀ i, i ≤ testIx j →
      B*(beta i^2/8) ≤ reserve C * height j →
      ∀ n : ℕ, n ≤ 2^(2*j) →
        B*log (2*n+1:ℝ) ≤ height j * (j:ℝ)^2 := by
  filter_upwards [eventually_ge_atTop 2, hpow_index (10000000000*reserve C) 64]
    with j hj hh B hBp i hi hB n hn
  let h := H j; let d := height j; let b := beta i
  have he : (1/6400)/h^32 ≤ b := (main_bounds _ hi).1
  have hp : 0 < h := H_pos _
  have hd : 0 ≤ d := (d_pos j).le
  have hY : B ≤ reserve C*d*(400000000*h^64) := by
    have hX : B * (((1/6400)/h^32)^2/8) ≤ reserve C*d :=
      le_trans (mul_le_mul_of_nonneg_left (by gcongr) hBp) hB
    field_simp at hX
    have hv : h^32^2 = h^((32:ℕ)^2) := rfl
    nlinarith [show 0 ≤ reserve C*d*h^64 from mul_nonneg
      (mul_nonneg (by linarith [reserve_ge hC]) hd) (by positivity),show (h^32)^2=h^64 by ring]
  have hI : log (2*n+1:ℝ) ≤ 4*(j:ℝ) := by
    have h₁ : (1:ℝ) ≤ 2^(2*j) := one_le_pow₀ (by norm_num)
    have h₂ : (n:ℝ) ≤ 2^(2*j) := by exact_mod_cast hn
    apply le_trans (log_le_log (by positivity) (by linarith : (2*n+1:ℝ) ≤ 3*2^(2*j)))
    rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow]
    have ht : 2 ≤ (j:ℝ) := by exact_mod_cast hj
    push_cast
    nlinarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2),log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)]
  change _ ≤ d*(j:ℝ)^2
  calc
    _ ≤ B*(4*(j:ℝ)) := mul_le_mul_of_nonneg_left hI hBp
    _ ≤ reserve C*d*(400000000*h^64)*(4*(j:ℝ)) := by gcongr
    _ = d*(1600000000*reserve C*h^64)*(j:ℝ) := by ring
    _ ≤ d*j*(j:ℝ) := by
      have h1 := reserve_ge hC
      have h3 : 1600000000*reserve C*h^64 ≤ (j:ℝ) :=
        (by calc
          _ ≤ (10000000000*reserve C)*h^64 := by gcongr; norm_num
          _ ≤ _ := hh)
      gcongr
    _ = _ := by ring

private lemma charge_small {C : ℝ} (hC : 1 ≤ C) {j i : ℕ} :
    4*shrinkScale (reserve C) j/(eps*kappa j (codeWeight C) i) ≤
      kappa j (codeWeight C) i /10 := by
  let D := reserve C; let a := codeWeight C; let d := height j; let h := H j
  let k := kappa j a i
  have hD : 1 ≤ D := reserve_ge hC
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one (code_ge hC)
  have hd : 0 < d := d_pos _; have hh : 0 < h := H_pos _
  have hk' : 0 < k := kappa_pos _ ha _ _
  have hkp : a*d/h ≤ k := le_mul_of_one_le_right (by positivity)
    (le_add_of_nonneg_right (by positivity))
  change 4*(300000*D^2*d^2/h^2)/(eps*k) ≤ k/10
  apply (div_le_iff₀ (mul_pos eps_pos hk')).mpr
  calc
    _ ≤ (a*d/h)/10*(eps*(a*d/h)) := by
      change 4*(300000*D^2*d^2/h^2) ≤
        (100000000*D*d/h)/10*(eps*(100000000*D*d/h))
      unfold eps
      field_simp
      nlinarith [show 0 ≤ D^2*d^2 by positivity]
    _ ≤ _ := by have he := eps_pos; gcongr

structure Press {M : ℕ} (C : ℝ) (j : ℕ) (p : Node) (A : Form M) : Prop where
  fits : p.ok M
  cap : ∃ n p', p.below p' ∧ Certified (H j) (plateErr j) n p' A ∧ (n:ℝ) ≤ C*H j ∧
    F A ≤ log p'.invlen + C*height j

lemma obtain_compressed (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ j : ℕ in atTop, ∀ (M : ℕ) (A : Form M) (p : Node), p.lev < M → Press C j p A →
      ∀ (a : Grid M → ℝ), 0 ≤ a → (∀ x, a x ≤ exp (height j)) → exp (-height j) ≤ p.avg a →
      ∀ (P : Law (Grid M)) (α : ℝ), PieceLaw p a P → 0 < α → p.avg a ≤ 2*α →
      ∀ i : ℕ, i ≤ testIx j →
        request A j p a α (side i) (kappa j (codeWeight C) i) →
        let l := snapGrid j p M
        let hl := snap_le (M:=M) j p
        let A' := tilde (H j) A p
        let k := kappa j (codeWeight C) i
        ∃ (w : Finset (Grid l)) (x : Grid l) (B : Bool)
          (v : Grid l → Grid M → ℂ) (V : Law (Grid l)) (t : ℝ),
          eps*k ≤ t ∧ t ≤ reserve C * height j ∧ w.Nonempty ∧ supported w V ∧
          separated (raise hl) A (sepRad j) (sig j*p.invlen/2) w ∧
          biases P p A hl w B v (beta i) ∧
          4*k/5 ≤ log (w.card:ℝ) ∧
          F (A' + long j • averageCost hl V x)- F A' ≤ 350*t ∧
          ((t=eps*k ∧ evenly w V) ∨ t/4 ≤ levelCost hl A' V (sLen j)) := by
  filter_upwards [sigma_small, span_scale C hC,stiff_budget C hC,hpoly 5000 1,levelcost_scale,
    kappa_scales (codeWeight C) (code_ge hC),spectral_compression (reserve C) (reserve_ge hC)]
    with j hs hsp hh hz hL hkl hcp
  intro M A p hp hP a ha hA hm P α hPA hα hm' i hi hreq l hl A' k
  let c := eps*k; let d := height j; let h := H j; let D := reserve C
  have hq := hP.fits
  obtain ⟨n,p',ht,HG,hN,hF⟩ := hP.cap
  obtain ⟨s,B,v,hs0,hs1,hs2,hB⟩ := extract_spectrum j hq.1 hp ha hα hPA
    (lt_of_lt_of_le (exp_pos _) hm) hm' (hs i hi) hreq
  have hM := step_scale j hq.2
  have hyp : A + place p M ≤ A' := tilde_le (H_ge j) HG.nonneg p
  have ht' : place p M ≤ A' := (le_add_of_nonneg_left HG.nonneg).trans hyp
  have hA' : 0 ≤ A' := (place_valid _ _).trans ht'
  have hD0 : 1 ≤ D := reserve_ge hC
  have hh' : 1 ≤ h := H_ge _
  have ha0 : 5000*h ≤ d := by simpa only [pow_one] using hz
  have hd : 0 < d := d_pos j
  have hu : F A - log p'.invlen ≤ C*d := by unfold d; linarith
  have hR := log_mesh j hq.2
  obtain ⟨hk0,hk1,hk2,hk3⟩ := hkl i hi
  have heps := eps_pos
  have hC' : 0 < c := by unfold c k; exact mul_pos eps_pos (kappa_pos _ (lt_of_lt_of_le zero_lt_one (code_ge hC)) _ _)
  have hY :
      -log (fq hl A' hA' 0) ≤ D*d := by
    obtain ⟨_,_,_,_,_,HE⟩ := fq_spec hl A' hA' hM.2.1 ht'
    apply HE.trans
    have hbr : F A'-F (A+place p M) ≤ d := by
      apply le_trans (tilde_tight HG (H_ge j) hq)
      apply le_trans (b:=C*h*(plateErr j + 1000*h)+2000) _ (le_trans hh ?_)
      · have he : 0 ≤ plateErr j :=
          div_nonneg hd.le (pow_nonneg (by linarith : 0 ≤ h) _)
        change (n:ℝ) * (plateErr j+1000*h)+_ ≤ _
        have hx : 0 ≤ plateErr j+1000*h := by linarith
        gcongr
      · exact div_le_self hd.le (one_le_pow₀ hh')
    have Hx := space_increment HG ht hq
    change log p.invlen-log (2^(M-l):ℝ) ≤ 1000*h at hR
    change _ ≤ _+C*d at hF
    unfold D reserve; linarith
  have hList (u : Finset (Grid l)) (hU : u⊆s) (m : ℕ) (he : m ≤ 2^(2*j)) :
      Compress.lnS (Fin m) (fun x : u => (x:Grid l)) ≤ height j * (j:ℝ)^2 := by
    obtain ⟨t,h1,h2⟩ := cheap_span hq ht HG hPA hl hM.1 hA hm
      (beta_pos i).le (beta_le i) hB
    apply le_trans (sumset_est (s:=u) (t:=t) (fun x hx => h1 _ (hU hx)) _)
    refine hsp _ (by positivity) i hi ?_ m he
    apply h2.trans
    change log p.invlen-log (2^(M-l):ℝ) ≤ 1000*h at hR
    unfold d h at *; unfold reserve; linarith
  have hCost (V : Law (Grid l)) (hw : supported s V) :
      levelCost hl A' V (sLen j) ≤ D*d := by
    have Hx := uniform_level_cost hq ht HG hyp hPA hl hA hm (beta_pos i) (beta_le i)
      hB V hw (sLen j) (pow_pos_nat _)
    unfold D reserve; unfold d at *; linarith [hL i hi]
  have hmem :
      c ≤ D*d := by
    calc
      _ ≤ eps*d := by
          unfold c k
          gcongr
      _ ≤ _ := by gcongr; unfold eps; linarith
  have hZ : 0 ≤ shrinkScale D j := by unfold shrinkScale; positivity
  obtain ⟨x,w,V,t,h1,h2,h3,h4,h5,h6,h7,h8,h9⟩ :=
    choose_compression hC' hZ hmem
      (fun u hu hv t hx hy hQ => hcp M l hl A' p.invlen hA' hM.2.1 ht' hY u hv
        (hList u hu) t (hk0.trans hx) hy hQ) hs0 hCost
  refine ⟨w,x,B,v,V,t,h1,h2,h5,h6,?_,?_,?_,h8,h9⟩
  · intro x hx y hy; exact hs2 x (h4 hx) y (h4 hy)
  · exact ⟨hB.1, fun x hx => hB.2 x (h4 hx)⟩
  have ht := h7.trans (charge_small hC)
  change k-log 2 ≤ _ at hs1
  change _ ≤ k/10 at ht
  change 100 ≤ k at hk3
  linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]

end FourierLLogL.Dyadic.Thermal

end OAI
