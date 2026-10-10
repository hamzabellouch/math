import OAI.Analysis.CStarAlgebra.PureInfiniteness.Products

namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
universe u
variable {A : Type u} [NonUnitalCStarAlgebra A]
local instance separationPartialOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance separationStarOrderedRing : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

lemma ramp_mem_Her {a : A} (ha : 0 ≤ a) {l u : ℝ} (hl : 0 ≤ l) :
    ramp a l u ∈ Her a :=
  Her_mono_of_mem (cut_mem_Her ha l) (ramp_mem_Her_cut ha hl)

lemma NormSignal.cutoff_ramp {a p : A} (h : NormSignal a p) (hp : 0 ≤ p) :
    NormSignal a (ramp p (1/2) 1) := by
  intro R hR
  let π := R.hom.toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ A)
  change ‖π (ramp p (1/2) 1)‖=1
  rw [map_ramp π hp (by norm_num : (0:ℝ)≤1/2)]
  apply norm_ramp_eq_one (map_nonneg π hp) (by norm_num) (by norm_num)
  exact (h R hR).symm.le

lemma HerCompression.mono {p q c : A} {κ τ : ℝ} (h : HerCompression p q c κ)
    (hκτ : κ ≤ τ) : HerCompression p q c τ := by
  intro x hx k hk
  exact (h x hx k hk).trans (by gcongr)

lemma iteration_step {p q c : A} {r θ : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hr : 0 < r) (_h : HerCompression p q c r)
    {p' q' : A} (hp'H : p' ∈ Her (ramp p (1/2) 1))
    (hq'H : q' ∈ Her (ramp q (1/2) 1))
    (h' : HerCompression p' q'
      (r⁻¹ • (ramp p (1/4) (1/2)*c*ramp q (1/4) (1/2))) θ) :
    HerCompression p' q' c (r*θ) := by
  have hpg : ramp p (1/4) (1/2)*cut p (1/2)=cut p (1/2) :=
    ramp_mul_cut hp (by norm_num) (by norm_num) le_rfl
  have hqg : ramp q (1/4) (1/2)*cut q (1/2)=cut q (1/2) :=
    ramp_mul_cut hq (by norm_num) (by norm_num) le_rfl
  have hpg' : cut p (1/2)*ramp p (1/4) (1/2)=cut p (1/2) := by
    simpa only [star_mul, (cut_nonneg p (1/2)).isSelfAdjoint.star_eq,
      (ramp_nonneg p (by norm_num : (1/4:ℝ)≤1/2)).isSelfAdjoint.star_eq] using congrArg star hpg
  intro x hx k hk
  have hxcut : x ∈ Her (cut p (1/2)) :=
    Her_mono_of_mem (ramp_mem_Her_cut hp (by norm_num : (0:ℝ)≤1/2))
      (Her_mono_of_mem hp'H hx)
  have hkcut : k ∈ Her (cut q (1/2)) :=
    Her_mono_of_mem (ramp_mem_Her_cut hq (by norm_num : (0:ℝ)≤1/2))
      (Her_mono_of_mem hq'H hk)
  have hxg := Her_fixed_right (cut_nonneg p (1/2)).isSelfAdjoint hpg' hxcut
  have hgk := Her_fixed_left hqg hkcut
  have he : x*(r⁻¹ • (ramp p (1/4) (1/2)*c*ramp q (1/4) (1/2)))*k =
      r⁻¹ • (x*c*k) := by
    rw [mul_smul_comm, smul_mul_assoc]
    congr 1
    simp only [mul_assoc, ← mul_assoc x (ramp p (1/4) (1/2)), hxg, hgk]
  have hb := h' x hx k hk
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)] at hb
  have hbr := mul_le_mul_of_nonneg_left hb hr.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul] using hbr

theorem iterated_separation (hp : PropertyP A) {a b c : A} (ha : 0 ≤ a) (han : ‖a‖ ≤ 1)
    (hb : 0 ≤ b) (hbn : ‖b‖ ≤ 1) (hcn : ‖c‖ ≤ 1) {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ (p q : A) (κ : ℝ), 0 ≤ p ∧ ‖p‖ ≤ 1 ∧ p ∈ Her a ∧
      0 ≤ q ∧ ‖q‖ ≤ 1 ∧ q ∈ Her b ∧ 0 ≤ κ ∧ κ < ζ ∧
      HerCompression p q c κ ∧ NormSignal a p ∧ NormSignal b q := by
  obtain ⟨θ,hθ0,hθ1,huniform⟩ := uniform_shrinking hp
  have hi : ∀ n : ℕ, ∃ p q : A, 0 ≤ p ∧ ‖p‖ ≤ 1 ∧ p ∈ Her a ∧
      0 ≤ q ∧ ‖q‖ ≤ 1 ∧ q ∈ Her b ∧
      HerCompression p q c (θ^(n+1)) ∧ NormSignal a p ∧ NormSignal b q := by
    intro n
    induction n with
    | zero => simpa only [Nat.zero_add, pow_one] using huniform a b c ha han hb hbn hcn
    | succ n ih =>
      obtain ⟨p,q,hp0,hpn,hpH,hq0,hqn,hqH,hcomp,hps,hqs⟩ := ih
      let f : A → A := fun p => ramp p (1/2) 1
      let g : A → A := fun p => ramp p (1/4) (1/2)
      let r := θ^(n+1)
      have hr : 0 < r := pow_pos hθ0 _
      have hgH (p : A) (hp : 0 ≤ p) : g p ∈ Her p := ramp_mem_Her hp (by norm_num)
      have hgn (p : A) : ‖g p‖ ≤ 1 := norm_ramp_le_one p (by norm_num)
      have hf0 (p : A) : 0 ≤ f p := ramp_nonneg p (by norm_num)
      have hfn (p : A) : ‖f p‖ ≤ 1 := norm_ramp_le_one p (by norm_num)
      have hc' : ‖r⁻¹ • (g p*c*g q)‖ ≤ 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
        have hh : ‖g p*c*g q‖ ≤ r := (hcomp _ (hgH p hp0) _ (hgH q hq0)).trans (by
          calc r*‖g p‖*‖g q‖ ≤ r*1*1 := by gcongr <;> apply hgn
               _ = r := by ring)
        calc r⁻¹*‖g p*c*g q‖ ≤ r⁻¹*r := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hr.le)
             _ = 1 := inv_mul_cancel₀ hr.ne'
      obtain ⟨p',q',hp'0,hp'n,hp'H,hq'0,hq'n,hq'H,hcomp',hps',hqs'⟩ :=
        huniform (f p) (f q) (r⁻¹ • (g p*c*g q)) (hf0 p) (hfn p) (hf0 q) (hfn q) hc'
      refine ⟨p',q',hp'0,hp'n,?_,hq'0,hq'n,?_,?_,?_,?_⟩
      · exact Her_mono_of_mem hpH (Her_mono_of_mem (ramp_mem_Her hp0 (by norm_num)) hp'H)
      · exact Her_mono_of_mem hqH (Her_mono_of_mem (ramp_mem_Her hq0 (by norm_num)) hq'H)
      · have hh := iteration_step hp0 hq0 hr hcomp hp'H hq'H hcomp'
        simpa only [r, pow_succ] using hh
      · intro R hR
        exact hps' R (by rw [hps.cutoff_ramp hp0 R hR]; norm_num)
      · intro R hR
        exact hqs' R (by rw [hqs.cutoff_ramp hq0 R hR]; norm_num)
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one hζ hθ1
  obtain ⟨p,q,hp0,hpn,hpH,hq0,hqn,hqH,hcomp,hps,hqs⟩ := hi n
  refine ⟨p,q,θ^(n+1),hp0,hpn,hpH,hq0,hqn,hqH,(pow_pos hθ0 _).le,?_,hcomp,hps,hqs⟩
  exact (by rw [pow_succ]; nlinarith [pow_pos hθ0 n] : θ^(n+1)≤θ^n).trans_lt hn
end MainGap

end

end OAI
