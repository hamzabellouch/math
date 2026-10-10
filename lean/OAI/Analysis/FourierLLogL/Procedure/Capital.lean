import OAI.Analysis.FourierLLogL.Thermal.Update
/-! # Deterministic budget state and caps -/
open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic.Procedure
open Law Node Real Period Compress.Params Thermal

def capA : ℝ := 10^16
lemma cap_ok : 1 ≤ capA := by norm_num [capA]

variable {M j : ℕ}

structure Fund (M : ℕ) where
  mood : Form M
  anchor : Node
  uses : ℕ
  spend : ℝ
  bank : ℝ

namespace Fund
def initial (M : ℕ) : Fund M := ⟨0,root,0,0,0⟩
def advance (p : Node) (c : Fund M) (u : Update j M p) : Fund M :=
    ⟨u.next c.mood,p,c.uses+1,c.spend+u.credit,c.bank+u.bill⟩

def breached (j : ℕ) (c : Fund M) := 1000*height j < c.bank
def fuel (j : ℕ) := eps*(height j / Thermal.H j)

structure Ok (c : Fund M) (p : Node) (j : ℕ) : Prop where
  domain : below p c.anchor
  effects : Certified (H j) (plateErr j) c.uses c.anchor c.mood
  under : (c.uses:ℝ) ≤ capA*H j
  nonneg : 0 ≤ c.bank ∧ c.bank ≤ c.spend
  solvent : c.bank ≤ (1000+reserve capA)*height j
  floor_ok : c.uses*fuel j ≤ c.spend
  relative : F c.mood ≤ log c.anchor.invlen + 3000*c.uses+400*c.spend
  verified : gap c.mood (track capA j c.uses) ≤ 402*c.bank-5000*(c.spend-c.bank)

lemma Ok.restrict {p q : Node} {c : Fund M} (h : c.Ok p j) (he : below q p) : c.Ok q j :=
    { h with domain := below_trans he h.domain }

lemma track_add (j n : ℕ) :
    track capA j (n+1)=track capA j n+ stepRad capA j := by simp only [track]; push_cast; ring

lemma envelope_scale :
    ∀ᶠ j : ℕ in atTop, sepRad j ≤ 1 ∧ fuel j > 0 ∧ 1 ≤ height j ∧ 1 ≤ height j/(H j)^2 := by
  filter_upwards [spacing capA cap_ok,hpoly 1 2] with j hj hh
  have hx := H_pos j; have hd := d_pos j
  refine ⟨hj.2.2.2.2.1,mul_pos eps_pos (div_pos hd hx),one_le_pow₀ (by norm_num),?_⟩
  exact (le_div_iff₀ (by positivity)).mpr hh

lemma fund_est :
    ∀ᶠ j : ℕ in atTop, ∀ M : ℕ, (initial M).Ok root j ∧
      ∀ c : Fund M, ∀ p, Ok c p j →
        c.spend ≤ 2*(c.bank+1) ∧
        (¬ breached j c → p.ok M → Press capA j p c.mood ∧
           c.uses+1 ≤ capA*H j ∧
           ∀ (u : Update j M p) P, u.Good capA c.mood P →
             Ok (c.advance p u) p j) := by
  filter_upwards [envelope_scale,hpoly (3000*capA) 1,kappa_scales (codeWeight capA) (code_ge cap_ok)] with j hj h ht M
  have hr := hj.1
  have hp := H_ge j
  let a := H j; let d := height j
  have hD : 1 ≤ d := hj.2.2.1
  have ha : 1 ≤ a := hp; have ha' : 0 < a := H_pos _
  constructor
  · refine ⟨below_refl _,certified_start M,?_,by simp [initial],?_,?_,?_,?_⟩
    · simp only [initial,Nat.cast_zero]; linarith [show (1:ℝ) ≤ capA*H j from one_le_mul_of_one_le_of_one_le cap_ok hp]
    · change 0 ≤ _; have := reserve_ge cap_ok; have := d_pos j; positivity
    · simp [initial]
    · simp [initial, invlen_top,F_zero]
    have he := r_steps cap_ok j 0 (show ((0:ℕ):ℝ) ≤ _ by
      push_cast; have := one_le_mul_of_one_le_of_one_le cap_ok hp; linarith)
    dsimp [initial]
    rw [gap_zero he.1 (by have := he.2; linarith)]
    simp
  intro c p hh
  have hA := hh.effects.nonneg
  have HX := r_steps cap_ok _ _ hh.under
  have Hx := hh.verified
  have hy := gap_lower hA HX.1 (by linarith [HX.2])
  have hnp := hh.nonneg
  have hz : c.spend ≤ 2*(c.bank+1) := by linarith [hnp.1]
  refine ⟨hz,?_⟩
  intro hd he
  rw [breached] at hd
  have HH : c.spend ≤ 2002*d := by change ¬1000*d<_ at hd; linarith
  have ht' := hh.floor_ok
  have hI : c.uses+1 ≤ capA*H j := by
    have hk : (c.uses:ℝ) ≤ 20020000*a := by
      have HL := ht'.trans HH
      unfold fuel eps at HL; change (c.uses:ℝ)*(1/10000*(d/a)) ≤ _ at HL
      apply le_of_mul_le_mul_left _ (show 0 < d by linarith)
      field_simp at HL; nlinarith
    unfold capA; nlinarith [show H j=a from rfl]
  refine ⟨⟨he,c.uses,c.anchor,hh.domain,hh.effects,hh.under,?_⟩,hI,?_⟩
  · have ht : 3000*c.uses ≤ d := by
      have h1 := hh.under
      change _*H j^1 ≤ d at h; rw [pow_one] at h
      change 3000*(c.uses:ℝ) ≤ d
      linarith
    change _ ≤ _+capA*d
    have hL := hh.relative
    unfold capA; nlinarith
  intro u P hu
  let v := c.advance p u
  have hK := certified_add hh.effects hp he hu.positive hu.plate
  have hR : Ok v p j := by
    have hf : fuel j ≤ u.credit := by
      apply le_trans _ hu.duration
      apply mul_le_mul_of_nonneg_left _ eps_pos.le
      apply le_trans _ (ht _ hu.ix_ok).2.2.1
      apply div_le_div_of_nonneg_right _ (H_pos _).le
      exact le_mul_of_one_le_left (d_pos j).le (code_ge cap_ok)
    have hc : 0 ≤ u.credit := hj.2.1.le.trans hf
    have hJ := hu.gap_est _ HX.1 HX.2
    refine ⟨below_refl _,hK,?_,?_,?_,?_,?_,?_⟩
    · unfold v advance; dsimp; push_cast; exact hI
    · dsimp only [v,advance]
      have he : 0 ≤ u.bill ∧ u.bill ≤ u.credit := by unfold Update.bill; split <;> simp [hc]
      constructor
      exact add_nonneg hnp.1 he.1
      exact add_le_add hnp.2 he.2
    · change c.bank+u.bill ≤ _
      unfold Update.bill; split
      · have hg := hu.reserves.2; linarith [hh.solvent]
      simp only [add_zero, hh.solvent]
    · change ((c.uses+1:ℕ):ℝ) * _ ≤ c.spend + u.credit
      push_cast; linarith
    · change F (u.next c.mood) ≤ _
      dsimp only [v,advance]
      push_cast
      have HZ := space_increment hh.effects hh.domain he
      linarith [hu.cost,hh.relative]
    · change gap (u.next c.mood) (track capA j (c.uses+1)) ≤ _
      rw [track_add]
      change gap _ _ ≤ 402*(c.bank+u.bill)-5000*((c.spend+u.credit)-(c.bank+u.bill))
      unfold Update.bill
      by_cases hh : u.regular = true
      · rw [ite_eq_left hh] at *
        linarith
      rw [ite_eq_right hh] at *
      have ht := hu.cheap (by simpa using hh)
      unfold eps at ht
      linarith
  exact hR
end Fund

end FourierLLogL.Dyadic.Procedure

end OAI
