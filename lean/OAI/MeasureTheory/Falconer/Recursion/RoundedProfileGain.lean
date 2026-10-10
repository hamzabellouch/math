import OAI.MeasureTheory.Falconer.Recursion.RoundedProfilePieces
import OAI.MeasureTheory.Falconer.Recursion.RoundedHighProfile

namespace OAI

/-! The rounded decomposition supplies the actual normal/good cell hypotheses
and retains a definite length of good cells. -/
namespace Falconer
open Set
attribute [local instance] Classical.propDecidable

theorem profileHighLength_nonneg {f : ℝ → ℝ} (u : ℝ) {S : List (ℝ × ℝ)}
    (hS : ∀ c ∈ S, 0 ≤ c.2) : 0 ≤ profileHighLength f u S := by
  rw [profileHighLength_eq_sum]
  apply List.sum_nonneg
  intro a ha
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ha
  split_ifs
  · exact hS c hc
  · rfl

theorem profileHighLength_antitone {f : ℝ → ℝ} {u v : ℝ} (huv : u ≤ v)
    {S : List (ℝ × ℝ)} (hS : ∀ c ∈ S, 0 ≤ c.2) :
    profileHighLength f v S ≤ profileHighLength f u S := by
  rw [profileHighLength_eq_sum,profileHighLength_eq_sum]
  induction S with
  | nil => simp
  | cons c S ih =>
    have ht := ih (fun d hd => hS d (by simp [hd]))
    have hc := hS c (by simp)
    simp only [List.map_cons,List.sum_cons]
    have hh : (if v ≤ intervalSecantSlope f c.1 c.2 then c.2 else 0) ≤
        if u ≤ intervalSecantSlope f c.1 c.2 then c.2 else 0 := by
      by_cases hv : v ≤ intervalSecantSlope f c.1 c.2
      · simp only [ite_eq_left hv,ite_eq_left (huv.trans hv),le_refl]
      · rw [ite_eq_right hv]
        split_ifs <;> linarith
    linarith

theorem rounded_profile_gain_cells {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    {m : ℕ} (hm : 0 < m) {τ ε s κ : ℝ} (hτ : 0 < τ) (hε : 0 ≤ ε) (hκ : 0 < κ)
    (hmesh : 2/(m:ℝ) ≤ τ/2) (herror : 4/(m:ℝ) ≤ ε*(τ/2))
    (hslack : 16/((m:ℝ)*τ) ≤ κ/2)
    {S : List (ℝ × ℝ)} (hS : StructuredProfilePieces f τ ε (s+κ) 1 S) :
    ∀ c ∈ S.map (innerProfileCell m),
      0 ≤ c.1 ∧ c.1+c.2 ≤ 1 ∧ τ/2 ≤ c.2 ∧
      s ≤ intervalSecantSlope f c.1 c.2 ∧ intervalSecantSlope f c.1 c.2 ≤ 2 ∧
      (∀ x ∈ Icc c.1 (c.1+c.2), -(3*ε)*c.2 ≤ intervalSecantError f c.1 c.2 x) ∧
      (s+2*κ ≤ intervalSecantSlope f c.1 c.2 →
        ∀ x ∈ Icc c.1 (c.1+c.2), |intervalSecantError f c.1 c.2 x| ≤ (3*ε)*c.2) := by
  intro c hc
  obtain ⟨ha,hb,hlen,hslope,halt⟩ :=
    (rounded_structured_profile_pieces hf hm hτ hε hmesh herror hS).2 c hc
  have hpos : 0 < c.2 := (half_pos hτ).trans_le hlen
  refine ⟨ha,hb,hlen,by linarith,?_,?_,?_⟩
  · exact (le_abs_self _).trans (intervalSecantSlope_abs_le hf c.1 hpos)
  · rcases halt with hlin | hsup
    · intro x hx
      simpa only [neg_mul] using (abs_le.mp (hlin x hx)).1
    · exact hsup.2
  · intro hh
    rcases halt with hlin | hsup
    · exact hlin
    · exfalso
      linarith [hsup.1]

theorem rounded_profile_good_length {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    {m : ℕ} (hm : 0 < m) {τ ε s κ t χ weak : ℝ}
    (hτ : 0 < τ) (hκ : 0 < κ) (hs : 0 ≤ s)
    (hmesh : 2/(m:ℝ) ≤ τ/2) (hslack : 16/((m:ℝ)*τ) ≤ κ)
    {S : List (ℝ × ℝ)} (hS : StructuredProfilePieces f τ ε (s+κ) 1 S)
    (hf0 : f 0 = 0) (hgrowth : t-weak ≤ f 1)
    (hcover : 1-χ ≤ (S.map Prod.snd).sum)
    (hgap : s+8*κ ≤ t) (hweak : weak+2*χ ≤ κ)
    (hround : (2/(m:ℝ))*(S.length:ℝ) ≤ κ) :
    κ ≤ profileHighLength f (s+2*κ) (S.map (innerProfileCell m)) := by
  have hraw := structured_profile_high_length_lower (κ := χ) (ε := weak) (t := t) hf hτ (by norm_num : (0:ℝ) < 1)
    (show 0 ≤ s+3*κ by positivity) hS hf0 (by simpa only [mul_one] using hgrowth)
    (by simpa only [mul_one,one_mul] using hcover)
  have hnonneg := profileHighLength_nonneg (f := f) (s+3*κ)
    (fun c hc => hτ.le.trans (hS.bounds c hc).2.2)
  have hhigh : 2*κ ≤ profileHighLength f (s+3*κ) S := by
    have hh : 0 ≤ (s+3*κ)*profileHighLength f (s+3*κ) S := mul_nonneg (by positivity) hnonneg
    simp only [mul_one] at hraw
    nlinarith only [hraw,hgap,hweak,hh]
  have hrounded := rounded_profile_high_length_lower hf hm hτ hmesh S
    (fun c hc => (hS.bounds c hc).2.2) (s+3*κ)
  have hmono := profileHighLength_antitone (f := f)
    (show s+2*κ ≤ s+3*κ-16/((m:ℝ)*τ) by linarith)
    (fun c hc => (half_pos hτ).le.trans (innerProfileCells_min_length hm hmesh
      (fun d hd => (hS.bounds d hd).2.2) c hc))
  linarith

end Falconer

end OAI
