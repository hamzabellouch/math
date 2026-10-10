import OAI.MeasureTheory.Falconer.Recursion.ProfileCellFamily

namespace OAI

/-! A profile with large total growth spends positive total length in the
linear intervals whose slope exceeds a prescribed intermediate threshold. -/
namespace Falconer
open Set

noncomputable def profileHighLength (f : ℝ → ℝ) (u : ℝ) (S : List (ℝ × ℝ)) : ℝ :=
  ((S.filter fun c => u ≤ intervalSecantSlope f c.1 c.2).map Prod.snd).sum

private theorem profileHighLength_cons (f : ℝ → ℝ) (u : ℝ) (c : ℝ × ℝ)
    (S : List (ℝ × ℝ)) :
    profileHighLength f u (c::S) =
      (if u ≤ intervalSecantSlope f c.1 c.2 then c.2 else 0)+profileHighLength f u S := by
  by_cases hc : u ≤ intervalSecantSlope f c.1 c.2 <;> simp [profileHighLength,hc]

theorem profile_increment_le_high_length {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    (u : ℝ) (S : List (ℝ × ℝ)) (hpos : ∀ c ∈ S, 0 < c.2) :
    (S.map (fun c => f (c.1+c.2)-f c.1)).sum ≤
      u*(S.map Prod.snd).sum+(2-u)*profileHighLength f u S := by
  induction S with
  | nil => simp [profileHighLength]
  | cons c S ih =>
    have hp := hpos c (by simp)
    have ht := ih (fun d hd => hpos d (by simp [hd]))
    have he : f (c.1+c.2)-f c.1 = intervalSecantSlope f c.1 c.2*c.2 := by
      unfold intervalSecantSlope
      rw [div_mul_cancel₀ _ hp.ne']
    have hbound := (le_abs_self (intervalSecantSlope f c.1 c.2)).trans
      (intervalSecantSlope_abs_le hf c.1 hp)
    rw [List.map_cons,List.sum_cons,List.map_cons,List.sum_cons,profileHighLength_cons]
    by_cases hc : u ≤ intervalSecantSlope f c.1 c.2
    · rw [ite_eq_left hc]
      have hm := mul_le_mul_of_nonneg_right hbound hp.le
      rw [← he] at hm
      nlinarith
    · rw [ite_eq_right hc]
      have hm := mul_le_mul_of_nonneg_right (le_of_not_ge hc) hp.le
      rw [← he] at hm
      nlinarith

theorem structured_profile_high_length_lower {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    {r θ s u t m κ ε : ℝ} (hr : 0 < r) (hm : 0 < m) (hu : 0 ≤ u)
    {S : List (ℝ × ℝ)} (hS : StructuredProfilePieces f r θ s m S)
    (hf0 : f 0 = 0) (hfm : t*m-ε*m ≤ f m)
    (hcover : m*(1-κ) ≤ (S.map Prod.snd).sum) :
    (t-u-ε-2*κ)*m ≤ (2-u)*profileHighLength f u S := by
  have hb : ∀ c ∈ S, 0 ≤ c.1 ∧ c.1+c.2 ≤ m ∧ 0 ≤ c.2 := by
    intro c hc
    have h := hS.bounds c hc
    exact ⟨h.1,h.2.1,hr.le.trans h.2.2⟩
  have hlen := ordered_interval_length_le hm.le hS.ordered hb
  have hinc := ordered_profile_increment_lower hf hm.le hS.ordered hb
  have hup := profile_increment_le_high_length hf u S (by
    intro c hc
    exact hr.trans_le (hS.bounds c hc).2.2)
  rw [hf0,sub_zero] at hinc
  have hw := mul_le_mul_of_nonneg_left hlen hu
  nlinarith

theorem structured_profile_high_linear {f : ℝ → ℝ} {r θ s u b : ℝ}
    {S : List (ℝ × ℝ)} (hS : StructuredProfilePieces f r θ s b S) (hsu : s < u)
    {c : ℝ × ℝ} (hc : c ∈ S) (hu : u ≤ intervalSecantSlope f c.1 c.2) :
    ∀ x ∈ Icc c.1 (c.1+c.2), |intervalSecantError f c.1 c.2 x| ≤ θ*c.2 := by
  rcases hS.alternatives c hc with hlin | hsuper
  · exact hlin.2
  · rw [hsuper.1] at hu
    exact False.elim (not_le_of_gt hsu hu)

end Falconer

end OAI
