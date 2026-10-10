import OAI.Analysis.AncientFlat.Evolution.EarlyIntegral

namespace OAI
noncomputable section
open Set Filter
namespace LocalHolder
variable {V E : Type} [NormedAddCommGroup V] [NormedAddCommGroup E]
lemma of_lipschitz (F : ℝ → V → E) (a T γ : ℝ) (ha : 0<a) (hγ : 0<γ) (hγ1 : γ<1)
    (B D E₀ : ℝ) (hB : 0≤B) (hD : 0≤D) (hE : 0≤E₀)
    (hn : ∀ t∈Icc a T, ∀ x, ‖F t x‖≤B)
    (hs : ∀ t∈Icc a T, ∀ x y, ‖F t x-F t y‖≤D*‖x-y‖)
    (htm : ∀ s∈Icc a T, ∀ t∈Icc a T, s≤t → t-s≤a → ∀ x,
      ‖F t x-F s x‖≤E₀*(t-s)) :
    ∃ C : ℝ, 0≤C ∧ (∀ t∈Icc a T, ∀ x, ‖F t x‖≤C) ∧
      ∀ t∈Icc a T, ∀ s∈Icc a T, ∀ x y, ‖F t x-F s y‖≤C*(‖x-y‖^γ+|t-s|^(γ/4)) := by
  let E₁ := E₀+2*B/a
  have hE₁ : 0≤E₁ := by dsimp [E₁]; positivity
  have htord (s) (hs : s∈Icc a T) (t) (ht : t∈Icc a T) (hst : s≤t) (x : V) :
      ‖F t x-F s x‖≤E₁*(t-s) := by
    by_cases he : t-s≤a
    · exact (htm s hs t ht hst he x).trans (mul_le_mul_of_nonneg_right
        (by dsimp [E₁]; exact le_add_of_nonneg_right (by positivity)) (sub_nonneg.mpr hst))
    · have ha' : a≤t-s := (lt_of_not_ge he).le
      calc
        _ ≤ ‖F t x‖+‖F s x‖ := norm_sub_le ..
        _ ≤ B+B := add_le_add (hn t ht x) (hn s hs x)
        _ = (2*B/a)*a := by field_simp; ring
        _ ≤ (2*B/a)*(t-s) := mul_le_mul_of_nonneg_left ha' (by positivity)
        _ ≤ E₁*(t-s) := mul_le_mul_of_nonneg_right (by dsimp [E₁]; exact le_add_of_nonneg_left hE) (sub_nonneg.mpr hst)
  have htime (s) (hs : s∈Icc a T) (t) (ht : t∈Icc a T) (x : V) :
      ‖F t x-F s x‖≤E₁*|t-s| := by
    rcases le_total s t with hst|hts
    · rw [abs_of_nonneg (sub_nonneg.mpr hst)]; exact htord s hs t ht hst x
    · rw [norm_sub_rev,abs_of_nonpos (sub_nonpos.mpr hts),neg_sub]; exact htord t ht s hs hts x
  let Cs := (2*B)^(1-γ)*D^γ
  let Ct := (2*B)^(1-γ/4)*E₁^(γ/4)
  have hCs : 0≤Cs := by dsimp [Cs]; positivity
  have hCt : 0≤Ct := by dsimp [Ct]; positivity
  refine ⟨B+Cs+Ct,by positivity,fun t ht x => (hn t ht x).trans (by linarith),?_⟩
  intro t ht s hs' x y
  have hsp : ‖F t x-F t y‖≤Cs*‖x-y‖^γ := by
    apply HolderInterpolation.scalar (norm_nonneg _) (by positivity) hD (norm_nonneg _) hγ hγ1
    · exact (norm_sub_le ..).trans ((add_le_add (hn t ht x) (hn t ht y)).trans_eq (by ring))
    · exact hs t ht x y
  have hti : ‖F t y-F s y‖≤Ct*|t-s|^(γ/4) := by
    apply HolderInterpolation.scalar (norm_nonneg _) (by positivity) hE₁ (abs_nonneg _) (by positivity) (by linarith)
    · exact (norm_sub_le ..).trans ((add_le_add (hn t ht y) (hn s hs' y)).trans_eq (by ring))
    · exact htime s hs' t ht y
  calc
    _ ≤ ‖F t x-F t y‖+‖F t y-F s y‖ := norm_sub_le_norm_sub_add_norm_sub ..
    _ ≤ Cs*‖x-y‖^γ+Ct*|t-s|^(γ/4) := add_le_add hsp hti
    _ ≤ (B+Cs+Ct)*‖x-y‖^γ+(B+Cs+Ct)*|t-s|^(γ/4) := by gcongr <;> linarith
    _ = _ := by ring
end LocalHolder

end

end OAI
