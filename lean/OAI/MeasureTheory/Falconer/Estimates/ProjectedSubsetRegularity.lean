import OAI.MeasureTheory.Falconer.Angular.GoodProjectionDirections

namespace OAI

/-! A bounded projected energy controls every large original subset.
After discarding at most half its labels, its projected counting law has
an explicit Frostman bound. Repeated projected coordinates are retained. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem projected_subset_weighted_regular (N : ℕ) {s c B ρ : ℝ}
    (hs : 0 ≤ s) (hB : 0 < B) (hρ : 0 < ρ)
    (P A : Finset (Space 2)) (hP : P.Nonempty) (hAP : A ⊆ P)
    (hsize : ρ*(P.card:ℝ) ≤ (A.card:ℝ))
    (henergy : planarProjectionEnergy N s c P ≤ B*(P.card:ℝ)^2) :
    ∃ S ⊆ A, S.Nonempty ∧ (A.card:ℝ)/2 ≤ (S.card:ℝ) ∧
      ∀ u r : ℝ, 1/(2:ℝ)^N ≤ r →
        ((S.filter fun p => |lineParameterProjection c p-u| ≤ r).card:ℝ) ≤
          ((2*B/ρ)*(2/ρ)*(2:ℝ)^s)*r^s*(S.card:ℝ) := by
  let δ := 1/(2:ℝ)^N
  let k := fun p q : Space 2 =>
    (1/max |lineParameterProjection c p-lineParameterProjection c q| δ)^s
  let f := fun p => ∑ q ∈ P, k p q
  let b := B*(P.card:ℝ)/ρ
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hPc : 0 < (P.card:ℝ) := Nat.cast_pos.mpr hP.card_pos
  have hAc : 0 < (A.card:ℝ) := (mul_pos hρ hPc).trans_le hsize
  have hb : 0 < b := by dsimp [b]; positivity
  have hf : ∀ p, 0 ≤ f p := fun p => Finset.sum_nonneg fun q _ => by dsimp [k]; positivity
  have hsum : (∑ p ∈ A, f p) ≤ b*(A.card:ℝ) := by
    calc
      _ ≤ ∑ p ∈ P, f p := Finset.sum_le_sum_of_subset_of_nonneg hAP (fun p _ _ => hf p)
      _ ≤ B*(P.card:ℝ)^2 := henergy
      _ = b*(ρ*(P.card:ℝ)) := by dsimp [b]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hsize hb.le
  let S := A.filter fun p => f p ≤ 2*b
  have hhalf : (A.card:ℝ)/2 ≤ (S.card:ℝ) := finite_low_half A f hb (fun p _ => hf p) hsum
  have hSc : 0 < (S.card:ℝ) := by linarith only [hhalf,hAc]
  have hS : S.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp hSc)
  have hSP : S ⊆ P := (Finset.filter_subset _ _).trans hAP
  have hPSc : (P.card:ℝ) ≤ (2/ρ)*(S.card:ℝ) := by
    calc
      _ ≤ (2*(S.card:ℝ))/ρ := (le_div_iff₀ hρ).2 (by linarith only [hsize,hhalf])
      _ = _ := by ring
  refine ⟨S,Finset.filter_subset _ _,hS,hhalf,?_⟩
  intro u r hr
  have hr0 : 0 < r := hδ.trans_le hr
  let F := S.filter fun p => |lineParameterProjection c p-u| ≤ r
  by_cases hF : F.Nonempty
  · obtain ⟨p,hpF⟩ := hF
    obtain ⟨hpS,hpu⟩ := Finset.mem_filter.mp hpF
    have hfp : f p ≤ 2*b := (Finset.mem_filter.mp hpS).2
    have hweight (q : Space 2) (hqF : q ∈ F) : 1 ≤ (2*r)^s*k p q := by
      have hqu := (Finset.mem_filter.mp hqF).2
      have hd : |lineParameterProjection c p-lineParameterProjection c q| ≤ 2*r := by
        have hh := abs_sub_le (lineParameterProjection c p) u (lineParameterProjection c q)
        rw [abs_sub_comm u (lineParameterProjection c q)] at hh
        linarith only [hh,hpu,hqu]
      have hmax : max |lineParameterProjection c p-lineParameterProjection c q| δ ≤ 2*r :=
        max_le hd (by linarith only [hr,hδ])
      have hmaxpos : 0 < max |lineParameterProjection c p-lineParameterProjection c q| δ :=
        hδ.trans_le (le_max_right _ _)
      have hbase : 1 ≤ (2*r)*(1/max |lineParameterProjection c p-lineParameterProjection c q| δ) := by
        rw [mul_one_div]
        exact (le_div_iff₀ hmaxpos).2 (by simpa only [one_mul] using hmax)
      dsimp [k]
      rw [← Real.mul_rpow (by positivity) (by positivity)]
      exact Real.one_le_rpow hbase hs
    have hcount : (F.card:ℝ) ≤ (2*r)^s*f p := by
      calc
        _ = ∑ _q ∈ F, (1:ℝ) := by simp
        _ ≤ ∑ q ∈ F, (2*r)^s*k p q := Finset.sum_le_sum hweight
        _ = (2*r)^s*∑ q ∈ F, k p q := by rw [Finset.mul_sum]
        _ ≤ (2*r)^s*f p := mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg ((Finset.filter_subset _ _).trans hSP)
            (fun q _ _ => by dsimp [k]; positivity)) (by positivity)
    calc
      _ ≤ (2*r)^s*f p := hcount
      _ ≤ (2*r)^s*(2*b) := mul_le_mul_of_nonneg_left hfp (by positivity)
      _ = ((2*r)^s*(2*B/ρ))*(P.card:ℝ) := by dsimp [b]; ring
      _ ≤ ((2*r)^s*(2*B/ρ))*((2/ρ)*(S.card:ℝ)) :=
        mul_le_mul_of_nonneg_left hPSc (by positivity)
      _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hr0.le]; ring
  · change (F.card:ℝ) ≤ _
    rw [Finset.not_nonempty_iff_eq_empty.mp hF,Finset.card_empty,Nat.cast_zero]
    positivity

end Falconer

end OAI
