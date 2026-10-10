import OAI.MeasureTheory.Falconer.Incidence.CoarsePacketPoints
import OAI.MeasureTheory.Falconer.Incidence.PencilEnergyPruning

namespace OAI

/-! Freeze fine-packet cardinalities by weighting the dyadic selection with
actual coarse incidences, then retain cells with large coarse pencils. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem weighted_dyadic_size_band (P : Finset (Space 2))
    (b : Space 2 → ℕ) (w : Space 2 → ℝ) (M : ℕ)
    (hb : ∀ x ∈ P, 0 < b x ∧ b x ≤ M)
    (hW : 0 < ∑ x ∈ P, w x) :
    let J := Nat.log 2 M+1
    ∃ k : ℕ, ∃ B ⊆ P, B.Nonempty ∧
      (∑ x ∈ P, w x) ≤ (J:ℝ)*(∑ x ∈ B, w x) ∧
      ∀ x ∈ B, 2^k ≤ b x ∧ b x < 2^(k+1) := by
  let J := Nat.log 2 M+1
  let f := fun x => Nat.log 2 (b x)
  let W := ∑ x ∈ P, w x
  have hJ : 0 < (J:ℝ) := by dsimp [J]; positivity
  have hmap : ∀ x ∈ P, f x ∈ Finset.range J := fun x hx =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right (hb x hx).2))
  have hdiv : (Finset.range J).card • (W/(J:ℝ)) ≤ W := by
    simp only [Finset.card_range,nsmul_eq_mul]
    rw [mul_div_cancel₀ _ hJ.ne']
  obtain ⟨k,_,hk⟩ := Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum hmap
    (show (Finset.range J).Nonempty from ⟨0,Finset.mem_range.mpr (by dsimp [J]; omega)⟩) hdiv
  let B := P.filter fun x => f x = k
  have hsum : W ≤ (J:ℝ)*(∑ x ∈ B, w x) := by
    simpa only [mul_comm] using (div_le_iff₀ hJ).mp hk
  have hB : B.Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty.mp hn,Finset.sum_empty,mul_zero] at hsum
    exact hW.not_ge hsum
  refine ⟨k,B,Finset.filter_subset _ _,hB,hsum,?_⟩
  intro x hx
  obtain ⟨hxP,hxk⟩ := Finset.mem_filter.mp hx
  dsimp [f] at hxk
  rw [← hxk]
  exact ⟨Nat.pow_log_le_self 2 (hb x hxP).1.ne',Nat.lt_pow_succ_log_self (by norm_num) _⟩

theorem freeze_coarse_packet_sizes (P : Finset (Space 2))
    (T : Space 2 → Finset (Space 2)) (b : Space 2 → ℕ) (D : ℕ)
    {m M : ℝ} (hP : P.Nonempty) (hm : 0 < m) (hM : 0 < M)
    (hcard : ∀ x ∈ P, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ M)
    (hb : ∀ l ∈ P.biUnion T, 0 < b l ∧ b l ≤ D) :
    let J := Nat.log 2 D+1
    ∃ k : ℕ, ∃ B ⊆ P.biUnion T, B.Nonempty ∧
      (∀ l ∈ B, 2^k ≤ b l ∧ b l < 2^(k+1)) ∧
      ∃ R ⊆ P, R.Nonempty ∧ m*(P.card:ℝ)/(2*(J:ℝ)*M) ≤ (R.card:ℝ) ∧
        ∀ x ∈ R, m/(2*(J:ℝ)) ≤ ((T x ∩ B).card:ℝ) := by
  let J := Nat.log 2 D+1
  have hJ : 0 < (J:ℝ) := by dsimp [J]; positivity
  have hPc : 0 < (P.card:ℝ) := Nat.cast_pos.mpr hP.card_pos
  have hI : m*(P.card:ℝ) ≤ ∑ l ∈ P.biUnion T, tubeDegree P T l := by
    rw [sum_tubeDegree]
    calc
      _ = ∑ _x ∈ P, m := by simp; ring
      _ ≤ _ := Finset.sum_le_sum fun x hx => (hcard x hx).1
  obtain ⟨k,B,hBU,hB,hmass,hband⟩ := weighted_dyadic_size_band (P.biUnion T) b
    (tubeDegree P T) D hb ((mul_pos hm hPc).trans_le hI)
  have hretained : m*(P.card:ℝ)/(J:ℝ) ≤ ∑ x ∈ P, ((T x ∩ B).card:ℝ) := by
    rw [sum_pencil_intersection]
    apply (div_le_iff₀ hJ).2
    simpa only [mul_comm] using hI.trans hmass
  obtain ⟨R,hRP,hR,hsize,hlarge⟩ := finite_large_weight_subset P
    (fun x => ((T x ∩ B).card:ℝ)) hP (div_pos (mul_pos hm hPc) hJ) hM
    (fun x hx => (Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_left)).trans
      (hcard x hx).2) hretained
  refine ⟨k,B,hBU,hB,hband,R,hRP,hR,?_,?_⟩
  · convert hsize using 1
    dsimp [J]
    field_simp
  · intro x hx
    have hh := hlarge x hx
    convert hh using 1
    dsimp [J]
    field_simp

end Falconer

end OAI
