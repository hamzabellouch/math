import OAI.MeasureTheory.Falconer.Incidence.CoarsePacketPoints
import OAI.MeasureTheory.Falconer.Incidence.FiniteBallBounds

namespace OAI

/-! Explicit fine-point fractions and pencil bounds in a selected coarse
packet. These are the inputs used by the centered packet-growth theorem. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem quantitative_packet_points {δ Δ s K m M J B : ℝ}
    (hδ : 0 < δ) (hΔ : 0 < Δ) (hδΔ : δ ≤ Δ) (hs : 0 ≤ s) (hK : 1 ≤ K)
    (hm : 0 < m) (hM : 0 < M) (hJ : 0 < J) (hB : 0 < B)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (q : Space 2 → Space 2) (a : Space 2)
    (hnear : ∀ x ∈ P, ∀ l ∈ T x, dist l (q l) ≤ Δ)
    (hT : ∀ x ∈ P, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ M ∧
      FiniteSeparatedAt δ (T x) ∧ NormalizedFiniteBallBound δ s K (T x) ∧
      ∀ l ∈ T x, |l 0| ≤ 1 ∧ TubeIncident δ x l)
    (hweight : ((∑ x ∈ P, (T x).card):ℝ) ≤ 2*J*B*(coarsePencilWeight P T q a:ℝ)) :
    ∃ A ⊆ P, A.Nonempty ∧
      (m/(4*J*B*(K*Δ^s*M)))*(P.card:ℝ) ≤ (A.card:ℝ) ∧
      ∀ x ∈ A,
        let U := (T x).filter fun l => q l = a
        U.Nonempty ∧ m/(4*J*B) ≤ (U.card:ℝ) ∧ (U.card:ℝ) ≤ K*Δ^s*M ∧
        FiniteSeparatedAt δ U ∧ NormalizedFiniteBallBound δ s (K*(4*J*B*M/m)) U ∧
        ∀ l ∈ U, |l 0| ≤ 1 ∧ |l 0-a 0| ≤ Δ ∧ |l 1-a 1| ≤ Δ ∧ TubeIncident δ x l := by
  let H := m*(P.card:ℝ)/(2*J*B)
  have hPc : 0 < (P.card:ℝ) := Nat.cast_pos.mpr hP.card_pos
  have hH : 0 < H := by dsimp [H]; positivity
  have hI : m*(P.card:ℝ) ≤ ((∑ x ∈ P, (T x).card):ℝ) := by
    calc
      _ = ∑ _x ∈ P, m := by simp; ring
      _ ≤ _ := Finset.sum_le_sum fun x hx => (hT x hx).1
  have hHw : H ≤ (coarsePencilWeight P T q a:ℝ) :=
    (div_le_iff₀ (by positivity)).2 (by nlinarith only [hI,hweight])
  obtain ⟨A,hAP,hA,hsize,hlarge⟩ := coarse_packet_points hΔ hδΔ hs hK hM hH P T hP q a hnear
    (fun x hx => (hT x hx).2.2.2.1) (fun x hx => (hT x hx).2.1) hHw
  have hlow (x : Space 2) (hx : x ∈ A) :
      m/(4*J*B) ≤ (((T x).filter fun l => q l = a).card:ℝ) := by
    convert hlarge x hx using 1
    dsimp [H]
    field_simp
    norm_num
  have hup (x : Space 2) (hx : x ∈ A) :
      (((T x).filter fun l => q l = a).card:ℝ) ≤ K*Δ^s*M := by
    have hsub : (T x).filter (fun l => q l = a) ⊆ (T x).filter (fun l => dist l a ≤ Δ) := by
      intro l hl
      obtain ⟨hlT,hla⟩ := Finset.mem_filter.mp hl
      exact Finset.mem_filter.mpr ⟨hlT,by simpa only [hla] using hnear x (hAP hx) l hlT⟩
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      ((normalized_ball_bound_all_radii hs hK (hT x (hAP hx)).2.2.2.1 a Δ hδΔ).trans
        (mul_le_mul_of_nonneg_left (hT x (hAP hx)).2.1 (by positivity)))
  refine ⟨A,hAP,hA,?_,?_⟩
  · convert hsize using 1
    dsimp [H]
    field_simp
    ring
  · intro x hx
    dsimp only
    have hl := hlow x hx
    have hUc : 0 < (((T x).filter fun l => q l = a).card:ℝ) := (by positivity : 0 < m/(4*J*B)).trans_le hl
    have hratio : ((T x).card:ℝ) ≤ (4*J*B*M/m)*(((T x).filter fun l => q l = a).card:ℝ) := by
      calc
        _ ≤ M := (hT x (hAP hx)).2.1
        _ = (4*J*B*M/m)*(m/(4*J*B)) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hl (by positivity)
    refine ⟨Finset.card_pos.mp (Nat.cast_pos.mp hUc),hl,hup x hx,
      finiteSeparatedAt_subset (Finset.filter_subset _ _) (hT x (hAP hx)).2.2.1,
      normalized_finite_ball_bound_subset hδ.le (zero_le_one.trans hK)
        (Finset.filter_subset _ _) hratio (hT x (hAP hx)).2.2.2.1,?_⟩
    intro l hl
    obtain ⟨hlT,hla⟩ := Finset.mem_filter.mp hl
    have hd : dist l a ≤ Δ := by simpa only [hla] using hnear x (hAP hx) l hlT
    exact ⟨((hT x (hAP hx)).2.2.2.2 l hlT).1,
      (show |l 0-a 0| ≤ dist l a by simpa only [Real.dist_eq] using PiLp.dist_apply_le l a 0).trans hd,
      (show |l 1-a 1| ≤ dist l a by simpa only [Real.dist_eq] using PiLp.dist_apply_le l a 1).trans hd,
      ((hT x (hAP hx)).2.2.2.2 l hlT).2⟩

end Falconer

end OAI
