import OAI.MeasureTheory.Falconer.Estimates.FiniteEnergyRegularity
import OAI.MeasureTheory.Falconer.Incidence.FiniteBallBounds

namespace OAI

/-! Discard high-energy tubes while preserving a positive fraction of every
retained cell's pencil. All energy and incidence budgets are explicit. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem high_energy_incidence_bound (U : Finset (Space 2)) (f g : Space 2 → ℝ)
    {Q E H : ℝ} (hQ : 0 ≤ Q) (hg : ∀ l ∈ U, 0 ≤ g l)
    (hE : (∑ l ∈ U, g l) ≤ E) (hH : (∑ l ∈ U, (f l)^2) ≤ H) :
    Q*(∑ l ∈ U.filter (fun l => Q < g l), f l)^2 ≤ E*H := by
  let B := U.filter fun l => Q < g l
  have hH0 : 0 ≤ H := (Finset.sum_nonneg fun _ _ => sq_nonneg _).trans hH
  have hc : Q*(B.card:ℝ) ≤ E := by
    calc
      _ = ∑ _l ∈ B, Q := by simp; ring
      _ ≤ ∑ l ∈ B, g l := Finset.sum_le_sum fun l hl => (Finset.mem_filter.mp hl).2.le
      _ ≤ ∑ l ∈ U, g l := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun l hl _ => hg l hl)
      _ ≤ E := hE
  have hs : (∑ l ∈ B, f l)^2 ≤ (B.card:ℝ)*H := by
    have hh := Finset.sum_mul_sq_le_sq_mul_sq B (fun _ => (1:ℝ)) f
    simp only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun l _ _ => sq_nonneg (f l))).trans hH) (Nat.cast_nonneg _))
  calc
    _ ≤ Q*((B.card:ℝ)*H) := mul_le_mul_of_nonneg_left hs hQ
    _ = (Q*(B.card:ℝ))*H := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hc hH0

theorem sum_pencil_intersection (P B : Finset (Space 2))
    (T : Space 2 → Finset (Space 2)) :
    (∑ x ∈ P, ((T x ∩ B).card:ℝ)) = ∑ l ∈ B, tubeDegree P T l := by
  unfold tubeDegree
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
  congr 2
  ext l
  simp only [Finset.mem_inter,Finset.mem_filter,and_comm]

theorem prune_high_energy_pencils (P : Finset (Space 2))
    (T : Space 2 → Finset (Space 2)) (g : Space 2 → ℝ)
    {m Q E H : ℝ} (hP : P.Nonempty) (hm : 0 < m) (hQ : 0 < Q)
    (hcard : ∀ x ∈ P, m ≤ ((T x).card:ℝ))
    (hg : ∀ l ∈ P.biUnion T, 0 ≤ g l)
    (hE : (∑ l ∈ P.biUnion T, g l) ≤ E)
    (hH : (∑ l ∈ P.biUnion T, (tubeDegree P T l)^2) ≤ H)
    (hbudget : 16*E*H ≤ Q*(m*(P.card:ℝ))^2) :
    ∃ R ⊆ P, R.Nonempty ∧ (P.card:ℝ)/2 ≤ (R.card:ℝ) ∧
      ∀ x ∈ R, m/2 ≤ ((T x |>.filter fun l => g l ≤ Q).card:ℝ) := by
  let U := P.biUnion T
  let B := U.filter fun l => Q < g l
  let bad := fun x => ((T x ∩ B).card:ℝ)
  have hPc : 0 < (P.card:ℝ) := Nat.cast_pos.mpr hP.card_pos
  have hI0 : 0 ≤ ∑ l ∈ B, tubeDegree P T l :=
    Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun x _ => by split <;> norm_num
  have hweighted := high_energy_incidence_bound U (tubeDegree P T) g hQ.le hg hE hH
  have hI : (∑ l ∈ B, tubeDegree P T l) ≤ m*(P.card:ℝ)/4 := by
    have hh : Q*(16*(∑ l ∈ B, tubeDegree P T l)^2) ≤ Q*(m*(P.card:ℝ))^2 := by
      calc
        _ = 16*(Q*(∑ l ∈ B, tubeDegree P T l)^2) := by ring
        _ ≤ 16*(E*H) := mul_le_mul_of_nonneg_left hweighted (by norm_num)
        _ ≤ _ := by nlinarith only [hbudget]
    have hh' := (mul_le_mul_iff_right₀ hQ).mp hh
    have hmP : 0 < m*(P.card:ℝ) := mul_pos hm hPc
    nlinarith only [hh',hI0,hmP]
  have hsum : (∑ x ∈ P, bad x) ≤ (m/4)*(P.card:ℝ) := by
    rw [show (∑ x ∈ P, bad x) = ∑ l ∈ B, tubeDegree P T l from sum_pencil_intersection P B T]
    nlinarith only [hI]
  let R := P.filter fun x => bad x ≤ 2*(m/4)
  have hhalf : (P.card:ℝ)/2 ≤ (R.card:ℝ) :=
    finite_low_half P bad (by positivity) (fun x _ => Nat.cast_nonneg _) hsum
  have hRc : 0 < (R.card:ℝ) := by linarith only [hhalf,hPc]
  refine ⟨R,Finset.filter_subset _ _,Finset.card_pos.mp (Nat.cast_pos.mp hRc),hhalf,?_⟩
  intro x hx
  obtain ⟨hxP,hxb⟩ := Finset.mem_filter.mp hx
  have he : T x ∩ B = (T x).filter fun l => ¬ g l ≤ Q := by
    ext l
    simp only [B,U,Finset.mem_inter,Finset.mem_filter,not_le]
    constructor
    · exact fun h => ⟨h.1,h.2.2⟩
    · exact fun h => ⟨h.1,Finset.mem_biUnion.mpr ⟨x,hxP,h.1⟩,h.2⟩
  have hp : (((T x).filter fun l => g l ≤ Q).card:ℝ) + bad x = (T x).card := by
    dsimp [bad]
    rw [he]
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := T x) (fun l => g l ≤ Q)
  linarith only [hp,hxb,hcard x hxP]

end Falconer

end OAI
