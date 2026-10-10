import OAI.MeasureTheory.Falconer.Angular.GoodProjectionDirections
import OAI.MeasureTheory.Falconer.Incidence.PencilFiberEnergy

namespace OAI

/-! A low-energy tube fiber contains a large regular set of original cells. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem finite_planar_energy_regular_subset (N : ℕ) {τ B : ℝ}
    (hτ : 0 ≤ τ) (hB : 0 < B) (P : Finset (Space 2)) (hP : P.Nonempty)
    (henergy : (∑ x ∈ P, ∑ y ∈ P,
      (1/max (dist x y) (1/(2:ℝ)^N))^τ) ≤ B*(P.card:ℝ)^2) :
    ∃ S ⊆ P, S.Nonempty ∧ (P.card:ℝ)/2 ≤ (S.card:ℝ) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^N) τ (4*B*(2:ℝ)^τ) S := by
  let δ := 1/(2:ℝ)^N
  let k := fun x y : Space 2 => (1/max (dist x y) δ)^τ
  let f := fun x => ∑ y ∈ P, k x y
  let S := P.filter fun x => f x ≤ 2*(B*(P.card:ℝ))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hPc : 0 < (P.card:ℝ) := Nat.cast_pos.mpr hP.card_pos
  have hb : 0 < B*(P.card:ℝ) := mul_pos hB hPc
  have hf (x : Space 2) : 0 ≤ f x := Finset.sum_nonneg fun y _ => by dsimp [k]; positivity
  have hhalf : (P.card:ℝ)/2 ≤ (S.card:ℝ) := by
    apply finite_low_half P f hb (fun x _ => hf x)
    change (∑ x ∈ P, ∑ y ∈ P, k x y) ≤ _
    convert henergy using 1
    ring
  have hSc : 0 < (S.card:ℝ) := by linarith only [hhalf,hPc]
  have hS : S.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp hSc)
  have hSP : S ⊆ P := Finset.filter_subset _ _
  refine ⟨S,hSP,hS,hhalf,?_⟩
  intro u r hr _
  have hr0 : 0 < r := hδ.trans_le hr
  let F := S.filter fun x => dist x u ≤ r
  by_cases hF : F.Nonempty
  · obtain ⟨x,hxF⟩ := hF
    obtain ⟨hxS,hxu⟩ := Finset.mem_filter.mp hxF
    have hfx : f x ≤ 2*(B*(P.card:ℝ)) := (Finset.mem_filter.mp hxS).2
    have hweight (y : Space 2) (hyF : y ∈ F) : 1 ≤ (2*r)^τ*k x y := by
      have hyu := (Finset.mem_filter.mp hyF).2
      have hd : dist x y ≤ 2*r := by
        have hh := dist_triangle x u y
        rw [dist_comm u y] at hh
        linarith only [hh,hxu,hyu]
      have hmax : max (dist x y) δ ≤ 2*r := max_le hd (by linarith only [hr,hδ])
      have hmaxpos : 0 < max (dist x y) δ := hδ.trans_le (le_max_right _ _)
      have hbase : 1 ≤ (2*r)*(1/max (dist x y) δ) := by
        rw [mul_one_div]
        exact (le_div_iff₀ hmaxpos).2 (by simpa only [one_mul] using hmax)
      dsimp [k]
      rw [← Real.mul_rpow (by positivity) (by positivity)]
      exact Real.one_le_rpow hbase hτ
    have hcount : (F.card:ℝ) ≤ (2*r)^τ*f x := by
      calc
        _ = ∑ _y ∈ F, (1:ℝ) := by simp
        _ ≤ ∑ y ∈ F, (2*r)^τ*k x y := Finset.sum_le_sum hweight
        _ = (2*r)^τ*∑ y ∈ F, k x y := by rw [Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg ((Finset.filter_subset _ _).trans hSP)
            (fun y _ _ => by dsimp [k]; positivity)) (by positivity)
    calc
      _ ≤ (2*r)^τ*f x := hcount
      _ ≤ (2*r)^τ*(2*(B*(P.card:ℝ))) := mul_le_mul_of_nonneg_left hfx (by positivity)
      _ ≤ (2*r)^τ*(2*(B*(2*(S.card:ℝ)))) := by gcongr; linarith only [hhalf]
      _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hr0.le]; ring
  · change (F.card:ℝ) ≤ _
    rw [Finset.not_nonempty_iff_eq_empty.mp hF,Finset.card_empty,Nat.cast_zero]
    positivity

noncomputable def pencilFiber (P : Finset (Space 2))
    (T : Space 2 → Finset (Space 2)) (l : Space 2) : Finset (Space 2) :=
  P.filter fun x => l ∈ T x

theorem pencilFiber_card (P : Finset (Space 2))
    (T : Space 2 → Finset (Space 2)) (l : Space 2) :
    ((pencilFiber P T l).card:ℝ) = tubeDegree P T l := by
  simp only [pencilFiber,tubeDegree,← Finset.sum_filter,Finset.sum_const,
    nsmul_eq_mul,mul_one]

theorem pencilFiber_energy (N : ℕ) (τ : ℝ) (P : Finset (Space 2))
    (T : Space 2 → Finset (Space 2)) (l : Space 2) :
    (∑ x ∈ pencilFiber P T l, ∑ y ∈ pencilFiber P T l,
      (1/max (dist x y) (1/(2:ℝ)^N))^τ) = pencilFiberEnergy N τ P T l := by
  simp only [pencilFiber,pencilFiberEnergy,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : l ∈ T x <;> simp [hx]

theorem pencil_fiber_regular_subset (N : ℕ) {τ B : ℝ}
    (hτ : 0 ≤ τ) (hB : 0 < B) (P : Finset (Space 2))
    (T : Space 2 → Finset (Space 2)) (l : Space 2)
    (hdegree : 0 < tubeDegree P T l)
    (henergy : pencilFiberEnergy N τ P T l ≤ B*(tubeDegree P T l)^2) :
    ∃ S ⊆ P, S.Nonempty ∧ tubeDegree P T l/2 ≤ (S.card:ℝ) ∧
      (∀ x ∈ S, l ∈ T x) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^N) τ (4*B*(2:ℝ)^τ) S := by
  have hF : (pencilFiber P T l).Nonempty := by
    apply Finset.card_pos.mp
    have hc : (0:ℝ) < (pencilFiber P T l).card := by
      rw [pencilFiber_card]
      exact hdegree
    exact Nat.cast_pos.mp hc
  obtain ⟨S,hSF,hS,hhalf,hreg⟩ := finite_planar_energy_regular_subset N hτ hB
    (pencilFiber P T l) hF (by simpa only [pencilFiber_energy,pencilFiber_card] using henergy)
  exact ⟨S,hSF.trans (Finset.filter_subset _ _),hS,
    by simpa only [pencilFiber_card] using hhalf,
    fun x hx => (Finset.mem_filter.mp (hSF hx)).2,hreg⟩

end Falconer

end OAI
