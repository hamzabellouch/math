import OAI.MeasureTheory.Falconer.Incidence.RegularEnergyPencils

namespace OAI

/-! Select an actual incident tube and a regular subset of its point fiber. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem pencilFiberEnergy_mono (N : ℕ) (τ : ℝ)
    (P R : Finset (Space 2)) (T U : Space 2 → Finset (Space 2))
    (hRP : R ⊆ P) (hUT : ∀ x ∈ R, U x ⊆ T x) (l : Space 2) :
    pencilFiberEnergy N τ R U l ≤ pencilFiberEnergy N τ P T l := by
  unfold pencilFiberEnergy
  apply (Finset.sum_le_sum_of_subset_of_nonneg hRP (fun x _ _ =>
    Finset.sum_nonneg fun y _ => by split <;> positivity)).trans'
  apply Finset.sum_le_sum
  intro x hx
  apply (Finset.sum_le_sum_of_subset_of_nonneg hRP (fun y _ _ => by split <;> positivity)).trans'
  apply Finset.sum_le_sum
  intro y hy
  by_cases h : l ∈ U x ∧ l ∈ U y
  · rw [ite_eq_left h,ite_eq_left ⟨hUT x hx h.1,hUT y hy h.2⟩]
  · rw [ite_eq_right h]
    split <;> positivity

theorem regular_fiber_of_pencil_degree (N : ℕ) {τ m L Q : ℝ}
    (hτ : 0 ≤ τ) (hm : 0 < m) (hL : 0 < L) (hQ : 0 < Q)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hcard : ∀ x ∈ P, m ≤ ((T x).card:ℝ))
    (hunion : ((P.biUnion T).card:ℝ) ≤ L)
    (henergy : ∀ l ∈ P.biUnion T, pencilFiberEnergy N τ P T l ≤ Q) :
    ∃ l ∈ P.biUnion T, ∃ S ⊆ P, S.Nonempty ∧
      m*(P.card:ℝ)/(2*L) ≤ (S.card:ℝ) ∧ (∀ x ∈ S, l ∈ T x) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^N) τ
        (4*Q*(L/(m*(P.card:ℝ)))^2*(2:ℝ)^τ) S := by
  let V := P.biUnion T
  let D := m*(P.card:ℝ)/L
  let B := Q*(L/(m*(P.card:ℝ)))^2
  have hPc : 0 < (P.card:ℝ) := Nat.cast_pos.mpr hP.card_pos
  have hD : 0 < D := by dsimp [D]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hI : m*(P.card:ℝ) ≤ ∑ l ∈ V, tubeDegree P T l := by
    rw [sum_tubeDegree]
    calc
      _ = ∑ _x ∈ P, m := by simp; ring
      _ ≤ _ := Finset.sum_le_sum hcard
  have hV : V.Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty.mp hn,Finset.sum_empty] at hI
    exact (mul_pos hm hPc).not_ge hI
  have hmean : (∑ _l ∈ V, D) ≤ ∑ l ∈ V, tubeDegree P T l := by
    calc
      _ = D*(V.card:ℝ) := by simp; ring
      _ ≤ D*L := mul_le_mul_of_nonneg_left hunion hD.le
      _ = m*(P.card:ℝ) := by dsimp [D]; field_simp
      _ ≤ _ := hI
  obtain ⟨l,hl,hdegree⟩ := Finset.exists_le_of_sum_le hV hmean
  have hBD : B*D^2 = Q := by dsimp [B,D]; field_simp
  have henergy' : pencilFiberEnergy N τ P T l ≤ B*(tubeDegree P T l)^2 := by
    calc
      _ ≤ Q := henergy l hl
      _ = B*D^2 := hBD.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (sq_le_sq₀ hD.le (hD.le.trans hdegree) |>.2 hdegree) hB.le
  obtain ⟨S,hSP,hS,hhalf,hinc,hreg⟩ := pencil_fiber_regular_subset N hτ hB P T l
    (hD.trans_le hdegree) henergy'
  refine ⟨l,hl,S,hSP,hS,?_,hinc,?_⟩
  · calc
      _ = D/2 := by dsimp [D]; ring
      _ ≤ tubeDegree P T l/2 := by gcongr
      _ ≤ _ := hhalf
  · convert hreg using 1
    dsimp [B]
    ring

end Falconer

end OAI
