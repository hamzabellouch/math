import OAI.MeasureTheory.Falconer.Incidence.PencilEnergyPruning
import OAI.MeasureTheory.Falconer.Incidence.PencilSecondMoment

namespace OAI

/-! The high-energy deletion with its geometric budgets discharged. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def pencilEnergyBudget (N : ℕ) (s t K M : ℝ)
    (P : Finset (Space 2)) : ℝ :=
  (K*(80*(1/(2:ℝ)^N))^s*M)*(1+2*K*planarCriticalConstant N t)*(P.card:ℝ)^2

noncomputable def pencilMomentBudget (N : ℕ) (s t K M : ℝ)
    (P : Finset (Space 2)) : ℝ :=
  (K*(80*(1/(2:ℝ)^N))^s*M)*(1+K*planarPotentialConstant s t)*(P.card:ℝ)^2

noncomputable def pencilEnergyCutoff (N : ℕ) (s t K M m : ℝ)
    (P : Finset (Space 2)) : ℝ :=
  16*pencilEnergyBudget N s t K M P*pencilMomentBudget N s t K M P /
    (m*(P.card:ℝ))^2

theorem prune_pencil_fiber_energy (N : ℕ) {s t K M m : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (hK : 1 ≤ K) (hm : 0 < m)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hPchart : InBoundedLineChart P)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t K P)
    (hT : ∀ x ∈ P, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ M ∧
      InBoundedLineChart (T x) ∧ NormalizedFiniteBallBound (1/(2:ℝ)^N) s K (T x) ∧
      ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^N) x l) :
    let Q := pencilEnergyCutoff N s t K M m P
    ∃ R ⊆ P, R.Nonempty ∧ (P.card:ℝ)/2 ≤ (R.card:ℝ) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^N) t (2*K) R ∧
      ∀ x ∈ R,
        m/2 ≤ (((T x).filter fun l => pencilFiberEnergy N (t-s) P T l ≤ Q).card:ℝ) ∧
        NormalizedFiniteBallBound (1/(2:ℝ)^N) s (K*(2*M/m))
          ((T x).filter fun l => pencilFiberEnergy N (t-s) P T l ≤ Q) := by
  let Q := pencilEnergyCutoff N s t K M m P
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hPc : 0 < (P.card:ℝ) := Nat.cast_pos.mpr hP.card_pos
  obtain ⟨p,hp⟩ := hP.exists_mem
  have hM : 0 < M := hm.trans_le ((hT p hp).1.trans (hT p hp).2.1)
  have hpot : 0 < planarPotentialConstant s t := planarPotentialConstant_pos hst
  have hcrit : 0 < planarCriticalConstant N t := by unfold planarCriticalConstant; positivity
  have hE : 0 < pencilEnergyBudget N s t K M P := by unfold pencilEnergyBudget; positivity
  have hH : 0 < pencilMomentBudget N s t K M P := by unfold pencilMomentBudget; positivity
  have hQ : 0 < Q := by dsimp [Q,pencilEnergyCutoff]; positivity
  have hgeom : ∀ x ∈ P, InBoundedLineChart (T x) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^N) s K (T x) ∧
      ((T x).card:ℝ) ≤ M ∧ ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^N) x l :=
    fun x hx => ⟨(hT x hx).2.2.1,(hT x hx).2.2.2.1,(hT x hx).2.1,(hT x hx).2.2.2.2⟩
  have hbudget : 16*pencilEnergyBudget N s t K M P*pencilMomentBudget N s t K M P ≤
      Q*(m*(P.card:ℝ))^2 := by
    dsimp [Q,pencilEnergyCutoff]
    rw [div_mul_cancel₀ _ (by positivity : (m*(P.card:ℝ))^2 ≠ 0)]
  obtain ⟨R,hRP,hR,hhalf,hgood⟩ := prune_high_energy_pencils P T
    (pencilFiberEnergy N (t-s) P T) hP hm hQ (fun x hx => (hT x hx).1)
    (fun l _ => Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => by
      split <;> positivity)
    (pencil_fiber_energy_average N hs hst.le hK hM.le P T hPchart hPball hgeom)
    (pencil_second_moment_bound N hs hst hK P T hPchart hPball hgeom) hbudget
  refine ⟨R,hRP,hR,hhalf,?_,?_⟩
  · simpa only [mul_comm K 2] using normalized_finite_ball_bound_subset
      (by positivity : 0 ≤ 1/(2:ℝ)^N) hK0.le hRP
      (show (P.card:ℝ) ≤ 2*(R.card:ℝ) by linarith only [hhalf]) hPball
  · intro x hx
    refine ⟨hgood x hx,?_⟩
    apply normalized_finite_ball_bound_subset (by positivity : 0 ≤ 1/(2:ℝ)^N)
      hK0.le (Finset.filter_subset _ _) _ (hT x (hRP hx)).2.2.2.1
    calc
      _ ≤ M := (hT x (hRP hx)).2.1
      _ = (2*M/m)*(m/2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (hgood x hx) (by positivity)

end Falconer

end OAI
