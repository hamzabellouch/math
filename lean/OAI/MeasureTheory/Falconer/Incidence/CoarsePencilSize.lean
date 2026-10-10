import OAI.MeasureTheory.Falconer.Incidence.FrozenPacketSelection
import OAI.MeasureTheory.Falconer.Incidence.VariableBaselineIncidence
import OAI.MeasureTheory.Falconer.Geometry.ProjectionSampleBudget

namespace OAI

/-! Uniform coarse pencils, and their size when the total coarse cover is small. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem uniform_pencil_size_band {δ t K : ℝ} (hδ : 0 ≤ δ) (hK : 0 ≤ K)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hPball : NormalizedFiniteBallBound δ t K P)
    (hT : ∀ x ∈ P, (T x).Nonempty) :
    let J := Nat.log 2 (P.biUnion T).card+1
    ∃ k : ℕ, ∃ R ⊆ P, R.Nonempty ∧ (P.card:ℝ) ≤ (J:ℝ)*(R.card:ℝ) ∧
      NormalizedFiniteBallBound δ t (K*(J:ℝ)) R ∧
      ∀ x ∈ R, (2:ℝ)^k ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ 2*(2:ℝ)^k := by
  obtain ⟨k,R,hRP,hR,hmass,hband⟩ := weighted_dyadic_size_band P
    (fun x => (T x).card) (fun _ => 1) (P.biUnion T).card (fun x hx =>
      ⟨(hT x hx).card_pos,Finset.card_le_card (Finset.subset_biUnion_of_mem T hx)⟩)
    (by simpa using (Nat.cast_pos.mpr hP.card_pos : (0:ℝ) < P.card))
  have hsize : (P.card:ℝ) ≤ (Nat.log 2 (P.biUnion T).card+1:ℕ)*(R.card:ℝ) := by
    simpa using hmass
  refine ⟨k,R,hRP,hR,hsize,normalized_finite_ball_bound_subset hδ hK hRP hsize hPball,?_⟩
  intro x hx
  have hlo : (2:ℝ)^k ≤ ((T x).card:ℝ) := by exact_mod_cast (hband x hx).1
  have hup : ((T x).card:ℝ) < (2:ℝ)^(k+1) := by exact_mod_cast (hband x hx).2
  exact ⟨hlo,by simpa only [pow_succ,mul_comm] using hup.le⟩

theorem comparable_pencil_size_upper (N : ℕ) {s t K m L : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (hK : 1 ≤ K) (hm : 0 < m) (_hL : 0 ≤ L)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hPchart : InBoundedLineChart P)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t K P)
    (hT : ∀ x ∈ P, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ 2*m ∧
      InBoundedLineChart (T x) ∧ NormalizedFiniteBallBound (1/(2:ℝ)^N) s K (T x) ∧
      ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^N) x l)
    (hunion : ((P.biUnion T).card:ℝ) ≤ L) :
    m ≤ 2*L*K*(80*(1/(2:ℝ)^N))^s*(1+K*planarPotentialConstant s t) := by
  have hp := planarPotentialConstant_pos hst
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hb := planar_variable_baseline_incidence N hs hst hK hm.le P T hP hPchart hPball hT
  have hh : m^2 ≤ L*((K*(80*(1/(2:ℝ)^N))^s*(2*m))*(1+K*planarPotentialConstant s t)) :=
    hb.trans (mul_le_mul_of_nonneg_right hunion (by positivity))
  apply (mul_le_mul_iff_left₀ hm).1
  nlinarith only [hh]

theorem comparable_pencil_size_power (N : ℕ) {κ s t K m L D : ℝ}
    (hκ : 0 < κ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (hgap : κ ≤ t-s)
    (hK : 1 ≤ K) (hm : 0 < m) (hD : 1 ≤ D) (hKD : K ≤ D)
    (hL : 0 ≤ L) (hLD : L ≤ D/((1/(2:ℝ)^N)^s)^2)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hPchart : InBoundedLineChart P)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t K P)
    (hT : ∀ x ∈ P, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ 2*m ∧
      InBoundedLineChart (T x) ∧ NormalizedFiniteBallBound (1/(2:ℝ)^N) s K (T x) ∧
      ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^N) x l)
    (hunion : ((P.biUnion T).card:ℝ) ≤ L) :
    m ≤ (160*(1+projectionGapConstant κ))*D^3/(1/(2:ℝ)^N)^s := by
  have hst : s < t := by linarith only [hκ,hgap]
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hδs : 0 < (1/(2:ℝ)^N)^s := by positivity
  have h80 : (80:ℝ)^s ≤ 80 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 80) hs1
  have hp := planarPotentialConstant_pos hst
  have hH := projectionGapConstant_pos hκ
  have hpot : 1+K*planarPotentialConstant s t ≤ (1+projectionGapConstant κ)*D := by
    calc
      _ ≤ 1+D*projectionGapConstant κ := by
        gcongr
        exact planarPotentialConstant_gap hκ hs1 hgap
      _ ≤ _ := by nlinarith only [hD]
  calc
    m ≤ 2*L*K*(80*(1/(2:ℝ)^N))^s*(1+K*planarPotentialConstant s t) :=
      comparable_pencil_size_upper N hs hst hK hm hL P T hP hPchart hPball hT hunion
    _ = 2*L*K*((80:ℝ)^s*(1/(2:ℝ)^N)^s)*(1+K*planarPotentialConstant s t) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 80) (by positivity)]
    _ ≤ 2*(D/((1/(2:ℝ)^N)^s)^2)*D*(80*(1/(2:ℝ)^N)^s)*
        ((1+projectionGapConstant κ)*D) := by gcongr
    _ = _ := by field_simp; ring

end Falconer

end OAI
