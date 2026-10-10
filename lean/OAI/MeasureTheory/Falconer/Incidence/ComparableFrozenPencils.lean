import OAI.MeasureTheory.Falconer.Incidence.CoarsePencilSize
import OAI.MeasureTheory.Falconer.Incidence.FrozenCoarseConfiguration

namespace OAI

/-! Select comparable original coarse pencils and then freeze their fine
packet sizes. Both selections retain explicit coarse-point mass. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem comparable_frozen_pencils {δ s t K : ℝ}
    (hδ : 0 < δ) (hK : 1 ≤ K)
    (P : Finset (Space 2)) (T G : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hPball : NormalizedFiniteBallBound δ t K P)
    (hT : ∀ x ∈ P, (T x).Nonempty ∧ InBoundedLineChart (T x) ∧
      FiniteSeparatedAt δ (T x) ∧ NormalizedFiniteBallBound δ s K (T x) ∧
      ∀ l ∈ T x, TubeIncident δ x l)
    (D : ℕ) (hG : ∀ a ∈ P.biUnion T, (G a).Nonempty ∧ (G a).card ≤ D) :
    let J₁ := Nat.log 2 (P.biUnion T).card+1
    let J₂ := Nat.log 2 D+1
    let F := 4*(J₁:ℝ)*(J₂:ℝ)
    ∃ m : ℝ, 0 < m ∧ ∃ R ⊆ P, R.Nonempty ∧ (P.card:ℝ) ≤ F*(R.card:ℝ) ∧
      NormalizedFiniteBallBound δ t (K*F) R ∧
      ∃ U : Space 2 → Finset (Space 2),
        (∀ x ∈ R, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ 2*m ∧
          U x ⊆ T x ∧ (U x).Nonempty ∧
          m/(2*(J₂:ℝ)) ≤ ((U x).card:ℝ) ∧ ((U x).card:ℝ) ≤ 2*m ∧
          InBoundedLineChart (U x) ∧ FiniteSeparatedAt δ (U x) ∧
          NormalizedFiniteBallBound δ s (K*F) (U x) ∧
          ∀ l ∈ U x, TubeIncident δ x l) ∧
        R.biUnion U ⊆ P.biUnion T ∧
        (∑ a ∈ R.biUnion U, ((G a).card:ℝ)) ≤ ∑ a ∈ P.biUnion T, ((G a).card:ℝ) ∧
        ∃ k : ℕ, ∀ a ∈ R.biUnion U, 2^k ≤ (G a).card ∧ (G a).card < 2^(k+1) := by
  let J₁ := Nat.log 2 (P.biUnion T).card+1
  let J₂ := Nat.log 2 D+1
  let F := 4*(J₁:ℝ)*(J₂:ℝ)
  have hJ₁ : 1 ≤ (J₁:ℝ) := by dsimp [J₁]; exact_mod_cast Nat.le_add_left 1 _
  have hJ₂ : 0 < (J₂:ℝ) := by dsimp [J₂]; positivity
  have hK0 := zero_le_one.trans hK
  have hKJ : 0 ≤ K*(J₁:ℝ) := by positivity
  obtain ⟨j,Q,hQP,hQ,hsize,hQball,hband⟩ := uniform_pencil_size_band hδ.le hK0 P T hP hPball
    (fun x hx => (hT x hx).1)
  let m : ℝ := 2^j
  have hm : 0 < m := by dsimp [m]; positivity
  have hTQ (x : Space 2) (hx : x ∈ Q) : m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ 2*m ∧
      InBoundedLineChart (T x) ∧ FiniteSeparatedAt δ (T x) ∧
      NormalizedFiniteBallBound δ s (K*(J₁:ℝ)) (T x) ∧ ∀ l ∈ T x, TubeIncident δ x l := by
    refine ⟨(hband x hx).1,(hband x hx).2,(hT x (hQP hx)).2.1,(hT x (hQP hx)).2.2.1,?_,
      (hT x (hQP hx)).2.2.2.2⟩
    intro z r hr hr1
    exact ((hT x (hQP hx)).2.2.2.1 z r hr hr1).trans (by
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (hδ.le.trans hr) _)
      exact le_mul_of_one_le_right hK0 hJ₁)
  have hQT : Q.biUnion T ⊆ P.biUnion T := Finset.biUnion_subset_biUnion_of_subset_left T hQP
  obtain ⟨R,hRQ,hR,hsizeR,hRb,U,hU,hUT,hGsum,k,hGband⟩ := frozen_coarse_configuration hδ hKJ hm
    (mul_pos (by norm_num) hm) Q T G hQ hQball hTQ D (fun a ha => hG a (hQT ha))
  have he : 2*(J₂:ℝ)*(2*m)/m = 4*(J₂:ℝ) := by field_simp; ring
  rw [he] at hsizeR hRb hU
  have hconst : (K*(J₁:ℝ))*(4*(J₂:ℝ)) = K*F := by dsimp [F]; ring
  rw [hconst] at hRb hU
  refine ⟨m,hm,R,hRQ.trans hQP,hR,?_,hRb,U,?_,hUT.trans hQT,?_,k,hGband⟩
  · calc
      (P.card:ℝ) ≤ (J₁:ℝ)*(Q.card:ℝ) := hsize
      _ ≤ (J₁:ℝ)*((4*(J₂:ℝ))*(R.card:ℝ)) :=
        mul_le_mul_of_nonneg_left hsizeR (zero_le_one.trans hJ₁)
      _ = _ := by ring
  · intro x hx
    obtain ⟨hsub,hne,hlo,hup,hchart,hsep,hball,hinc⟩ := hU x hx
    exact ⟨(hband x (hRQ hx)).1,(hband x (hRQ hx)).2,hsub,hne,hlo,hup,hchart,hsep,hball,hinc⟩
  · exact hGsum.trans (Finset.sum_le_sum_of_subset_of_nonneg hQT (fun _ _ _ => Nat.cast_nonneg _))

end Falconer

end OAI
