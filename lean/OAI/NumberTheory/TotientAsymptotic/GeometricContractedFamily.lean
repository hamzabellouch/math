import OAI.NumberTheory.TotientAsymptotic.NaturalShiftScale
import OAI.NumberTheory.TotientAsymptotic.ScaleVolumeLower
import OAI.NumberTheory.TotientAsymptotic.FixedPrefixLower
import OAI.NumberTheory.TotientAsymptotic.MassMajorant

namespace OAI

/-! Positive-volume prime-coordinate families with strict rows and geometric minima. -/
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace TotientAsymptotic

def geometricContractedFamily (m n : ℕ) (B c : ℝ) : Set (Fin n → ℝ) :=
  contractedPrefix n (B/(1+rowContractionError m))
    (fun i => 1+rowContractionError (m-(i.val+1))) ∩
    {v | (∀ i,c*(rho^(m-i.val))⁻¹ ≤ v i) ∧
      ∀ i j,i < j → v j ≤ v i/(1+rowContractionError (m-(i.val+1)))}

lemma measurableSet_geometricContractedFamily (m n : ℕ) (B c : ℝ) :
    MeasurableSet (geometricContractedFamily m n B c) := by
  have hcoord : MeasurableSet {v : Fin n → ℝ | ∀ i,c*(rho^(m-i.val))⁻¹ ≤ v i} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i => measurableSet_le measurable_const (measurable_pi_apply i))
  have hgap : MeasurableSet {v : Fin n → ℝ | ∀ i j,i < j →
      v j ≤ v i/(1+rowContractionError (m-(i.val+1)))} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun j => ?_))
    by_cases hij : i < j
    · simpa [hij] using
        (measurableSet_le (by fun_prop : Measurable (fun v : Fin n → ℝ => v j))
          (by fun_prop : Measurable
          (fun v : Fin n → ℝ => v i/(1+rowContractionError (m-(i.val+1))))))
    · simp [hij]
  exact (measurableSet_contractedPrefix _ _ _).inter (hcoord.inter hgap)

lemma prefixRegion_real_eq_G {x : ℝ} {n : ℕ} (hB : 0 ≤ B x) (hn : 0 < n) :
    volume.real (prefixRegion n (B x) 0 0)=G x n := by
  have he : volume (prefixRegion n (B x) 0 0)=ENNReal.ofReal (G x n) := by
    rw [volume_prefixRegion_explicit n hn]
    simp only [Pi.zero_apply,mul_zero,Finset.sum_const_zero,sub_zero,max_eq_left hB]
    rw [G,prod_fin_shifted n g]
  rw [Measure.real,he,ENNReal.toReal_ofReal]
  unfold G
  exact div_nonneg (pow_nonneg hB _) (mul_nonneg (Nat.cast_nonneg _)
    (Finset.prod_nonneg (fun i _ => (g_pos i).le)))

theorem geometric_contracted_volume_lower : ∃ c δ : ℝ,0 < c ∧ 0 < δ ∧
    ∀ H : ℕ,1 ≤ H → ∀ᶠ x : ℝ in atTop,
      ∀ N : ℕ,N+2+H=m x →
        δ*G x (N+2) ≤ volume.real (geometricContractedFamily (m x) (N+2) (B x) c) := by
  obtain ⟨K,δ,hK,hδ,hprefix⟩ := ordered_prefix_volume_lower
  obtain ⟨d,hd,hcoord⟩ := natural_contracted_coordinate_lower
  let M := Real.exp rowContractionCost
  have hM : 0 < M := Real.exp_pos _
  refine ⟨d*K,δ/M,mul_pos hd hK,div_pos hδ hM,?_⟩
  intro H hH
  obtain ⟨L,hL⟩ := eventually_atTop.mp hprefix
  filter_upwards [hcoord,m_tendsto.eventually (eventually_ge_atTop (L+2+H)),
    B_tendsto.eventually (eventually_gt_atTop (0:ℝ))] with x hx hm hB
  intro N hN
  have hNL : L ≤ N := by omega
  have hn : N+2 ≤ m x := by omega
  let t := K*B x/((N+2:ℝ)*g (N+3))
  let S := orderedSlackRegion (N+2) (B x) t
  let T := geometricContractedFamily (m x) (N+2) (B x) (d*K)
  let β : ℕ → ℝ := fun r => 1+rowContractionError (m x-r)
  let κ : Fin (N+2) → ℝ := enlargementScale β
  have hβ (r) : 1 ≤ β r := by
    dsimp [β]
    linarith only [rowContractionError_nonneg (m x-r)]
  have hk (i) : 0 < κ i := enlargementScale_pos hβ i
  have hmap : Set.MapsTo (simplexScale κ) S T := by
    intro u hu
    have hv := reciprocal_enlargement_contracts hβ hu.1 hu.2.1
    refine ⟨⟨hv.1,hv.2.1,hv.2.2.1,?_⟩,?_,?_⟩
    · simpa only [β,Nat.sub_zero] using reciprocal_enlargement_top hβ hu.1
    · intro i
      have hh := hx (N+2) H (by omega) hH hN K hK u
        (by simpa only [Nat.cast_add,Nat.cast_ofNat,show N+2+1=N+3 by omega] using hu) i
      simpa only [mul_assoc] using hh
    · intro i j hij
      exact prefix_contraction_gap (fun i => hβ (i.val+1))
        (fun i => (hβ 0).trans (enlargementScale_top hβ i))
        (enlargementScale_step hβ) hu.1 hu.2.1 hij
  have hfinite : volume T ≠ ⊤ := by
    apply measure_ne_top_of_subset
      (fun _ hu => contractedPrefix_subset_prefixRegion (fun i => hβ (i.val+1)) hu.1)
    exact prefixRegion_volume_ne_top (by omega) _
  have hscaled := simplexScale_volume_lower κ hk
    (measurableSet_geometricContractedFamily _ _ _ _) hfinite hmap
  have hp : 0 < ∏ i : Fin (N+2),κ i := Finset.prod_pos (fun i _ => hk i)
  have hjac : (∏ i : Fin (N+2),κ i) ≤ M := row_contraction_jacobian hn
  have hmass : δ*G x (N+2) ≤ volume.real S := by
    have hh := hL N hNL (B x) hB
    rw [prefixRegion_real_eq_G hB.le (by omega)] at hh
    exact hh
  calc
    _ = (δ*G x (N+2))/M := by ring
    _ ≤ volume.real S/M := div_le_div_of_nonneg_right hmass hM.le
    _ ≤ volume.real S/(∏ i : Fin (N+2),κ i) :=
      div_le_div_of_nonneg_left ENNReal.toReal_nonneg hp hjac
    _ ≤ _ := hscaled

end TotientAsymptotic

end

end OAI
