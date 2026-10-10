import OAI.Probability.ContinuumTransition.ConstructionSequence

namespace OAI

section
open scoped Topology BigOperators
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

def ConstructionData.masses {p : ℝ} (C : ConstructionData p) (n : ℕ) : ℝ := (C.stages n).a

def prefixMass (σ : ℕ → ℝ) (n k : ℕ) : ℝ := if k < n then σ k else 0

def tailMass (σ : ℕ → ℝ) (n k : ℕ) : ℝ := if n ≤ k then σ k else 0

lemma prefixMass_nonneg {σ : ℕ → ℝ} (hσ : ∀ k, 0 ≤ σ k) (n k : ℕ) : 0 ≤ prefixMass σ n k := by
  unfold prefixMass
  split_ifs
  · exact hσ k
  · exact le_refl _

lemma tailMass_nonneg {σ : ℕ → ℝ} (hσ : ∀ k, 0 ≤ σ k) (n k : ℕ) : 0 ≤ tailMass σ n k := by
  unfold tailMass
  split_ifs
  · exact hσ k
  · exact le_refl _

lemma prefixMass_add_tailMass (σ : ℕ → ℝ) (n : ℕ) :
    (fun k => prefixMass σ n k+tailMass σ n k) = σ := by
  funext k
  by_cases hk : k < n
  · simp [prefixMass,tailMass,hk,Nat.not_le.mpr hk]
  · simp [prefixMass,tailMass,hk,Nat.le_of_not_gt hk]

lemma prefixMass_summable {σ : ℕ → ℝ} (hσ : ∀ k, 0 ≤ σ k) (hs : Summable σ) (n : ℕ) :
    Summable (prefixMass σ n) := by
  apply hs.of_nonneg_of_le (prefixMass_nonneg hσ n)
  intro k
  unfold prefixMass
  split_ifs <;> simp_all

lemma tailMass_summable {σ : ℕ → ℝ} (hσ : ∀ k, 0 ≤ σ k) (hs : Summable σ) (n : ℕ) :
    Summable (tailMass σ n) := by
  apply hs.of_nonneg_of_le (tailMass_nonneg hσ n)
  intro k
  unfold tailMass
  split_ifs <;> simp_all

lemma tsum_prefixMass (σ : ℕ → ℝ) (n : ℕ) :
    ∑' k, prefixMass σ n k = ∑ k ∈ Finset.range n, σ k := by
  rw [tsum_eq_sum (s := Finset.range n) (fun k hk => by
    simp only [Finset.mem_range] at hk
    simp only [prefixMass,ite_eq_right hk])]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [prefixMass,Finset.mem_range.mp hk,ite_true]

lemma tailMass_tsum_tendsto {σ : ℕ → ℝ} (hσ : ∀ k, 0 ≤ σ k) (hs : Summable σ) :
    Tendsto (fun n => ∑' k, tailMass σ n k) atTop (𝓝 0) := by
  have he (n : ℕ) : ∑' k, tailMass σ n k = (∑' k, σ k)-∑ k ∈ Finset.range n, σ k := by
    have hh := (prefixMass_summable hσ hs n).tsum_add (tailMass_summable hσ hs n)
    rw [prefixMass_add_tailMass,tsum_prefixMass] at hh
    linarith
  simp_rw [he]
  simpa only [sub_self] using (tendsto_const_nhds (x := ∑' k, σ k)).sub hs.hasSum.tendsto_sum_nat

lemma ConstructionData.reference_mass {p : ℝ} (C : ConstructionData p) (n : ℕ) :
    ∑' k, (C.stages n).σ k = ∑ k ∈ Finset.range n, C.masses k := by
  induction n with
  | zero => simp [C.initial_zero]
  | succ n ih =>
    rw [(C.transitions n).mass_eq,tsum_prepend _ (C.stages n).σ_summable,ih,Finset.sum_range_succ]
    dsimp [ConstructionData.masses]
    ring

lemma ConstructionData.masses_nonneg {p : ℝ} (C : ConstructionData p) (n : ℕ) : 0 ≤ C.masses n :=
  (C.stages n).a_pos.le

lemma ConstructionData.sum_masses_le {p : ℝ} (C : ConstructionData p) (n : ℕ) :
    ∑ k ∈ Finset.range n, C.masses k ≤ firstMass p+1 := by
  rw [← C.reference_mass]
  exact (C.stages n).base_mass

lemma ConstructionData.masses_summable {p : ℝ} (C : ConstructionData p) : Summable C.masses :=
  summable_of_sum_range_le C.masses_nonneg C.sum_masses_le

lemma ConstructionData.mass_bound {p : ℝ} (C : ConstructionData p) : ∑' k, C.masses k ≤ firstMass p+1 :=
  Real.tsum_le_of_sum_range_le C.masses_nonneg C.sum_masses_le

lemma ConstructionData.ranges_one {p : ℝ} (C : ConstructionData p) (n : ℕ) : 1 ≤ C.ranges n := by
  have hh := (C.transitions n).range_large
  linarith

lemma ConstructionData.reference_profile {p : ℝ} (C : ConstructionData p) (n : ℕ) (r : ℝ) :
    physicalProfile C.t (C.stages n).σ (C.stages n).R r =
      coreProfile C.t r-C.t*∑ k ∈ Finset.range n, C.masses k*scaledKernelProfile (C.ranges k) r := by
  induction n with
  | zero => simp [C.initial_zero,physicalProfile_zero]
  | succ n ih =>
    rw [(C.transitions n).mass_eq,(C.transitions n).range_eq,
      physicalProfile_prepend C.t (C.stages n).σ_nonneg (C.stages n).R_one (C.stages n).σ_summable,ih,
      Finset.sum_range_succ]
    dsimp [ConstructionData.masses]
    ring

lemma attraction_prefixMass (t : ℝ) (σ R : ℕ → ℝ) (n : ℕ) (r : ℝ) :
    attraction t (prefixMass σ n) R r = t*∑ k ∈ Finset.range n, σ k*scaledKernelProfile (R k) r := by
  unfold attraction
  congr 1
  rw [tsum_eq_sum (s := Finset.range n) (fun k hk => by
    simp only [Finset.mem_range] at hk
    simp only [prefixMass,ite_eq_right hk,zero_mul])]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [prefixMass,Finset.mem_range.mp hk,ite_true]

lemma ConstructionData.reference_eq_prefix {p : ℝ} (C : ConstructionData p) (n : ℕ) :
    physicalProfile C.t (C.stages n).σ (C.stages n).R = physicalProfile C.t (prefixMass C.masses n) C.ranges := by
  funext r
  rw [C.reference_profile]
  unfold physicalProfile
  rw [attraction_prefixMass]

end ContinuumTemperature
end
end

end OAI
