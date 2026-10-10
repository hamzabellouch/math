import Mathlib
import OAI.Probability.LatticeSurface.Brownian.VectorRiemannIntegral
import OAI.Probability.LatticeSurface.Skorokhod.BVVectorSupport

namespace OAI

namespace ConvexSkorokhod

open Set Filter MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem normal_partition_measure (B : Body E) (u k : ℝ → E)
    (hu : ContinuousOn u (Icc 0 1)) (hk : ContinuousOn k (Icc 0 1))
    (_hBu : ∀ t∈Icc (0:ℝ) 1,u t∈B.carrier)
    (hBV : BoundedVariationOn k (Icc (0:ℝ) 1))
    (hn : NormalPartitionCondition B u k) :
    ∃ μ : VectorMeasure unitInterval E, IsFiniteMeasure μ.variation ∧
      μ ({0}:Set unitInterval)=0 ∧
      (∀ a b : unitInterval,a ≤ b → μ (Ioc a b)=k b-k a) ∧
      ∀ y : unitInterval → E,Continuous y → (∀ t,y t∈B.carrier) →
        μ.integral (fun t => u t-y t) (innerSL ℝ) ≤ 0 := by
  let kr : unitInterval → E := fun t => k t
  have hk' : Continuous kr := continuousOn_iff_continuous_domRestrict.mp hk
  have hv' : BoundedVariationOn kr univ := by
    apply (lt_of_le_of_lt _ hBV.lt_top).ne
    exact eVariationOn.comp_le_of_monotoneOn k (fun t : unitInterval => (t:ℝ))
      (fun _ _ _ _ h => h) (fun t _ => t.property)
  obtain ⟨μ,hμfin,hμ₀,hμinc⟩ := exists_continuous_bv_vector_measure kr hv' hk' 0
  let := hμfin
  have hz : μ ({0}:Set unitInterval)=0 := by
    simpa only [botSet_eq_singleton_of_isBot (show IsBot (0:unitInterval) from fun _ => bot_le)] using hμ₀
  refine ⟨μ,hμfin,hz,hμinc,?_⟩
  intro y hy hyB
  let f : unitInterval → E := fun t => u t-y t
  have hf : Continuous f := (continuousOn_iff_continuous_domRestrict.mp hu).sub hy
  have hlim := tendsto_vectorStep_integral μ hz (innerSL ℝ) f hf
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨M,hM⟩ := hn ε hε
  have hE : ∀ᶠ n : ℕ in atTop,μ.integral (vectorStep f (n+1)) (innerSL ℝ) ≤ ε := by
    filter_upwards [eventually_ge_atTop M] with n hn
    have hnpos : 0 < n+1 := Nat.succ_pos _
    have hnM : M ≤ n+1 := hn.trans (Nat.le_succ _)
    have hpart := hM (n+1) hnM hnpos (fun j => y (unitGrid (n+1) j)) (fun j hj => hyB _)
    rw [vectorStep_integral]
    convert hpart using 1
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j < n+1 := Finset.mem_range.mp hj
    have hgrid : unitGrid (n+1) j ≤ unitGrid (n+1) (j+1) := by
      change (unitGrid (n+1) j : ℝ) ≤ (unitGrid (n+1) (j+1) : ℝ)
      rw [unitGrid_val (n+1) j hnpos hj'.le,unitGrid_val (n+1) (j+1) hnpos hj']
      exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ j) (Nat.cast_nonneg _)
    rw [hμinc _ _ hgrid]
    simp only [f,kr,unitGrid_val (n+1) j hnpos hj'.le,
      unitGrid_val (n+1) (j+1) hnpos hj']
    rfl
  simpa only [zero_add] using le_of_tendsto hlim hE

end ConvexSkorokhod

end OAI
