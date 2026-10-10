import OAI.Analysis.AncientFlat.Evolution.ClassicalEvolution
import OAI.Analysis.AncientFlat.Evolution.EvolutionCore

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction SchwartzMap Laplacian
namespace ParametrixVolterra
open FrozenParametrix StrongWeightedVolterra BiharmonicKernel SourceFrozenRows
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {T α β : ℝ} (hα : 0<α) (A : C(Slab T,V →ᵇ Icc α β))
    (hT₀ : 0≤T) (L : ℝ) (hL : 0≤L)
    (hLip : ∀ s r : Slab T, ∀ x z : V,
      |(A s x).val-(A r z).val|≤L*(‖x-z‖+|s.val-r.val|))
    (j : Time T →ᵇ C₀(V,ℂ)) (H : ℝ) (hH : 0≤H)
    (hhold : ∀ s : Time T, ∀ x y,
      ‖unweighted j s.val x-unweighted j s.val y‖≤H*s.val^(-7/8 : ℝ)*‖x-y‖^(1/4 : ℝ))
include hT₀ hL hH hLip hhold
lemma bounded_iteratedFDeriv_duhamel (t : Time T) (n : ℕ) (hn : n≤4) :
    ∃ M : ℝ, ∀ x, ‖iteratedFDeriv ℝ n (fun y => duhamel hα A j t.val y) x‖≤M := by
  have hf : StronglyMeasurable (fun s => (unweighted j s).toBCF) :=
    ZeroAtInftyContinuousMap.isometry_toBCF.continuous.comp_stronglyMeasurable
      (stronglyMeasurable_unweighted j)
  have hfn : ∀ s ∈ Ioo 0 t.val, ‖(unweighted j s).toBCF‖≤‖j‖*s^(-(3/4 : ℝ)) := by
    intro s hs
    rw [ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    simpa only [neg_div,mul_comm] using norm_unweighted_le j s hs.1
  have hh : ∀ s ∈ Ioo 0 t.val, ∀ x y : V,
      ‖(unweighted j s).toBCF x-(unweighted j s).toBCF y‖≤
        (H*s^(-(7/8 : ℝ)))*‖x-y‖^(1/4 : ℝ) := by
    intro s hs x y
    change ‖unweighted j s x-unweighted j s y‖≤_
    simpa only [neg_div] using hhold ⟨s,hs.1,hs.2.le.trans t.property.2⟩ x y
  rw [funext (duhamel_eq_sourceDuhamel A hT₀ hα j t)]
  exact WeightedSourceFrozenRows.exists_norm_iteratedFDeriv_duhamel_bound
    (heatKernel 1 zero_lt_one) (extendedA A hT₀) (continuous_extendedA A hT₀)
    α β hα (extendedA_range A hT₀) L hL (extendedA_lipschitz A hT₀ L hLip)
    (fun s => (unweighted j s).toBCF) hf (3/4) (7/8) ‖j‖ H (1/4) t.val
    (by norm_num) (by norm_num) (norm_nonneg j) hH t.property.1
    (by norm_num) (by norm_num) hfn hh n hn
lemma bounded_iteratedFDeriv_mildTime (d : C₀(V,ℂ)) (t : Time T) (n : ℕ) (hn : n≤4) :
    ∃ M : ℝ, ∀ x, ‖iteratedFDeriv ℝ n (fun y => mildTime hα A hT₀ d j t.val y) x‖≤M := by
  obtain ⟨M,hM⟩ := bounded_iteratedFDeriv_duhamel hα A hT₀ L hL hLip j H hH hhold t n hn
  let R := timeBCF (heatKernel 1 zero_lt_one) hα (A (initial hT₀)) t.val t.property.1 d.toBCF n
  refine ⟨‖R‖+M,fun x => ?_⟩
  have h0 : ContDiff ℝ n (fun y => c0Time hα (A (initial hT₀)) t.val d y) := by
    rw [funext (c0Time_eq_sourceValue hα _ _ t.property.1 d)]
    exact contDiff_infty.mp (contDiff_value (heatKernel 1 zero_lt_one) _
      (continuous_subtype_val.comp (A (initial hT₀)).continuous) α β hα
      (fun y => (A (initial hT₀) y).property) _ (Real.rpow_pos_of_pos t.property.1 _) d.toBCF) n
  have h1 : ContDiff ℝ n (fun y => duhamel hα A j t.val y) :=
    (contDiff_duhamel_of_holder A hT₀ hα L hL hLip j H hH hhold t).of_le (by exact_mod_cast hn)
  change ‖iteratedFDeriv ℝ n (fun y => c0Time hα (A (initial hT₀)) t.val d y+duhamel hα A j t.val y) x‖≤_
  rw [fun_iteratedFDeriv_add h0 h1,iteratedFDeriv_c0Time hα _ _ t.property.1 d]
  exact (norm_add_le _ _).trans (add_le_add (R.norm_coe_le_norm x) (hM x))
end ParametrixVolterra

end

end OAI
