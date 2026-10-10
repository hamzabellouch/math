import OAI.Analysis.CircleDomains.Topology.NestedCompactContinua
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.UniformConvergence

namespace OAI

/-! A compact level continuum obtained from connected approximating
sets with a common point. Tail closures retain contact with a closed
boundary set; no choice of a Hausdorff subsequence is needed. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem exists_limit_level_continuum
    {X : Type*} [MetricSpace X] {S E : Set X} (hS : IsCompact S) (hE : IsClosed E)
    (f : ℕ → X → ℝ) {v : X → ℝ} (hv : Continuous v)
    (hlim : TendstoUniformlyOn f v atTop S)
    (K : ℕ → Set X) (hc : ∀ n, IsConnected (K n)) (hKS : ∀ n, K n ⊆ S)
    {x : X} (hx : ∀ n, x ∈ K n)
    (hlevel : ∀ n y, y ∈ K n → f n y = f n x)
    (hmeet : ∀ n, (K n ∩ E).Nonempty) :
    ∃ C : Set X, IsCompact C ∧ IsConnected C ∧ x ∈ C ∧ C ⊆ S ∧
      (∀ y ∈ C, v y = v x) ∧ (C ∩ E).Nonempty := by
  let T (n : ℕ) : Set X := closure (⋃ m : {m : ℕ // n ≤ m}, K m.val)
  have hsub (n : ℕ) : T n ⊆ S := by
    apply closure_minimal _ hS.isClosed
    exact iUnion_subset (fun m => hKS m.val)
  have hxT (n : ℕ) : x ∈ T n :=
    subset_closure (mem_iUnion_of_mem ⟨n, le_rfl⟩ (hx n))
  have hm : Antitone T := by
    intro n m hnm
    apply closure_mono
    intro y hy
    obtain ⟨k, hk⟩ := mem_iUnion.mp hy
    exact mem_iUnion_of_mem ⟨k.val, hnm.trans k.property⟩ hk
  have hTc (n : ℕ) : IsCompact (T n) :=
    hS.of_isClosed_subset isClosed_closure (hsub n)
  have hTp (n : ℕ) : IsPreconnected (T n) := by
    apply IsPreconnected.closure
    apply isPreconnected_iUnion
    · exact ⟨x, mem_iInter.mpr (fun _ => hx _)⟩
    · exact fun m => (hc m.val).isPreconnected
  let C := ⋂ n, T n
  have hxC : x ∈ C := mem_iInter.mpr hxT
  have hCS : C ⊆ S := (iInter_subset T 0).trans (hsub 0)
  have hCc : IsCompact C :=
    hS.of_isClosed_subset (isClosed_iInter (fun _ => isClosed_closure)) hCS
  have hconn : IsConnected C :=
    ⟨⟨x, hxC⟩, preconnected_iInter_compact_antitone T hTc hTp hm⟩
  have hCE : (C ∩ E).Nonempty := by
    have hmE : Antitone (fun n => T n ∩ E) := fun n m h => inter_subset_inter_left _ (hm h)
    obtain ⟨y, hy⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      (fun n => T n ∩ E) hmE.directed_ge
      (fun n => by
        obtain ⟨y, hyK, hyE⟩ := hmeet n
        exact ⟨y, subset_closure (mem_iUnion_of_mem ⟨n, le_rfl⟩ hyK), hyE⟩)
      (fun n => (hTc n).inter_right hE) (fun _ => isClosed_closure.inter hE)
    exact ⟨y, mem_iInter.mpr (fun n => (mem_iInter.mp hy n).1), (mem_iInter.mp hy 0).2⟩
  refine ⟨C, hCc, hconn, hxC, hCS, ?_, hCE⟩
  intro y hy
  apply dist_eq_zero.mp
  apply le_antisymm _ dist_nonneg
  apply le_of_forall_pos_le_add
  intro ε hε
  simp only [zero_add]
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((Metric.tendstoUniformlyOn_iff.mp hlim) (ε/2) (half_pos hε))
  have hband : T N ⊆ {z | dist (v z) (v x) ≤ ε} := by
    apply closure_minimal _ (isClosed_le (hv.dist continuous_const) continuous_const)
    intro z hz
    obtain ⟨m, hm⟩ := mem_iUnion.mp hz
    change dist (v z) (v x) ≤ ε
    have ha := hN m.val m.property z (hKS m.val hm)
    have hb := hN m.val m.property x (hKS m.val (hx m.val))
    rw [hlevel m.val z hm] at ha
    have ht := dist_triangle (v z) (f m.val z) (v x)
    rw [hlevel m.val z hm, dist_comm (f m.val x)] at ht
    linarith
  exact hband (mem_iInter.mp hy N)

end CircleDomainRigidity

end

end OAI
