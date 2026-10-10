import Mathlib
import OAI.Combinatorics.KMedian.Process.CopyRound
import OAI.Combinatorics.KMedian.Process.CopyTransport
import OAI.Combinatorics.KMedian.Process.BackupGeometry
import OAI.Combinatorics.KMedian.Process.TaperGraph

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset PhysicalPotential FixedBatch
variable {F X : Type*} [Fintype F] [DecidableEq F] [PseudoMetricSpace X] {Δ : ℕ}

omit [Fintype F] in

theorem round_erasure_backup (A S₀ : Finset (Copy (F := F) Δ))
    (location : F → X) (client : X) {g P R : ℝ}
    (D : Taper.GraphData Δ g P (fun i : A => location i.val.1) (own Δ A))
    (G : A → Finset A) (H : Finset A) (Z : Finset (HeavyAction (graphActions G) H))
    (hg : 0 ≤ g) (hP : 0 < P) (hP1 : P ≤ 1/2) (hR : 0 ≤ R)
    (hS : S₀ ⊆ A) (hm : mass g S₀=1)
    (hd : ∀ i ∈ S₀, dist client (location i.1) ≤ R) (hgood : D.Good G)
    (herased : (S₀ ∩ roundErased A G H Z).Nonempty) :
    ∃ f ∈ roundOpened A G H Z, dist client (location f) ≤ 5*R := by
  obtain ⟨i,hi⟩ := herased
  obtain ⟨t,ht,hti⟩ := mem_image.mp (mem_inter.mp hi).2
  obtain ⟨e,he,hte⟩ := mem_biUnion.mp ht
  let a := heavyParent (graphActions G) H e
  have ha : a ∈ G t := (mem_graph_erase G _ _).mp (heavy_erase_parent (graphActions G) H e hte)
  have hiS : t ∈ localSet A S₀ := (mem_localSet A S₀ t).mpr (hti ▸ (mem_inter.mp hi).1)
  have hm' : ((localSet A S₀).card:ℝ)*g=1 := by
    rw [mul_comm,← mass,localSet_mass A S₀ hS,hm]
  have hn := Taper.backup_source_close (fun i : A => location i.val.1) client
    (localSet A S₀) D.radius D.marginal hg hP hP1 hR hm'
    (fun i hi => hd i.val ((mem_localSet A S₀ i).mp hi)) D.radius_nonneg D.marginal_nonneg
    (fun i _ => D.minimal i) D.upper hiS (hgood.2.2 a t ha)
  exact ⟨a.val.1,mem_image.mpr ⟨a,parent_selected G H Z he,rfl⟩,hn⟩

theorem round_backup (A S₀ : Finset (Copy (F := F) Δ))
    (location : F → X) (client : X) {g P R : ℝ}
    (D : Taper.GraphData Δ g P (fun i : A => location i.val.1) (own Δ A))
    (G : A → Finset A) (H : Finset A) (Z : Finset (HeavyAction (graphActions G) H))
    (hg : 0 ≤ g) (hP : 0 < P) (hP1 : P ≤ 1/2) (hR : 0 ≤ R)
    (hm : mass g S₀=1) (hd : ∀ i ∈ S₀, dist client (location i.1) ≤ R)
    (hgood : D.Good G)
    (hbackup : (¬∃ f ∈ integral Δ A, dist client (location f) ≤ 5*R) → S₀ ⊆ A) :
    (¬∃ f ∈ integral Δ (next Δ A (roundErased A G H Z) (roundOpened A G H Z)),
      dist client (location f) ≤ 5*R) →
      S₀ ⊆ next Δ A (roundErased A G H Z) (roundOpened A G H Z) := by
  intro hn
  have hnone : ¬∃ f ∈ integral Δ A, dist client (location f) ≤ 5*R := by
    rintro ⟨f,hf,hd⟩
    exact hn ⟨f,round_integral_persists A G H Z hgood.1 hgood.2.1 hf,hd⟩
  have hS := hbackup hnone
  intro i hi
  by_cases he : i ∈ roundErased A G H Z
  · obtain ⟨f,hf,hfd⟩ := round_erasure_backup A S₀ location client D G H Z hg hP hP1 hR
      hS hm hd hgood ⟨i,mem_inter.mpr ⟨hi,he⟩⟩
    exact False.elim (hn ⟨f,reset_integral Δ A _ _ hf,hfd⟩)
  · exact mem_union_left _ (mem_sdiff.mpr ⟨hS hi,he⟩)

end MetricKMedian.CopyState
end
end

end OAI
