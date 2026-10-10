import OAI.Probability.BenjaminiSchramm.LayerMonotoneLimit
import OAI.Probability.BenjaminiSchramm.SlabFractionalRecurrence

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma restrictedLayerCount_le_adjustedSlab (a : V → ℝ) (I : Set E) (A : Set V)
    (d c l u : ℝ) (ω : Set E) (x : V)
    (hI : I ⊆ Percolation.internalEdges G.ends
      {z | d ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ c})
    (hA : A ⊆ {z | l ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ u}) :
    restrictedLayerCount G.ends I A ω x ≤ G.adjustedSlabBandCount a d c l u ω x := by
  rw [G.adjustedSlabBandCount_eq_restricted]
  exact (restrictedLayerCount_mono_edges G.ends hI A ω x).trans
    (restrictedLayerCount_mono_vertices G.ends hA _ ω x)

lemma height_difference_jump (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (R : ℝ)
    (hjump : ∀ e u v, u ∈ G.ends e → v ∈ G.ends e →
      |G.orbitAdjustedHeight a u v| ≤ R) (x : V) :
    ∀ e u v, u ∈ G.ends e → v ∈ G.ends e →
      |G.orbitAdjustedHeight a x v-G.orbitAdjustedHeight a x u| ≤ R := by
  intro e u v hu hv
  have hh := G.orbitAdjustedHeight_change_base hc hl a x u v
  convert hjump e u v hu hv using 1
  congr 1
  linarith

lemma lower_extension_frontier_count_bound
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ)
    (R c : ℝ) (hc0 : 0 ≤ c) (n : ℕ) (x z : V)
    (hzlo : -((n+1 : ℕ) : ℝ)*R ≤ G.orbitAdjustedHeight a x z)
    (hzhi : G.orbitAdjustedHeight a x z < -(n : ℝ)*R) (ω : Set E) :
    restrictedLayerCount G.ends
      (Percolation.internalEdges G.ends {v | -((n : ℝ)+1)*R ≤ G.orbitAdjustedHeight a x v ∧
        G.orbitAdjustedHeight a x v ≤ c})
      {v | -R ≤ G.orbitAdjustedHeight a x v ∧ G.orbitAdjustedHeight a x v ≤ R} ω z ≤
      G.adjustedSlabBandCount a (-(c+R)) (-G.orbitAdjustedHeight a x z+(c+R))
        (-G.orbitAdjustedHeight a x z-R) (-G.orbitAdjustedHeight a x z+R) ω z := by
  have hcast : ((n+1 : ℕ) : ℝ)=(n : ℝ)+1 := by norm_cast
  rw [hcast] at hzlo
  apply G.restrictedLayerCount_le_adjustedSlab
  · apply Percolation.internalEdges_mono G.ends
    intro v hv
    have hh := G.orbitAdjustedHeight_change_base hc hl a x z v
    exact ⟨by linarith [hv.1],by linarith [hv.2]⟩
  · intro v hv
    have hh := G.orbitAdjustedHeight_change_base hc hl a x z v
    exact ⟨by linarith [hv.1],by linarith [hv.2]⟩

variable [Countable V] [Countable E]

theorem lower_extension_fractional_recurrence
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ)
    (d : ℕ) (hd : ∀ u, (Percolation.finite_neighbors hl u).toFinset.card ≤ d)
    (R c : ℝ) (hR : 0 ≤ R) (hc0 : 0 ≤ c)
    (hjump : ∀ e u v, u ∈ G.ends e → v ∈ G.ends e → |G.orbitAdjustedHeight a u v| ≤ R)
    (p : unitInterval) (hfin : ∀ x, ∀ᵐ ω ∂G.law p, (Percolation.cluster G.ends ω x).Finite)
    (n : ℕ) (x : V) {q t : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (ht : 0 < t) (ht1 : t ≤ 1)
    (L : ℝ≥0∞)
    (hL : ∀ z, -((n : ℝ)+1)*R ≤ G.orbitAdjustedHeight a x z →
      G.orbitAdjustedHeight a x z < -(n : ℝ)*R →
      (∫⁻ ω, (restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {v | -((n : ℝ)+1)*R ≤ G.orbitAdjustedHeight a x v ∧
          G.orbitAdjustedHeight a x v ≤ c})
        {v | -R ≤ G.orbitAdjustedHeight a x v ∧ G.orbitAdjustedHeight a x v ≤ R} ω z)^q ∂G.law p) ≤ L) :
    (∫⁻ ω, (G.adjustedSlabBandCount a (-((n : ℝ)+1)*R) c (-R) R ω x)^(q*t) ∂G.law p) ≤
      (∫⁻ ω, (G.adjustedSlabBandCount a (-(n : ℝ)*R) c (-R) R ω x)^(q*t) ∂G.law p)+
      (d : ℝ≥0∞)^t*
        (∫⁻ ω, (G.adjustedSlabBandCount a (-(n : ℝ)*R) c (-(n : ℝ)*R-R) (-(n : ℝ)*R+R) ω x)^t ∂G.law p)*L^t := by
  let f := fun z => -G.orbitAdjustedHeight a x z
  let I := Percolation.internalEdges G.ends
    {v | -(n : ℝ)*R ≤ G.orbitAdjustedHeight a x v ∧ G.orbitAdjustedHeight a x v ≤ c}
  let J := Percolation.internalEdges G.ends
    {v | -((n : ℝ)+1)*R ≤ G.orbitAdjustedHeight a x v ∧ G.orbitAdjustedHeight a x v ≤ c}
  let W := {v | -R ≤ G.orbitAdjustedHeight a x v ∧ G.orbitAdjustedHeight a x v ≤ R}
  have hIeq : Percolation.internalEdges G.ends {v | -c ≤ f v ∧ f v ≤ (n : ℝ)*R}=I := by
    congr 1
    ext v
    change (-c ≤ -G.orbitAdjustedHeight a x v ∧ -G.orbitAdjustedHeight a x v ≤ (n : ℝ)*R) ↔ _
    dsimp [I]
    constructor <;> intro hv <;> constructor <;> linarith [hv.1,hv.2]
  have hJ : J ⊆ Percolation.internalEdges G.ends {v | -c ≤ f v} :=
    Percolation.internalEdges_mono G.ends (fun v hv => by dsimp [f]; linarith [hv.2])
  have hj : ∀ e u v, u ∈ G.ends e → v ∈ G.ends e → |f v-f u| ≤ R := by
    intro e u v hu hv
    have hh := G.height_difference_jump hc hl a R hjump x e u v hu hv
    simpa only [f,neg_sub_neg,abs_sub_comm] using hh
  have hI : ∀ᵐ ω ∂G.law p, (Percolation.cluster G.ends (ω ∩ I) x).Finite := by
    filter_upwards [hfin x] with ω hω
    exact hω.subset fun v hv => Percolation.conn_mono G.ends inter_subset_left hv
  have hrec := lower_slab_fractional_recurrence G.ends hl d hd (fun _ => p) f R (-c) ((n : ℝ)*R)
    hj J hJ x (by simp only [f,G.orbitAdjustedHeight_self,neg_zero]; exact ⟨by linarith,by positivity⟩)
    (by simpa only [hIeq,CriticalPercolation.BernoulliProduct.law_const,CriticalPercolation.BondGraph.law] using hI) W hq hq1 ht ht1 L
    (fun z hzlo hzhi => by
      simpa only [J,W,CriticalPercolation.BernoulliProduct.law_const,CriticalPercolation.BondGraph.law] using
        hL z (by dsimp [f] at hzhi; linarith) (by dsimp [f] at hzlo; linarith))
  simp only [CriticalPercolation.BernoulliProduct.law_const] at hrec
  change (∫⁻ ω, restrictedLayerCount G.ends J W ω x^(q*t) ∂G.law p) ≤ _ at hrec
  rw [hIeq] at hrec
  simp only [G.adjustedSlabBandCount_eq_restricted]
  apply hrec.trans
  apply add_le_add le_rfl
  apply mul_le_mul' _ le_rfl
  apply mul_le_mul' le_rfl
  apply lintegral_mono
  intro ω
  apply ENNReal.rpow_le_rpow _ ht.le
  apply restrictedLayerCount_mono_vertices G.ends
  intro v hv
  dsimp [f] at hv
  exact ⟨by linarith [hv.2],by linarith [hv.1]⟩

end CriticalPercolation.BondGraph

end

end OAI
