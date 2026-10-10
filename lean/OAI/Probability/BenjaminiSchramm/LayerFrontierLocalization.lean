import OAI.Probability.BenjaminiSchramm.LayerFrontierExpectation

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma restrictedLayerCount_eq_card (I : Set E) (A : Set V) (ω : Set E) (x : V)
    (F : Finset V) (hF : ∀ y, y ∈ F ↔ y ∈ A ∧ Conn G (ω ∩ I) x y) :
    restrictedLayerCount G I A ω x = F.card := by
  unfold restrictedLayerCount
  rw [tsum_eq_sum (s := F) (fun y hy => ite_eq_right (fun hh => hy ((hF y).mpr hh)))]
  calc
    _ = ∑ _y ∈ F, (1 : ℝ≥0∞) :=
      Finset.sum_congr rfl (fun y hy => ite_eq_left ((hF y).mp hy))
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,mul_one]

theorem frontierCount_le_boundary_layer (hloc : LocallyFinite G) (d : ℕ)
    (hd : ∀ u, (finite_neighbors hloc u).toFinset.card ≤ d)
    (I J : Set E) (ω : Set E) (x : V) (A : Set V)
    (hfin : (cluster G (ω ∩ I) x).Finite)
    (hA : ∀ u ∈ cluster G (ω ∩ I) x, ∀ z ∉ cluster G (ω ∩ I) x,
      ∀ e ∈ ω ∩ J, G e = s(u,z) → u ∈ A) :
    frontierCount G I J ω x ≤ (d : ℝ≥0∞)*restrictedLayerCount G I A ω x := by
  let C := cluster G (ω ∩ I) x
  have hCA : (C ∩ A).Finite := hfin.inter_of_left A
  let S := hCA.toFinset
  have hF := openFrontier_finite G hloc (ω ∩ J) hfin
  let F := hF.toFinset
  have hcover : F ⊆ S.biUnion (fun u => (finite_neighbors hloc u).toFinset) := by
    intro z hz
    obtain ⟨hz,u,hu,e,he,heq⟩ := hF.mem_toFinset.mp hz
    exact Finset.mem_biUnion.mpr ⟨u,hCA.mem_toFinset.mpr ⟨hu,hA u hu z hz e he heq⟩,
      (finite_neighbors hloc u).mem_toFinset.mpr ⟨e,heq⟩⟩
  have hcard : F.card ≤ S.card*d :=
    (Finset.card_le_card hcover).trans (Finset.card_biUnion_le.trans
      ((Finset.sum_le_sum (fun u _ => hd u)).trans_eq (by simp)))
  have hcount : restrictedLayerCount G I A ω x = S.card :=
    restrictedLayerCount_eq_card G I A ω x S (fun y => by
      rw [hCA.mem_toFinset]
      exact and_comm)
  have hfcount : frontierCount G I J ω x = F.card :=
    frontierCount_eq_card_on_cell G I J x C F
      ⟨rfl,hF.coe_toFinset.symm⟩
  rw [hfcount,hcount,mul_comm]
  exact_mod_cast hcard

theorem lower_halfspace_frontier_incident_top_band
    (f : V → ℝ) (R b : ℝ)
    (hjump : ∀ e u v, u ∈ G e → v ∈ G e → |f v-f u| ≤ R)
    (ω : Set E) (J : Set E) (x : V) (hx : f x ≤ b)
    {u z : V} (hu : u ∈ cluster G (ω ∩ internalEdges G {v | f v ≤ b}) x)
    (hz : z ∉ cluster G (ω ∩ internalEdges G {v | f v ≤ b}) x)
    {e : E} (he : e ∈ ω ∩ J) (heq : G e = s(u,z)) :
    b-R ≤ f u ∧ f u ≤ b := by
  have hub := conn_internalEdges_end_mem G ω {v | f v ≤ b} hx hu
  have hzb : ¬f z ≤ b := openFrontier_lowerCluster_outside G ω
    {v | f v ≤ b} x hx ⟨hz,u,hu,e,he.1,heq⟩
  have hj := (abs_le.mp (hjump e u z (by rw [heq]; simp) (by rw [heq]; simp))).2
  exact ⟨by linarith,hub⟩

theorem lower_halfspace_frontierCount_le_top_band
    (hloc : LocallyFinite G) (d : ℕ)
    (hd : ∀ u, (finite_neighbors hloc u).toFinset.card ≤ d)
    (f : V → ℝ) (R b : ℝ)
    (hjump : ∀ e u v, u ∈ G e → v ∈ G e → |f v-f u| ≤ R)
    (ω : Set E) (J : Set E) (x : V) (hx : f x ≤ b)
    (hfin : (cluster G (ω ∩ internalEdges G {v | f v ≤ b}) x).Finite) :
    frontierCount G (internalEdges G {v | f v ≤ b}) J ω x ≤
      (d : ℝ≥0∞)*restrictedLayerCount G (internalEdges G {v | f v ≤ b})
        {u | b-R ≤ f u ∧ f u ≤ b} ω x := by
  exact frontierCount_le_boundary_layer G hloc d hd _ J ω x _ hfin
    (fun _ hu _ hz _ he heq =>
      lower_halfspace_frontier_incident_top_band G f R b hjump ω J x hx hu hz he heq)

end Percolation.BenjaminiSchramm

end

end OAI
