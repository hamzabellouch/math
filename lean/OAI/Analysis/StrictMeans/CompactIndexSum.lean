import OAI.Analysis.StrictMeans.RegularLevels

namespace OAI

section
open Set Function Filter
open scoped Topology
namespace StrictInverseFirstPower.Grid
noncomputable section

lemma compact_sum_local_indices {u : ℂ → ℝ} {K : Set ℂ} (hK : IsCompact K)
    (C : Finset ℂ) (r : ℂ → ℝ) (sign : ℂ → ℤ)
    (hballs : ∀ p∈C, Metric.closedBall p (r p) ⊆ K)
    (hdisj : (C:Set ℂ).PairwiseDisjoint (fun p=>Metric.closedBall p (r p)))
    (hregular : ∀ z∈K, (∀ p∈C, r p≤dist z p) →
      ContDiffAt ℝ 1 u z ∧ fderiv ℝ u z≠0)
    (hlocal : ∀ p∈C, ∀ᶠ s in 𝓝 (0:ℝ), 0<s → ∀ (o : ℂ) (S : Finset Lattice),
      (∀ v, v∈S ↔ dist (meshPoint o s v) p≤r p) →
        ∑ v∈S, heightIndex (u ∘ meshPoint o s) ex ey v=sign p) :
    ∀ᶠ s in 𝓝 (0:ℝ), 0<s → ∀ (o : ℂ) (S : Finset Lattice),
      (∀ v, v∈S ↔ meshPoint o s v∈K) →
        ∑ v∈S, heightIndex (u ∘ meshPoint o s) ex ey v=∑ p∈C, sign p := by
  classical
  let A := K \ ⋃ p∈C, Metric.ball p (r p)
  have hA : IsCompact A := hK.diff (isOpen_biUnion (fun p _=>Metric.isOpen_ball))
  have hreg : ∀ z∈A, ∃ L : ℂ →L[ℝ] ℝ,
      HasStrictFDerivAt u L z ∧ (L 1≠0 ∨ L Complex.I≠0) := by
    intro z hz
    have hh := hregular z hz.1 (by
      intro p hp
      exact le_of_not_gt (fun hb=>hz.2 (mem_iUnion.mpr ⟨p,mem_iUnion.mpr ⟨hp,hb⟩⟩)))
    refine ⟨fderiv ℝ u z,hh.1.hasStrictFDerivAt one_ne_zero,?_⟩
    by_contra h
    push Not at h
    exact hh.2 (realCLM_eq_zero h.1 h.2)
  have hg := compact_regular_star hA (by simp : ‖(1:ℂ)‖≤1) (by simp : ‖Complex.I‖≤1) hreg
  have hl := (C.eventually_all).mpr hlocal
  filter_upwards [hg,hl] with s hs hs'
  intro hspos o S hS
  let L : ℂ → Finset Lattice := fun p=>(meshPoint_bounded_preimage (o:=o) hspos.ne'
    (Metric.isBounded_closedBall (x:=p) (r:=r p))).toFinset
  have hL (p : ℂ) (v : Lattice) : v∈L p ↔ dist (meshPoint o s v) p≤r p := by
    simp only [L,Set.Finite.mem_toFinset,mem_preimage,Metric.mem_closedBall]
  let T := C.biUnion L
  have hTS : T⊆S := by
    intro v hv
    obtain ⟨p,hp,hv⟩ := Finset.mem_biUnion.mp hv
    exact (hS v).mpr (hballs p hp ((hL p v).mp hv))
  have hzero : ∀ v∈S, v∉T → heightIndex (u ∘ meshPoint o s) ex ey v=0 := by
    intro v hv hvt
    have hva : meshPoint o s v∈A := by
      refine ⟨(hS v).mp hv,?_⟩
      intro hm
      obtain ⟨p,hp,hm⟩ := mem_iUnion₂.mp hm
      apply hvt
      exact Finset.mem_biUnion.mpr ⟨p,hp,(hL p v).mpr hm.le⟩
    exact RegularStar.index_zero ((hs _ hva hspos).toRegularStar)
  have hpair : (C:Set ℂ).PairwiseDisjoint L := by
    intro p hp q hq hpq
    apply Finset.disjoint_left.mpr
    intro v hvp hvq
    exact Set.disjoint_left.mp (hdisj hp hq hpq) ((hL p v).mp hvp) ((hL q v).mp hvq)
  calc
    ∑ v∈S, heightIndex (u ∘ meshPoint o s) ex ey v = ∑ v∈T, heightIndex (u ∘ meshPoint o s) ex ey v :=
      (Finset.sum_subset hTS (fun v hv hvt=>hzero v hv hvt)).symm
    _ = ∑ p∈C, ∑ v∈L p, heightIndex (u ∘ meshPoint o s) ex ey v := Finset.sum_biUnion hpair
    _ = ∑ p∈C, sign p := Finset.sum_congr rfl (fun p hp=>hs' p hp hspos o (L p) (hL p))

end
end StrictInverseFirstPower.Grid

end

end OAI
