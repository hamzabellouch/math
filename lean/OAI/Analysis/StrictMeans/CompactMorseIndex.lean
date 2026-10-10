import OAI.Analysis.StrictMeans.CompactIndexSum

namespace OAI

section
open Set Function Filter
open scoped Topology
namespace StrictInverseFirstPower.Grid
noncomputable section

lemma compact_morse_index_sum {u : ℂ → ℝ} {K : Set ℂ} (hK : IsCompact K)
    (C : Finset ℂ) (hc : ∀ z∈K, fderiv ℝ u z=0 ↔ z∈C)
    (hC : ∀ p∈C, p∈interior K)
    (hu : ∀ p∈K, ContDiffAt ℝ 2 u p)
    (htr : ∀ p∈C, 0<second u p 1 1+second u p Complex.I Complex.I)
    (hdet : ∀ p∈C, hessianDet u p≠0) :
    ∀ᶠ s in 𝓝 (0:ℝ), 0<s → ∀ (o : ℂ) (S : Finset Lattice),
      (∀ v, v∈S ↔ meshPoint o s v∈K) →
        ∑ v∈S, heightIndex (u ∘ meshPoint o s) ex ey v=∑ p∈C, morseSign u p := by
  classical
  have hchoose : ∀ p : ℂ, ∃ r>0, p∈C →
      (Metric.closedBall p r⊆K) ∧
      (∀ q∈C, q≠p → 3*r<dist p q) ∧
      (∀ᶠ s in 𝓝 (0:ℝ), 0<s → ∀ (o : ℂ) (S : Finset Lattice),
        (∀ v, v∈S ↔ dist (meshPoint o s v) p≤r) →
          ∑ v∈S, heightIndex (u ∘ meshPoint o s) ex ey v=morseSign u p) := by
    intro p
    by_cases hp : p∈C
    · have hpK := interior_subset (hC p hp)
      obtain ⟨R,hR,hlocal⟩ := smooth_morse_local_index (hu p hpK) ((hc p hpK).mpr hp)
        (htr p hp) (hdet p hp)
      obtain ⟨ρ,hρ,hnb⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp (hC p hp))
      have hsep : ∀ᶠ r in 𝓝 (0:ℝ), ∀ q∈C, q≠p → r<dist p q/3 := by
        apply (C.eventually_all).mpr
        intro q hq
        by_cases hqp : q=p
        · exact Filter.Eventually.of_forall (fun _ h=>False.elim (h hqp))
        · exact (gt_mem_nhds (by simpa using (div_pos (dist_pos.mpr (Ne.symm hqp)) (by norm_num : (0:ℝ)<3)))).mono
            (fun _ hh _=>hh)
      obtain ⟨r,hr,hrr,hrr',hrs⟩ := ((gt_mem_nhds hR).and ((gt_mem_nhds hρ).and hsep)).exists_gt
      refine ⟨r,hr,fun _=>⟨?_,?_,hlocal r ⟨hr,hrr⟩⟩⟩
      · intro z hz
        exact hnb (lt_of_le_of_lt hz hrr')
      · intro q hq hqp
        have := hrs q hq hqp
        linarith
    · exact ⟨1,by norm_num,fun h=>False.elim (hp h)⟩
  choose r hrpos hr using hchoose
  apply compact_sum_local_indices hK C r (morseSign u) (fun p hp=>(hr p hp).1) ?_ ?_
    (fun p hp=>(hr p hp).2.2)
  · intro p hp q hq hpq
    apply Set.disjoint_left.mpr
    intro z hpz hqz
    have ha := (hr p hp).2.1 q hq hpq.symm
    have hb := (hr q hq).2.1 p hp hpq
    rw [dist_comm q p] at hb
    have ht := dist_triangle p z q
    rw [dist_comm p z] at ht
    change dist z p≤r p at hpz
    change dist z q≤r q at hqz
    linarith [dist_nonneg (x:=p) (y:=q)]
  · intro z hz hdist
    refine ⟨(hu z hz).of_le (by norm_num),?_⟩
    intro hzero
    have hzC := (hc z hz).mp hzero
    have hd := hdist z hzC
    rw [dist_self] at hd
    exact (not_le_of_gt (hrpos z)) hd

end
end StrictInverseFirstPower.Grid

end

end OAI
