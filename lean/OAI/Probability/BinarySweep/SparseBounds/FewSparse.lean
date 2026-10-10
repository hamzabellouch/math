import Mathlib
import OAI.Probability.BinarySweep.TensorBounds.SignedPlacement
import OAI.Probability.BinarySweep.SparseBounds.FewSparseBases
import OAI.Probability.BinarySweep.SparseBounds.FewSparseNumerics
import OAI.Probability.BinarySweep.Trajectories.EndpointGood

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

section
open Sparse Young Irrep

theorem centeredEndpointHS_few_sparse {b r h k : ℕ} {bits : Fin b → ℕ}
    (hb : 1 ≤ b) (hbB : b ≤ 16000) (hd : ∀j, r ≤ bits j ∧ bits j ≤ 2*r)
    (hL : (10:ℝ)^26 ≤ Real.log (gridSize bits)) (hk : 1 ≤ k)
    (htail : ((k+h:ℕ):ℝ) ≤ (gridSize bits:ℝ)^(1599/1600:ℝ)) (hh : h ≤ 100000*k)
    (H : PathFamily bits h) :
    (∑x : Placement H k 0, ∑y : Placement H k (Fin.last b),
      (centeredEndpointKernel H 0 (fun i => ((x i).val,(y i).val)))^2) ≤
      Real.exp (-(k:ℝ)*Real.log (gridSize bits)/1000000000000) := by
  let L := Real.log (gridSize bits)
  let η := Real.exp (-L/160000)
  have hs : (0:ℝ) < gridSize bits := by exact_mod_cast gridSize_pos bits
  have hL0 : 0 ≤ L := (by positivity : (0:ℝ) ≤ 10^26).trans hL
  obtain ⟨hη1,hg⟩ := few_eta_good b hbB hL
  have hv := few_vertex_base b h k hs hbB hL htail
  have hx := few_line_base h h k hs hL htail (by omega)
  have hy := few_line_base k h k hs hL htail (by omega)
  have he (a : ℝ) (ha : 0 < a) : Real.exp (-L/a) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hL0) ha.le
  obtain ⟨ht,htv,htl⟩ := few_cutoff_bounds b k hb hbB
  have hbound := centeredEndpointKernel_few_hs H (fun j => (hd j).2)
    (Real.exp_pos (-L/160000)) hη1 (hg.trans (he _ (by norm_num)))
    (k/4+1) (k/(8*b)+1) ht (hv.trans (he _ (by norm_num)))
    (hx.trans (he _ (by norm_num))) (hy.trans (he _ (by norm_num)))
  apply hbound.trans
  apply few_hs_scalar b h k (k/4+1) (k/(8*b)+1)
    (fun j => (Fintype.card (GridOutside bits j)+1:ℕ)^⌊2*(k:ℝ)/((2^bits j:ℕ)*η)⌋₊)
    hbB hk (by exact_mod_cast hh) hL htv htl (by positivity) hg (by positivity) hv
    (by positivity) hx (by positivity) hy (fun _ => by positivity)
  intro j
  convert adaptive_count_small (Fintype.card (GridOutside bits j)) k hs hL
    (outside_card_add_one_le bits j) (few_axis_eta_large hbB hd hL j) using 1
  push_cast
  rfl

theorem conditional_specht_few_sparse {b r h k : ℕ} {bits : Fin b → ℕ}
    (hb : 1 ≤ b) (hbB : b ≤ 16000) (hd : ∀j, r ≤ bits j ∧ bits j ≤ 2*r)
    (hL : (10:ℝ)^26 ≤ Real.log (gridSize bits)) (hk : 1 ≤ k)
    (htail : ((k+h:ℕ):ℝ) ≤ (gridSize bits:ℝ)^(1599/1600:ℝ)) (hh : h ≤ 100000*k)
    (H : PathFamily bits h) (μ : YoungDiagram) (e : Cell μ ≃ FreeSlot H 0)
    (a : Tail μ ≃ Fin k) :
    evenMoment 1 (groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
      (fun g => (conditionalGroupLaw H 0 g:ℂ))) ≤
      Real.exp (-(k:ℝ)*Real.log (gridSize bits)/1000000000000) :=
  (conditional_specht_hs H μ e a 0).trans
    (centeredEndpointHS_few_sparse hb hbB hd hL hk htail hh H)

end

lemma sparse_tail_le_quarter {s : ℝ} (hs : 0 < s) (hL : (10:ℝ)^26 ≤ Real.log s) :
    s^(1599/1600:ℝ) ≤ s/4 := by
  have hc : (4:ℝ) ≤ Real.exp (Real.log s/1600) :=
    (show (4:ℝ) ≤ Real.log s/1600+1 from by linarith).trans (Real.add_one_le_exp _)
  apply (le_div_iff₀ (by norm_num : (0:ℝ)<4)).mpr
  calc
    _ ≤ Real.exp ((1599/1600:ℝ)*Real.log s)*Real.exp (Real.log s/1600) := by
      rw [Real.rpow_def_of_pos hs]
      simpa only [mul_comm (Real.log s)] using mul_le_mul_of_nonneg_left hc
        (Real.exp_pos ((1599/1600:ℝ)*Real.log s)).le
    _ = s := by rw [←Real.exp_add,show (1599/1600:ℝ)*Real.log s+Real.log s/1600=Real.log s by ring,Real.exp_log hs]

lemma few_sparse_sign_geometry {b h k : ℕ} {bits : Fin b → ℕ}
    (hL : (10:ℝ)^26 ≤ Real.log (gridSize bits))
    (htail : ((k+h:ℕ):ℝ) ≤ (gridSize bits:ℝ)^(1599/1600:ℝ))
    (j : Fin b) (hj : 2 ≤ bits j) :
    h+k+Fintype.card (GridOutside bits j) < gridSize bits := by
  have hs : (0:ℝ) < gridSize bits := by exact_mod_cast gridSize_pos bits
  have hquarter := htail.trans (sparse_tail_le_quarter hs hL)
  have ha : 4 ≤ 2^bits j := (show 4=2^2 by norm_num) ▸ Nat.pow_le_pow_right (by omega : 1 ≤ 2) hj
  have ho : 4*Fintype.card (GridOutside bits j) ≤ gridSize bits := by
    have he := outside_card_mul_axis bits j
    nlinarith [Nat.mul_le_mul_left (Fintype.card (GridOutside bits j)) ha]
  have hoR : (4:ℝ)*Fintype.card (GridOutside bits j) ≤ gridSize bits := by exact_mod_cast ho
  have hl : ((h+k+Fintype.card (GridOutside bits j):ℕ):ℝ) < gridSize bits := by
    push_cast at hquarter ⊢
    linarith
  exact_mod_cast hl

lemma many_sparse_sign_geometry {b h k : ℕ} {bits : Fin b → ℕ}
    (hbase : ((k+h:ℕ):ℝ)*(∑j : Fin b, (1:ℝ)/Fintype.card (GridOutside bits j)) < 1)
    (j : Fin b) : h+k < Fintype.card (GridOutside bits j) := by
  have hp : (0:ℝ) < Fintype.card (GridOutside bits j) := by exact_mod_cast Fintype.card_pos
  have he : (1:ℝ)/Fintype.card (GridOutside bits j) ≤
      ∑j : Fin b, (1:ℝ)/Fintype.card (GridOutside bits j) :=
    Finset.single_le_sum (f := fun j : Fin b => (1:ℝ)/Fintype.card (GridOutside bits j)) (fun _ _ => by positivity) (Finset.mem_univ j)
  have hh := (mul_le_mul_of_nonneg_left he (show (0:ℝ) ≤ (k+h:ℕ) by positivity)).trans_lt hbase
  rw [mul_one_div] at hh
  have hl := (div_lt_one hp).mp hh
  simpa only [Nat.add_comm] using (show k+h < Fintype.card (GridOutside bits j) by exact_mod_cast hl)

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical
open Filter Topology

namespace BinaryCoordinateSweeps

instance finitePathFamily {b h : ℕ} {bits : Fin b → ℕ} : Finite (PathFamily bits h) :=
  Finite.of_injective PathFamily.position (by
    intro H J he
    cases H
    cases J
    cases he
    rfl)

def sparseEndpointBound {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h) (k : ℕ) (z : ℝ) : Prop :=
    (∑x : Placement H k 0, ∑y : Placement H k (Fin.last b),
      (centeredEndpointKernel H z (fun i => ((x i).val,(y i).val)))^2) ≤
        Real.exp (-(k:ℝ)*Real.log (gridSize bits)/2000000000000) ∧
    signedCenteredHS H k z ≤ Real.exp (-(k:ℝ)*Real.log (gridSize bits)/2000000000000)

lemma sparseEndpointBound_eventually {b r h k : ℕ} {bits : Fin b → ℕ}
    (hb : 1 ≤ b) (hbB : b ≤ 16000) (hr : 2 ≤ r) (hd : ∀j, r ≤ bits j ∧ bits j ≤ 2*r)
    (hL : (10:ℝ)^26 ≤ Real.log (gridSize bits)) (hk : 1 ≤ k)
    (htail : ((k+h:ℕ):ℝ) ≤ (gridSize bits:ℝ)^(1599/1600:ℝ)) (hh : h ≤ 100000*k)
    (H : PathFamily bits h) : ∀ᶠ z in 𝓝 0, sparseEndpointBound H k z := by
  have hbound := centeredEndpointHS_few_sparse hb hbB hd hL hk htail hh H
  have hstrict : (∑x : Placement H k 0, ∑y : Placement H k (Fin.last b),
      (centeredEndpointKernel H 0 (fun i => ((x i).val,(y i).val)))^2) <
        Real.exp (-(k:ℝ)*Real.log (gridSize bits)/2000000000000) := by
    apply hbound.trans_lt (Real.exp_lt_exp.mpr ?_)
    have hkR : (0:ℝ) < k := by exact_mod_cast hk
    have hKL : 0 < (k:ℝ)*Real.log (gridSize bits) := mul_pos hkR (by linarith)
    linarith
  let j : Fin b := ⟨0,by omega⟩
  have hgeom := few_sparse_sign_geometry hL htail j (hr.trans (hd j).1)
  have hzero : signedCenteredHS H k 0=0 := signedCenteredHS_zero H k 0 (fun l hl x y =>
    signedPlacementEntry_zero_few H j (by omega) x y)
  have hsigned : signedCenteredHS H k 0 < Real.exp (-(k:ℝ)*Real.log (gridSize bits)/2000000000000) := by
    rw [hzero]
    exact Real.exp_pos _
  filter_upwards [(continuousAt_centeredEndpointHS H k).eventually_lt continuousAt_const hstrict,
    (continuousAt_signedCenteredHS H k).eventually_lt continuousAt_const hsigned] with z h1 h2
  exact ⟨h1.le,h2.le⟩

theorem sparse_finite_radius (r : ℕ) (hr : 2 ≤ r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ b : ℕ, 1 ≤ b → b ≤ 16000 →
      ∀bits : Fin b → ℕ, (∀j, r ≤ bits j ∧ bits j ≤ 2*r) →
      ∀h k : ℕ, h ≤ gridSize bits → k ≤ gridSize bits →
      (10:ℝ)^26 ≤ Real.log (gridSize bits) → 1 ≤ k →
      ((k+h:ℕ):ℝ) ≤ (gridSize bits:ℝ)^(1599/1600:ℝ) → h ≤ 100000*k →
      ∀H : PathFamily bits h, ∀z : ℝ, 0 ≤ z → z ≤ δ → sparseEndpointBound H k z := by
  have hev : ∀ᶠ z : ℝ in 𝓝 0,
      ∀b : Fin 16001, ∀ds : Fin b.val → Fin (2*r+1),
      ∀h : Fin (gridSize (fun j => (ds j).val)+1),
      ∀k : Fin (gridSize (fun j => (ds j).val)+1),
      ∀H : PathFamily (fun j => (ds j).val) h.val,
      (1 ≤ b.val ∧ (∀j, r ≤ (ds j).val) ∧
        (10:ℝ)^26 ≤ Real.log (gridSize (fun j => (ds j).val)) ∧ 1 ≤ k.val ∧
        ((k.val+h.val:ℕ):ℝ) ≤ (gridSize (fun j => (ds j).val):ℝ)^(1599/1600:ℝ) ∧
        h.val ≤ 100000*k.val) → sparseEndpointBound H k.val z := by
    apply eventually_all.mpr
    intro b
    apply eventually_all.mpr
    intro ds
    apply eventually_all.mpr
    intro h
    apply eventually_all.mpr
    intro k
    apply eventually_all.mpr
    intro H
    by_cases hc : 1 ≤ b.val ∧ (∀j, r ≤ (ds j).val) ∧
        (10:ℝ)^26 ≤ Real.log (gridSize (fun j => (ds j).val)) ∧ 1 ≤ k.val ∧
        ((k.val+h.val:ℕ):ℝ) ≤ (gridSize (fun j => (ds j).val):ℝ)^(1599/1600:ℝ) ∧
        h.val ≤ 100000*k.val
    · filter_upwards [sparseEndpointBound_eventually hc.1 (by omega) hr
        (fun j => ⟨hc.2.1 j,by have := (ds j).isLt; omega⟩)
        hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2 H] with z hz
      exact fun _ => hz
    · exact Eventually.of_forall (fun _ h => False.elim (hc h))
  obtain ⟨ε,hε,he⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ε/2,by linarith,?_⟩
  intro b hb hbB bits hd h k hh hk hL hk0 htail hholes H z hz hze
  have hdist : dist z 0 < ε := by rw [Real.dist_eq,sub_zero,abs_of_nonneg hz]; linarith
  exact he hdist ⟨b,by omega⟩ (fun j => ⟨bits j,(hd j).2.trans_lt (Nat.lt_succ_self _)⟩)
    ⟨h,by change h < gridSize bits+1; omega⟩ ⟨k,by change k < gridSize bits+1; omega⟩ H ⟨hb,fun j => (hd j).1,hL,hk0,htail,hholes⟩

end BinaryCoordinateSweeps

end

end OAI
