import OAI.Combinatorics.HoneycombChords.ColumnProjection

namespace OAI

/-! Column positivity for critical honeycomb strips.

The formulas follow the finite strip transfer calculation in the companion paper
on uniform marked polygon estimates. -/

section
namespace CriticalHoneycomb.Transfer.RasterGrid
open PhysicalTiles CenterPartition ChordOrientations FiniteConfigurations FiniteContinuation
open Filter Topology
open scoped Matrix
lemma row_vacuum (W H : ℕ) : (rowTransfer W^H) (fun _=>1) (fun _=>1)=1 :=
  physical_vacuum_entry W H
lemma actual_any_cut_bound {W H k j : ℕ} (hk : k≤j) (hj : j+k≤H)
    (south north : Column (W+1)) :
    ‖(rowTransfer (W+1)^(H+1)) south north-
      (rowTransfer (W+1)^j) south (fun _=>1)*
      (rowTransfer (W+1)^(H-j)) (fun _=>1) north‖ ≤ AnyRow.rowErrorBound W H k := by
  rw [transfer_cut_difference south north (⟨j,by omega⟩ : Fin (H+1))]
  obtain ⟨hw,he⟩:=hardAssignment_walls (H:=H) south north
  exact AnyRow.actual_cutrow_bound hk hj _ hw he
lemma vacuum_column_cauchy (W : ℕ) (s : Column (W+1)) :
    CauchySeq (fun H=>(rowTransfer (W+1)^(H+1)) s (fun _=>1)) := by
  apply AnyRow.cauchy_of_cut_approximation _ (fun k=>(rowTransfer (W+1)^k) s (fun _=>1))
    (fun k H=>AnyRow.rowErrorBound W H k) (AnyRow.rowLimitError W)
    (AnyRow.rowErrorBound_limit W) (AnyRow.rowLimitError_limit W)
  intro k
  filter_upwards [eventually_ge_atTop (2*k)] with H hH
  have hh:=actual_any_cut_bound (W:=W) (H:=H) (j:=k) (k:=k) le_rfl (by omega) s (fun _=>1)
  simpa only [row_vacuum,mul_one] using hh
lemma vacuum_row_cauchy (W : ℕ) (s : Column (W+1)) :
    CauchySeq (fun H=>(rowTransfer (W+1)^(H+1)) (fun _=>1) s) := by
  apply AnyRow.cauchy_of_cut_approximation _ (fun k=>(rowTransfer (W+1)^k) (fun _=>1) s)
    (fun k H=>AnyRow.rowErrorBound W H k) (AnyRow.rowLimitError W)
    (AnyRow.rowErrorBound_limit W) (AnyRow.rowLimitError_limit W)
  intro k
  filter_upwards [eventually_ge_atTop (2*k)] with H hH
  have hh:=actual_any_cut_bound (W:=W) (H:=H) (j:=H-k) (k:=k) (by omega) (by omega) (fun _=>1) s
  have he : H-(H-k)=k := by omega
  simpa only [row_vacuum,one_mul,he] using hh
end CriticalHoneycomb.Transfer.RasterGrid

namespace CriticalHoneycomb.Transfer.RasterGrid
open PhysicalTiles Filter Topology
open scoped Matrix
lemma exists_vacuum_column_limit (W : ℕ) (s : Column (W+1)) :
    ∃ a : ℂ,Tendsto (fun H=>(rowTransfer (W+1)^H) s (fun _=>1)) atTop (𝓝 a) := by
  obtain ⟨a,ha⟩:=cauchySeq_tendsto_of_complete (vacuum_column_cauchy W s)
  exact ⟨a,(tendsto_add_atTop_iff_nat 1).mp ha⟩
lemma exists_vacuum_row_limit (W : ℕ) (s : Column (W+1)) :
    ∃ a : ℂ,Tendsto (fun H=>(rowTransfer (W+1)^H) (fun _=>1) s) atTop (𝓝 a) := by
  obtain ⟨a,ha⟩:=cauchySeq_tendsto_of_complete (vacuum_row_cauchy W s)
  exact ⟨a,(tendsto_add_atTop_iff_nat 1).mp ha⟩
noncomputable def archColumn (W : ℕ) (s : Column (W+1)) : ℂ :=
  (exists_vacuum_column_limit W s).choose
noncomputable def archRow (W : ℕ) (s : Column (W+1)) : ℂ :=
  (exists_vacuum_row_limit W s).choose
lemma archColumn_limit (W : ℕ) (s : Column (W+1)) :
    Tendsto (fun H=>(rowTransfer (W+1)^H) s (fun _=>1)) atTop (𝓝 (archColumn W s)) :=
  (exists_vacuum_column_limit W s).choose_spec
lemma archRow_limit (W : ℕ) (s : Column (W+1)) :
    Tendsto (fun H=>(rowTransfer (W+1)^H) (fun _=>1) s) atTop (𝓝 (archRow W s)) :=
  (exists_vacuum_row_limit W s).choose_spec
lemma archColumn_vacuum (W : ℕ) : archColumn W (fun _=>1)=1 := by
  apply tendsto_nhds_unique (archColumn_limit W _)
  simpa only [row_vacuum] using (tendsto_const_nhds : Tendsto (fun _ : ℕ=>(1:ℂ)) atTop (𝓝 1))
lemma archRow_vacuum (W : ℕ) : archRow W (fun _=>1)=1 := by
  apply tendsto_nhds_unique (archRow_limit W _)
  simpa only [row_vacuum] using (tendsto_const_nhds : Tendsto (fun _ : ℕ=>(1:ℂ)) atTop (𝓝 1))

theorem physical_rank_one_limit (W : ℕ) (s n : Column (W+1)) :
    Tendsto (fun H=>(rowTransfer (W+1)^H) s n) atTop
      (𝓝 (archColumn W s*archRow W n)) := by
  have ht : Tendsto (fun H : ℕ=>H/2) atTop atTop := by
    exact le_of_eq (map_div_atTop_eq_nat 2 (by omega))
  have hu : Tendsto (fun H : ℕ=>H-H/2) atTop atTop := by
    apply tendsto_atTop_mono _ ht
    intro H
    omega
  have hp:=((archColumn_limit W s).comp ht).mul ((archRow_limit W n).comp hu)
  have he : Tendsto (fun H=>(rowTransfer (W+1)^(H+1)) s n-
      (rowTransfer (W+1)^(H/2)) s (fun _=>1)*
      (rowTransfer (W+1)^(H-H/2)) (fun _=>1) n) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun H=>norm_nonneg _) (fun H=>actual_transfer_cut_bound W H s n)
      (middleErrorBound_limit W)
  apply (tendsto_add_atTop_iff_nat 1).mp
  convert he.add hp using 1 <;> simp
end CriticalHoneycomb.Transfer.RasterGrid

end

section
namespace CriticalHoneycomb.Transfer.RasterGrid
open Filter Topology PhysicalTiles
open scoped Matrix
noncomputable def archProjection (W : ℕ) : Matrix (Column (W+1)) (Column (W+1)) ℂ :=
  fun s n=>archColumn W s*archRow W n
lemma physical_matrix_limit (W : ℕ) :
    Tendsto (fun H=>rowTransfer (W+1)^H) atTop (𝓝 (archProjection W)) := by
  apply tendsto_pi_nhds.mpr
  intro s
  apply tendsto_pi_nhds.mpr
  intro n
  exact physical_rank_one_limit W s n
lemma projection_vacuum (W : ℕ) : archProjection W (fun _=>1) (fun _=>1)=1 := by
  simp [archProjection,archColumn_vacuum,archRow_vacuum]
lemma projection_mul_transfer (W : ℕ) : archProjection W*rowTransfer (W+1)=archProjection W := by
  have h1:=(physical_matrix_limit W).mul (tendsto_const_nhds (x:=rowTransfer (W+1)))
  have h2:=(physical_matrix_limit W).comp (tendsto_add_atTop_nat 1)
  simp only [Function.comp_def,pow_succ] at h2
  exact tendsto_nhds_unique h1 h2
lemma transfer_mul_projection (W : ℕ) : rowTransfer (W+1)*archProjection W=archProjection W := by
  have h1:=(tendsto_const_nhds (x:=rowTransfer (W+1))).mul (physical_matrix_limit W)
  have h2:=(physical_matrix_limit W).comp (tendsto_add_atTop_nat 1)
  simp only [Function.comp_def,pow_succ'] at h2
  exact tendsto_nhds_unique h1 h2
lemma projection_idempotent (W : ℕ) : archProjection W*archProjection W=archProjection W := by
  have ht : Tendsto (fun H : ℕ=>H+H) atTop atTop :=
    tendsto_atTop_mono (fun H=>Nat.le_add_right H H) tendsto_id
  have h1:=(physical_matrix_limit W).mul (physical_matrix_limit W)
  have h2:=(physical_matrix_limit W).comp ht
  simp only [Function.comp_def,pow_add] at h2
  exact tendsto_nhds_unique h1 h2
lemma arch_pairing (W : ℕ) : (∑ s,archRow W s*archColumn W s)=1 := by
  have h:=congrFun (congrFun (projection_idempotent W) (fun _=>1)) (fun _=>1)
  simpa [Matrix.mul_apply,archProjection,archColumn_vacuum,archRow_vacuum] using h
lemma projection_mulVec (W : ℕ) (v : Column (W+1)→ℂ) :
    (archProjection W).mulVec v=(∑ s,archRow W s*v s) • archColumn W := by
  funext s
  simp only [Matrix.mulVec,dotProduct,archProjection,Pi.smul_apply,smul_eq_mul]
  simp_rw [mul_assoc]
  rw [←Finset.mul_sum,mul_comm]
lemma archColumn_eigen (W : ℕ) :
    (rowTransfer (W+1)).mulVec (archColumn W)=archColumn W := by
  have h:=transfer_mul_projection W
  funext s
  have hs:=congrFun (congrFun h s) (fun _=>1)
  simpa [Matrix.mul_apply,Matrix.mulVec,dotProduct,archProjection,archRow_vacuum] using hs
lemma archColumn_ne_zero (W : ℕ) : archColumn W≠0 := by
  intro h
  have hh:=archColumn_vacuum W
  rw [h] at hh
  simp at hh
end CriticalHoneycomb.Transfer.RasterGrid

end

section
namespace CriticalHoneycomb.Transfer.RasterGrid
open Filter Topology PhysicalTiles
open scoped Matrix
lemma physical_vector_limit (W : ℕ) (v : Column (W+1)→ℂ) :
    Tendsto (fun H=>(rowTransfer (W+1)^H).mulVec v) atTop
      (𝓝 ((archProjection W).mulVec v)) := by
  apply tendsto_pi_nhds.mpr
  intro s
  exact tendsto_finsetSum _ (fun n hn=>(physical_rank_one_limit W s n).mul_const (v n))
lemma physical_iterate_eigen {W : ℕ} (v : Column (W+1)→ℂ) (z : ℂ)
    (hv : (rowTransfer (W+1)).mulVec v=z • v) (H : ℕ) :
    (rowTransfer (W+1)^H).mulVec v=(z^H) • v := by
  induction H with
  | zero => simp
  | succ H ih =>
    rw [pow_succ',←Matrix.mulVec_mulVec,ih,Matrix.mulVec_smul,hv,smul_smul,pow_succ]

theorem physical_fixed_line (W : ℕ) (v : Column (W+1)→ℂ)
    (hv : (rowTransfer (W+1)).mulVec v=v) :
    v=(∑ s,archRow W s*v s) • archColumn W := by
  have hi : ∀ H,(rowTransfer (W+1)^H).mulVec v=v := by
    intro H
    simpa using physical_iterate_eigen v 1 (by simpa using hv) H
  have hlim:=physical_vector_limit W v
  simp_rw [hi] at hlim
  have he:=tendsto_nhds_unique tendsto_const_nhds hlim
  exact he.trans (projection_mulVec W v)
lemma projection_eigen_zero {W : ℕ} (v : Column (W+1)→ℂ) (z : ℂ) (hz : z≠1)
    (hv : (rowTransfer (W+1)).mulVec v=z • v) : (archProjection W).mulVec v=0 := by
  have hx : z • ((archProjection W).mulVec v)=(archProjection W).mulVec v := by
    rw [←Matrix.mulVec_smul,←hv,Matrix.mulVec_mulVec,projection_mul_transfer]
  funext s
  have hs:=congrFun hx s
  simp only [Pi.smul_apply,smul_eq_mul] at hs
  have hh : (z-1)*((archProjection W).mulVec v s)=0 := by linear_combination hs
  exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hz)

theorem physical_other_eigenvalue_small {W : ℕ} (v : Column (W+1)→ℂ) (z : ℂ)
    (hv0 : v≠0) (hz : z≠1) (hv : (rowTransfer (W+1)).mulVec v=z • v) : ‖z‖<1 := by
  obtain ⟨s,hs⟩ : ∃ s,v s≠0 := by
    by_contra hn
    push Not at hn
    exact hv0 (funext hn)
  have hl:=(tendsto_pi_nhds.mp (physical_vector_limit W v)) s
  rw [projection_eigen_zero v z hz hv] at hl
  simp only [Pi.zero_apply] at hl
  have he : ∀ H,(rowTransfer (W+1)^H).mulVec v s=z^H*v s := by
    intro H
    simpa only [Pi.smul_apply,smul_eq_mul] using congrFun (physical_iterate_eigen v z hv H) s
  simp_rw [he] at hl
  have hh:=hl.div_const (v s)
  simp only [mul_div_cancel_right₀ _ hs,zero_div] at hh
  exact tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mp hh
end CriticalHoneycomb.Transfer.RasterGrid

end

end OAI
