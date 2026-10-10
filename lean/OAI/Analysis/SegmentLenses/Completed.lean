import OAI.Analysis.SegmentLenses.TailBudget

namespace OAI

/-!
# Completed midpoint bounds and coordinate density
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses



instance infiniteLocallyFiniteBot : LocallyFiniteOrderBot InfiniteVertex := by
  classical
  exact LocallyFiniteOrderBot.ofIic InfiniteVertex (fun b => b.inits.toFinset)
    (fun a x => by simp [List.mem_inits, LE.le])

instance forestLocallyFiniteBot : LocallyFiniteOrderBot ForestVertex := by
  classical
  have hf : ∀ b : ForestVertex, {v : ForestVertex | v ≤ b}.Finite := by
    intro b
    apply Set.Finite.of_injOn (f := fun v : ForestVertex => v.val.2)
      (t := {w : List ℕ | w.IsPrefix b.val.2})
    · intro v hv
      exact hv.2
    · intro v hv w hw he
      apply Subtype.ext
      exact Prod.ext (hv.1.trans hw.1.symm) he
    · exact b.val.2.inits.finite_toSet.subset (by
        intro w hw
        exact (List.mem_inits w b.val.2).mpr hw)
  exact LocallyFiniteOrderBot.ofIic ForestVertex (fun b => (hf b).toFinset)
    (fun a x => by simp)

section FiniteAncestry
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrderBot V]

def ancestralHull (S : Finset V) : Finset V := S.biUnion Finset.Iic

theorem subset_ancestralHull (S : Finset V) : S ⊆ ancestralHull S := by
  intro v hv
  exact Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_Iic.mpr le_rfl⟩

theorem ancestralHull_ancestral (S : Finset V) : Ancestral (· ≤ ·) (ancestralHull S) := by
  intro v w hv hwv
  obtain ⟨b, hb, hvb⟩ := Finset.mem_biUnion.mp hv
  exact Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_Iic.mpr (hwv.trans (Finset.mem_Iic.mp hvb))⟩

end FiniteAncestry

section LocalizingTests
variable {V : Type*} [DecidableEq V] [SegmentSystem V]

theorem head_pairing_of_support (K : Finset V) (y : FullDual V) (u : Test V)
    (hu : u.coeff.support ⊆ K) : head K y (u : Primal V) = y (u : Primal V) := by
  rw [head_pairing]
  have he : u.coeff.filter (· ∈ K) = u.coeff := by
    ext v
    by_cases hv : v ∈ K
    · simp [hv]
    · have hz : u.coeff v = 0 := Finsupp.notMem_support_iff.mp (fun h => hv (hu h))
      simp [hv, hz]
  rw [he]
  rfl

theorem tail_head_pairing (H K : Finset V) (y : FullDual V) (u : Test V)
    (hu : u.coeff.support ⊆ K) : tail H (head K y) (u : Primal V) = tail H y (u : Primal V) := by
  rw [tail_pairing, tail_pairing]
  apply head_pairing_of_support
  change (u.coeff.filter (· ∉ H)).support ⊆ K
  rw [Finsupp.support_filter]
  exact (Finset.filter_subset _ _).trans hu

end LocalizingTests

section CompletedMain
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V]
  [LocallyFiniteOrderBot V] [TreeOrder V] [SegmentSystem V] [IntervalSegments V]



theorem completed_main_tail {H : Finset V} (hH : Ancestral (· ≤ ·) H)
    (x y : FullDual V) (hx : head H x = x)
    (R : ℝ) (hR : 0 ≤ R) (hp : ‖x + y‖ ≤ R) (hm : ‖x - y‖ ≤ R) :
    ‖tail H y‖ ≤ 2 * Real.sqrt (R ^ 2 - ‖x‖ ^ 2) := by
  apply dual_norm_le _ (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
  intro u
  let K := ancestralHull (H ∪ u.coeff.support)
  have hK : Ancestral (· ≤ ·) K := ancestralHull_ancestral _
  have hHK : H ⊆ K := Finset.subset_union_left.trans (subset_ancestralHull _)
  have huK : u.coeff.support ⊆ K := Finset.subset_union_right.trans (subset_ancestralHull _)
  have hxK := head_eq_of_subset hHK x hx
  have hpK : ‖x + head K y‖ ≤ R := by
    have he : x + head K y = head K (x + y) := by
      change x + headLinear K y = headLinear K (x + y)
      simp only [map_add, headLinear_apply, hxK]
    rw [he]
    exact (norm_head_le hK (x + y)).trans hp
  have hmK : ‖x - head K y‖ ≤ R := by
    have he : x - head K y = head K (x - y) := by
      change x - headLinear K y = headLinear K (x - y)
      simp only [map_sub, headLinear_apply, hxK]
    rw [he]
    exact (norm_head_le hK (x - y)).trans hm
  have hb := finite_main_tail hH hK hHK x (head K y) hx (head_head K y) R hR hpK hmK
  rw [← tail_head_pairing H K y u huK]
  have hop := (tail H (head K y)).le_opNorm (u : Primal V)
  rw [Real.norm_eq_abs, UniformSpace.Completion.norm_coe] at hop
  exact hop.trans (mul_le_mul_of_nonneg_right hb (norm_nonneg u))

end CompletedMain


theorem forest_main_tail (H : Finset ForestVertex) (hH : Ancestral ForestAncestor H)
    (x y : X) (hx : x = head H x) (R : ℝ) (hR : 0 ≤ R)
    (hp : ‖x + y‖ ≤ R) (hm : ‖x - y‖ ≤ R) :
    ‖tail H y‖ ≤ 2 * Real.sqrt (R ^ 2 - ‖x‖ ^ 2) :=
  by
    classical
    exact completed_main_tail hH x y hx.symm R hR hp hm



theorem infinite_main_tail (H : Finset InfiniteVertex) (hH : Ancestral List.IsPrefix H)
    (x y : BInfinite) (hx : x.val = head H x.val) (R : ℝ) (hR : 0 ≤ R)
    (hp : ‖x + y‖ ≤ R) (hm : ‖x - y‖ ≤ R) :
    ‖tail H y.val‖ ≤ 2 * Real.sqrt (R ^ 2 - ‖x‖ ^ 2) :=
  by
    classical
    exact completed_main_tail hH x.val y.val hx.symm R hR hp hm

section CoordinateNorms
variable {V : Type*} [decidableEqV : DecidableEq V] [SegmentSystem V]

theorem norm_test_unit (v : V) : ‖(Test.ofFinsupp (Finsupp.single v 1) : Test V)‖ = 1 := by
  have _ := decidableEqV
  apply le_antisymm
  · change segmentSeminorm V (Finsupp.single v 1) ≤ 1
    rw [segmentSeminorm_apply]
    apply ciSup_le
    intro F
    change ‖F.test (Finsupp.single v 1)‖ ≤ 1
    simpa [SegmentFamily.test, Finsupp.linearCombination_single] using F.norm_column_le v
  · change 1 ≤ segmentSeminorm V (Finsupp.single v 1)
    have h := abs_coord_le (Finsupp.single v (1 : ℝ)) v
    simpa using h

@[simp] theorem norm_unitVector (v : V) : ‖unitVector v‖ = 1 := by
  rw [unitVector, UniformSpace.Completion.norm_coe, norm_test_unit]

@[simp] theorem norm_coordinate (v : V) : ‖coordinate v‖ = 1 := by
  apply le_antisymm
  · apply dual_norm_le _ (by norm_num)
    intro u
    rw [coordinate_apply_test, one_mul]
    exact abs_coord_le u.coeff v
  · have h := (coordinate v).le_opNorm (unitVector v)
    simpa [coordinate_unitVector] using h

theorem coordinate_mem_span (v : V) :
    coordinate v ∈ Submodule.span ℝ (Set.range (coordinate (V := V))) := by
  have _ := decidableEqV
  exact
    Submodule.subset_span ⟨v, rfl⟩

theorem coordinate_mem (v : V) : coordinate v ∈ coordinateSpan V :=
  (Submodule.le_topologicalClosure _) (coordinate_mem_span v)

theorem head_mem_span (H : Finset V) (x : FullDual V) :
    head H x ∈ Submodule.span ℝ (Set.range (coordinate (V := V))) := by
  apply Submodule.sum_mem
  intro v hv
  exact Submodule.smul_mem _ _ (coordinate_mem_span v)

theorem head_mem (H : Finset V) (x : FullDual V) : head H x ∈ coordinateSpan V :=
  (Submodule.le_topologicalClosure _) (head_mem_span H x)


def predualCoordinate (v : V) : CoordinatePredual V := ⟨coordinate v, coordinate_mem v⟩

@[simp] theorem norm_predualCoordinate (v : V) : ‖predualCoordinate v‖ = 1 := norm_coordinate v


theorem span_finitely_supported (z : FullDual V)
    (hz : z ∈ Submodule.span ℝ (Set.range (coordinate (V := V)))) :
    ∃ H : Finset V, head H z = z := by
  classical
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨v, rfl⟩ := hz
      refine ⟨{v}, (head_eq_iff _ _).mpr ?_⟩
      intro w hw
      have hn : v ≠ w := by simpa only [Finset.mem_singleton, eq_comm] using hw
      simp [coordinate_unitVector, hn]
  | zero => exact ⟨∅, by simp [head]⟩
  | add z w hz hw hz' hw' =>
      obtain ⟨H, hH⟩ := hz'
      obtain ⟨K, hK⟩ := hw'
      refine ⟨H ∪ K, (head_eq_iff _ _).mpr ?_⟩
      intro v hv
      rw [_root_.add_apply, (head_eq_iff _ _).mp hH v (fun h => hv (Finset.mem_union_left _ h)),
        (head_eq_iff _ _).mp hK v (fun h => hv (Finset.mem_union_right _ h)), add_zero]
  | smul a z hz hz' =>
      obtain ⟨H, hH⟩ := hz'
      refine ⟨H, (head_eq_iff _ _).mpr ?_⟩
      intro v hv
      simp only [_root_.smul_apply, smul_eq_mul, (head_eq_iff _ _).mp hH v hv, mul_zero]

end CoordinateNorms

section CoordinateDensity
variable {V : Type*} [DecidableEq V] [PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V]
  [locallyFiniteOrderBotV : LocallyFiniteOrderBot V] [treeOrderV : TreeOrder V] [SegmentSystem V] [intervalSegmentsV : IntervalSegments V]



theorem predual_finite_approx (x : CoordinatePredual V) {ε : ℝ} (hε : 0 < ε) :
    ∃ H : Finset V, Ancestral (· ≤ ·) H ∧ ∃ z : FullDual V, head H z = z ∧ ‖x.val - z‖ < ε := by
  have _ := locallyFiniteOrderV
  have _ := treeOrderV
  have _ := intervalSegmentsV
  have hx : x.val ∈ closure ((Submodule.span ℝ (Set.range (coordinate (V := V)))) : Set (FullDual V)) := x.property
  obtain ⟨z, hz, hdist⟩ := Metric.mem_closure_iff.mp hx ε hε
  obtain ⟨H, hH⟩ := span_finitely_supported z hz
  exact ⟨ancestralHull H, ancestralHull_ancestral H, z,
    head_eq_of_subset (subset_ancestralHull H) z hH, by simpa only [dist_eq_norm] using hdist⟩



theorem predual_small_tail (x : CoordinatePredual V) (H : Finset V) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : Finset V, Ancestral (· ≤ ·) K ∧ H ⊆ K ∧ ‖tail K x.val‖ < ε := by
  obtain ⟨L, hL, z, hz, he⟩ := predual_finite_approx x hε
  let K := ancestralHull (H ∪ L)
  have hK : Ancestral (· ≤ ·) K := ancestralHull_ancestral _
  have hHK : H ⊆ K := Finset.subset_union_left.trans (subset_ancestralHull _)
  have hLK : L ⊆ K := Finset.subset_union_right.trans (subset_ancestralHull _)
  have hzK := head_eq_of_subset hLK z hz
  have heq : tail K x.val = tail K (x.val - z) := by
    change tailLinear K x.val = tailLinear K (x.val - z)
    simp only [map_sub, tailLinear_apply]
    rw [show tail K z = 0 by simp [tail, hzK], sub_zero]
  exact ⟨K, hK, hHK, by rw [heq]; exact (norm_tail_le hK _).trans_lt he⟩


def predualHead {H : Finset V} (hH : Ancestral (· ≤ ·) H) :
    CoordinatePredual V →L[ℝ] CoordinatePredual V := by
  let f : CoordinatePredual V →ₗ[ℝ] CoordinatePredual V :=
    LinearMap.codRestrict (coordinateSpan V)
      ((headLinear H).comp (coordinateSpan V).subtype)
      (fun x : CoordinatePredual V => head_mem H x.val)
  exact LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ) (E := CoordinatePredual V)
    (F := CoordinatePredual V) f 1 (fun x => by
    change ‖head H x.val‖ ≤ 1 * ‖x.val‖
    simpa only [one_mul] using norm_head_le hH x.val)

def predualTail {H : Finset V} (hH : Ancestral (· ≤ ·) H) :
    CoordinatePredual V →L[ℝ] CoordinatePredual V := by
  let f : CoordinatePredual V →ₗ[ℝ] CoordinatePredual V :=
    LinearMap.codRestrict (coordinateSpan V)
      ((tailLinear H).comp (coordinateSpan V).subtype)
      (fun x : CoordinatePredual V => (coordinateSpan V).sub_mem x.property (head_mem H x.val))
  exact LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ) (E := CoordinatePredual V)
    (F := CoordinatePredual V) f 1 (fun x => by
    change ‖tail H x.val‖ ≤ 1 * ‖x.val‖
    simpa only [one_mul] using norm_tail_le hH x.val)

@[simp] theorem predualHead_coe {H : Finset V} (hH : Ancestral (· ≤ ·) H) (x : CoordinatePredual V) :
    (predualHead hH x).val = head H x.val := by
  have _ := locallyFiniteOrderBotV
  exact rfl

@[simp] theorem predualTail_coe {H : Finset V} (hH : Ancestral (· ≤ ·) H) (x : CoordinatePredual V) :
    (predualTail hH x).val = tail H x.val := by
  have _ := locallyFiniteOrderBotV
  exact rfl

theorem norm_predualHead_le {H : Finset V} (hH : Ancestral (· ≤ ·) H) (x : CoordinatePredual V) :
    ‖predualHead hH x‖ ≤ ‖x‖ := by
  have _ := locallyFiniteOrderBotV
  exact norm_head_le hH x.val

theorem norm_predualTail_le {H : Finset V} (hH : Ancestral (· ≤ ·) H) (x : CoordinatePredual V) :
    ‖predualTail hH x‖ ≤ ‖x‖ := by
  have _ := locallyFiniteOrderBotV
  exact norm_tail_le hH x.val

end CoordinateDensity


end SegmentLenses

end

end OAI
