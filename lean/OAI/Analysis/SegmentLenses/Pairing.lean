import OAI.Analysis.SegmentLenses.FiniteLaws

namespace OAI

/-!
# Finite heads and the completion–dual pairing
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses

section Restrictions
variable {V : Type*} [decidableEqV : DecidableEq V] [PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V]


theorem subinterval_isSegment {S T : Finset V}
    (hS : SegmentSystem.isSegment S) (hTS : T ⊆ S)
    (hc : ∀ a ∈ T, ∀ b ∈ T, ∀ v, a ≤ v → v ≤ b → v ∈ T) :
    T = ∅ ∨ SegmentSystem.isSegment T := by
  have _ := decidableEqV
  have _ := locallyFiniteOrderV
  classical
  rcases T.eq_empty_or_nonempty with he | hn
  · exact Or.inl he
  right
  obtain ⟨a, b, hab, hS⟩ := (IntervalSegments.iff_interval S).mp hS
  obtain ⟨c, hcT, hcmin⟩ := Finset.exists_minimal hn
  obtain ⟨d, hdT, hdmax⟩ := Finset.exists_maximal hn
  have hchain : ∀ v ∈ T, ∀ w ∈ T, v ≤ w ∨ w ≤ v := by
    intro v hv w hw
    exact TreeOrder.lower_chain ((hS v).mp (hTS hv)).2 ((hS w).mp (hTS hw)).2
  have hmin : ∀ v ∈ T, c ≤ v := by
    intro v hv
    exact (hchain c hcT v hv).elim id (hcmin hv)
  have hmax : ∀ v ∈ T, v ≤ d := by
    intro v hv
    exact (hchain v hv d hdT).elim id (hdmax hv)
  apply (IntervalSegments.iff_interval T).mpr
  refine ⟨c, d, hmin d hdT, ?_⟩
  intro v
  exact ⟨fun hv => ⟨hmin v hv, hmax v hv⟩,
    fun hv => hc c hcT d hdT v hv.1 hv.2⟩

theorem norm_filter_le (u : V →₀ ℝ) (P : V → Prop) [DecidablePred P]
    (hP : ∀ a b v, P a → P b → a ≤ v → v ≤ b → P v) :
    segmentSeminorm V (u.filter P) ≤ segmentSeminorm V u := by
  classical
  rw [segmentSeminorm_apply]
  apply ciSup_le
  intro F
  have h := indexed_test_bound u (fun S : F.sets => S.val.filter P)
    (fun S => subinterval_isSegment (F.segment _ S.property) (Finset.filter_subset _ _)
      (by
        intro a ha b hb v hav hvb
        apply Finset.mem_filter.mpr
        obtain ⟨l, r, hlr, hs⟩ := (IntervalSegments.iff_interval S.val).mp
          (F.segment _ S.property)
        exact ⟨(hs v).mpr ⟨le_trans ((hs a).mp (Finset.mem_filter.mp ha).1).1 hav,
          le_trans hvb ((hs b).mp (Finset.mem_filter.mp hb).1).2⟩,
          hP a b v (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 hav hvb⟩))
    (by
      intro S T hne
      exact (F.disjoint S.property T.property (fun he => hne (Subtype.ext he))).mono
        (Finset.filter_subset _ _) (Finset.filter_subset _ _))
  have he : F.seminorm (u.filter P) ^ 2 =
      ∑ S : F.sets, (∑ v ∈ S.val.filter P, u v) ^ 2 := by
    rw [F.seminorm_sq]
    simp only [Finsupp.filter_apply, Finset.sum_filter]
  rw [← he] at h
  nlinarith [apply_nonneg F.seminorm (u.filter P), apply_nonneg (segmentSeminorm V) u]

theorem norm_headTest_le {H : Finset V} (hH : Ancestral (· ≤ ·) H) (u : V →₀ ℝ) :
    segmentSeminorm V (u.filter (· ∈ H)) ≤ segmentSeminorm V u :=
  norm_filter_le u _ (fun _ _ _ _ hb _ hvb => hH hb hvb)

theorem norm_tailTest_le {H : Finset V} (hH : Ancestral (· ≤ ·) H) (u : V →₀ ℝ) :
    segmentSeminorm V (u.filter (· ∉ H)) ≤ segmentSeminorm V u :=
  norm_filter_le u _ (fun _ _ _ ha _ hav _ hv => ha (hH hv hav))

end Restrictions

section Pairing
variable {V : Type*} [SegmentSystem V]

@[simp] theorem coordinate_apply_test (v : V) (u : Test V) :
    coordinate v (u : Primal V) = u.coeff v := by
  exact ContinuousLinearMap.extend_eq _ UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformInducing_coe _) u

@[simp] theorem coordinate_unitVector [DecidableEq V] (v w : V) :
    coordinate v (unitVector w) = if v = w then 1 else 0 := by
  classical
  rw [unitVector, coordinate_apply_test]
  simp [Test.coeff, Test.ofFinsupp, Finsupp.single_apply, eq_comm]


theorem dual_norm_le (x : FullDual V) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ u : Test V, |x (u : Primal V)| ≤ M * ‖u‖) : ‖x‖ ≤ M := by
  apply x.opNorm_le_bound hM
  intro u
  refine UniformSpace.Completion.induction_on u (p := fun u => ‖x u‖ ≤ M * ‖u‖)
    (isClosed_le (x.continuous.norm) (continuous_const.mul continuous_norm)) ?_
  intro u
  simpa only [Real.norm_eq_abs, UniformSpace.Completion.norm_coe] using h u

theorem test_as_sum (u : Test V) :
    (u : Primal V) = ∑ v ∈ u.coeff.support, u.coeff v • unitVector v := by
  classical
  have he : u = ∑ v ∈ u.coeff.support, u.coeff v • Test.ofFinsupp (Finsupp.single v 1) := by
    change u.coeff = ∑ v ∈ u.coeff.support, u.coeff v • Finsupp.single v 1
    simpa only [Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.sum] using
      (Finsupp.sum_single u.coeff).symm
  calc
    (u : Primal V) = ((∑ v ∈ u.coeff.support,
        u.coeff v • Test.ofFinsupp (Finsupp.single v 1) : Test V) : Primal V) :=
      congrArg (fun v : Test V => (v : Primal V)) he
    _ = ∑ v ∈ u.coeff.support, u.coeff v • unitVector v := by
      change (UniformSpace.Completion.toComplL : Test V →L[ℝ] Primal V) (∑ v ∈ u.coeff.support,
        u.coeff v • Test.ofFinsupp (Finsupp.single v 1)) = _
      simp only [map_sum, map_smul]; rfl


theorem dual_apply_test (x : FullDual V) (u : Test V) :
    x (u : Primal V) = ∑ v ∈ u.coeff.support, u.coeff v * x (unitVector v) := by
  rw [test_as_sum]
  simp only [map_sum, map_smul, smul_eq_mul]

@[simp] theorem head_apply_test (H : Finset V) (x : FullDual V) (u : Test V) :
    head H x (u : Primal V) = ∑ v ∈ H, x (unitVector v) * u.coeff v := by
  simp [head, coordinate_apply_test]


def segmentFunctional (S : Finset V) : FullDual V := ∑ v ∈ S, coordinate v

@[simp] theorem segmentFunctional_apply (S : Finset V) (u : Test V) :
    segmentFunctional S (u : Primal V) = ∑ v ∈ S, u.coeff v := by
  simp [segmentFunctional]


structure Representation (V : Type*) [SegmentSystem V] where
  family : SegmentFamily V
  coeff : family.sets → ℝ

def Representation.value (A : Representation V) : FullDual V :=
  ∑ S : A.family.sets, A.coeff S • segmentFunctional S.val

def Representation.energy (A : Representation V) : ℝ := ∑ S, A.coeff S ^ 2

@[simp] theorem Representation.apply_test (A : Representation V) (u : Test V) :
    A.value (u : Primal V) = ∑ S, A.coeff S * ∑ v ∈ S.val, u.coeff v := by
  simp [Representation.value]


theorem Representation.norm_le (A : Representation V) :
    ‖A.value‖ ≤ Real.sqrt A.energy := by
  apply dual_norm_le _ (Real.sqrt_nonneg _)
  intro u
  rw [A.apply_test]
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun S => |A.coeff S|) (fun S => |∑ v ∈ S.val, u.coeff v|)
  simp only [sq_abs, ← A.family.seminorm_sq, Real.sqrt_sq (apply_nonneg _ _)] at h
  calc
    |∑ S, A.coeff S * ∑ v ∈ S.val, u.coeff v| ≤
        ∑ S, |A.coeff S| * |∑ v ∈ S.val, u.coeff v| := by
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
        (fun S => A.coeff S * ∑ v ∈ S.val, u.coeff v) Finset.univ
    _ ≤ Real.sqrt A.energy * A.family.seminorm u.coeff := h
    _ ≤ Real.sqrt A.energy * ‖u‖ :=
      mul_le_mul_of_nonneg_left (le_segmentSeminorm _ _) (Real.sqrt_nonneg _)

end Pairing

section MorePairing
variable {V : Type*} [decidableEqV : DecidableEq V] [SegmentSystem V]

theorem dual_ext_test {x y : FullDual V}
    (h : ∀ u : Test V, x (u : Primal V) = y (u : Primal V)) : x = y := by
  have _ := decidableEqV
  ext u
  exact UniformSpace.Completion.induction_on u
    (isClosed_eq x.continuous y.continuous) h

@[simp] theorem head_unitVector (H : Finset V) (x : FullDual V) (v : V) :
    head H x (unitVector v) = if v ∈ H then x (unitVector v) else 0 := by
  simp [head, coordinate_unitVector, eq_comm]

@[simp] theorem head_head (H : Finset V) (x : FullDual V) : head H (head H x) = head H x := by
  simp only [head, _root_.sum_apply, smul_apply, smul_eq_mul,
    coordinate_unitVector]
  apply Finset.sum_congr rfl
  intro v hv
  simp [hv, eq_comm]


theorem head_pairing (H : Finset V) (x : FullDual V) (u : Test V) :
    head H x (u : Primal V) =
      x ((Test.ofFinsupp (u.coeff.filter (· ∈ H)) : Test V) : Primal V) := by
  rw [head_apply_test, dual_apply_test]
  change (∑ v ∈ H, x (unitVector v) * u.coeff v) =
    ∑ v ∈ (u.coeff.filter (· ∈ H)).support,
      (u.coeff.filter (· ∈ H)) v * x (unitVector v)
  have hsub : (u.coeff.filter (· ∈ H)).support ⊆ H := by
    intro v hv
    exact (Finsupp.mem_support_iff.mp hv |> fun h => by
      by_contra hn
      exact h (by simp [hn]))
  rw [Finset.sum_subset hsub (by
    intro v hv hnv
    have hz := Finsupp.notMem_support_iff.mp hnv
    rw [hz, zero_mul])]
  apply Finset.sum_congr rfl
  intro v hv
  simp [hv, mul_comm]

theorem tail_pairing (H : Finset V) (x : FullDual V) (u : Test V) :
    tail H x (u : Primal V) =
      x ((Test.ofFinsupp (u.coeff.filter (· ∉ H)) : Test V) : Primal V) := by
  have he : u - Test.ofFinsupp (u.coeff.filter (· ∈ H)) =
      Test.ofFinsupp (u.coeff.filter (· ∉ H)) := by
    change u.coeff - u.coeff.filter (· ∈ H) = u.coeff.filter (· ∉ H)
    ext v
    by_cases hv : v ∈ H <;> simp [hv]
  change x (u : Primal V) - head H x (u : Primal V) = _
  rw [head_pairing, ← map_sub, ← UniformSpace.Completion.coe_sub, he]

end MorePairing

section DualRestrictions
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V]

theorem norm_head_le {H : Finset V} (hH : Ancestral (· ≤ ·) H) (x : FullDual V) :
    ‖head H x‖ ≤ ‖x‖ := by
  apply dual_norm_le _ (norm_nonneg _)
  intro u
  rw [head_pairing]
  have h := x.le_opNorm ((Test.ofFinsupp (u.coeff.filter (· ∈ H)) : Test V) : Primal V)
  rw [Real.norm_eq_abs, UniformSpace.Completion.norm_coe] at h
  exact h.trans (mul_le_mul_of_nonneg_left (norm_headTest_le hH _) (norm_nonneg _))

theorem norm_tail_le {H : Finset V} (hH : Ancestral (· ≤ ·) H) (x : FullDual V) :
    ‖tail H x‖ ≤ ‖x‖ := by
  apply dual_norm_le _ (norm_nonneg _)
  intro u
  rw [tail_pairing]
  have h := x.le_opNorm ((Test.ofFinsupp (u.coeff.filter (· ∉ H)) : Test V) : Primal V)
  rw [Real.norm_eq_abs, UniformSpace.Completion.norm_coe] at h
  exact h.trans (mul_le_mul_of_nonneg_left (norm_tailTest_le hH _) (norm_nonneg _))

end DualRestrictions

section IndexedFamilies
variable {V ι : Type*} [DecidableEq V] [SegmentSystem V] [Fintype ι]


def SegmentFamily.ofPieces (S : ι → Finset V)
    (hS : ∀ i, S i = ∅ ∨ SegmentSystem.isSegment (S i))
    (hd : Pairwise fun i j => Disjoint (S i) (S j)) : SegmentFamily V where
  sets := (Finset.univ.image S).erase ∅
  segment := by
    intro T hT
    obtain ⟨hne, him⟩ := Finset.mem_erase.mp hT
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp him
    exact (hS i).resolve_left hne
  disjoint := by
    intro A hA B hB hne
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_erase.mp hA).2
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_erase.mp hB).2
    exact hd (fun hij => hne (congrArg S hij))

theorem SegmentFamily.ofPieces_sq (S : ι → Finset V)
    (hS : ∀ i, S i = ∅ ∨ SegmentSystem.isSegment (S i))
    (hd : Pairwise fun i j => Disjoint (S i) (S j)) (p : V →₀ ℝ) :
    (ofPieces S hS hd).seminorm p ^ 2 = ∑ i, (∑ v ∈ S i, p v) ^ 2 := by
  classical
  rw [seminorm_sq, Finset.sum_coe_sort (ofPieces S hS hd).sets
    (fun T : Finset V => (∑ v ∈ T, p v) ^ 2)]
  change (∑ T ∈ (Finset.univ.image S).erase ∅, (∑ v ∈ T, p v) ^ 2) = _
  rw [Finset.sum_erase _ (by simp)]
  apply Finset.sum_image_of_pairwise_eq_zero
  intro i hi j hj hij heq
  have hempty : S i = ∅ := by
    have hh : Disjoint (S i) (S j) := hd hij
    rw [← heq] at hh
    exact disjoint_self.mp hh
  simp [hempty]

end IndexedFamilies

section ClipFamilies
variable {V : Type*} [DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [treeOrderV : TreeOrder V]
  [SegmentSystem V] [intervalSegmentsV : IntervalSegments V]

theorem clip_segment {H : Finset V} (hH : Ancestral (· ≤ ·) H)
    (F : SegmentFamily V) (S : F.sets) :
    S.val ∩ H = ∅ ∨ SegmentSystem.isSegment (S.val ∩ H) := by
  apply subinterval_isSegment (F.segment _ S.property) Finset.inter_subset_left
  intro a ha b hb v hav hvb
  rw [F.repr S] at ha hb ⊢
  exact Finset.mem_inter.mpr ⟨Finset.mem_Icc.mpr
    ⟨le_trans (Finset.mem_Icc.mp (Finset.mem_inter.mp ha).1).1 hav,
      le_trans hvb (Finset.mem_Icc.mp (Finset.mem_inter.mp hb).1).2⟩,
    hH (Finset.mem_inter.mp hb).2 hvb⟩

theorem clip_disjoint (H : Finset V) (F : SegmentFamily V) :
    Pairwise fun S T : F.sets => Disjoint (S.val ∩ H) (T.val ∩ H) := by
  have _ := partialOrderV
  have _ := locallyFiniteOrderV
  have _ := treeOrderV
  have _ := intervalSegmentsV
  intro S T hne
  exact (F.disjoint S.property T.property (fun he => hne (Subtype.ext he))).mono
    Finset.inter_subset_left Finset.inter_subset_left

def SegmentFamily.clip {H : Finset V} (hH : Ancestral (· ≤ ·) H)
    (F : SegmentFamily V) : SegmentFamily V :=
  ofPieces (fun S : F.sets => S.val ∩ H) (clip_segment hH F) (clip_disjoint H F)

theorem SegmentFamily.clip_subset {H : Finset V} (hH : Ancestral (· ≤ ·) H)
    (F : SegmentFamily V) : ∀ S ∈ (F.clip hH).sets, S ⊆ H := by
  intro S hS
  obtain ⟨T, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_erase.mp hS).2
  exact Finset.inter_subset_right

theorem SegmentFamily.clip_seminorm {H : Finset V} (hH : Ancestral (· ≤ ·) H)
    (F : SegmentFamily V) (p : V →₀ ℝ) (hp : p.support ⊆ H) :
    (F.clip hH).seminorm p = F.seminorm p := by
  have he : (F.clip hH).seminorm p ^ 2 = F.seminorm p ^ 2 := by
    rw [clip, ofPieces_sq, F.seminorm_sq]
    apply Finset.sum_congr rfl
    intro S hS
    congr 1
    apply Finset.sum_subset Finset.inter_subset_left
    intro v hv hnv
    apply Finsupp.notMem_support_iff.mp
    intro hvs
    exact hnv (Finset.mem_inter.mpr ⟨hv, hp hvs⟩)
  nlinarith [apply_nonneg (F.clip hH).seminorm p, apply_nonneg F.seminorm p]

end ClipFamilies


end SegmentLenses

end

end OAI
