import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Nuclearity.NuclearFinitePacking

namespace OAI

noncomputable section
namespace DirectPacking
open Pureness CurrentMain DirectComparison Filter
open scoped ComplexOrder

section PairBounds
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [TraceFamily D]
lemma OrthogonalProjectionPair.halving_le (Q : OrthogonalProjectionPair D)
    (τ : RestrictedTracialState D) (x : unitary D) :
    ‖τ.functional (Q.left * (x : D)) - (1 / 2 : ℂ) * τ.functional (x : D)‖ ≤
      (Q.remaining τ + Q.balance τ (x : D)) / 2 := by
  have hid : τ.functional (Q.left * (x : D)) - (1 / 2 : ℂ) * τ.functional (x : D) =
      (1 / 2 : ℂ) * ((τ.functional (Q.left * (x : D)) - τ.functional (Q.right * (x : D))) -
        τ.functional ((1 - Q.total) * (x : D))) := by
    simp only [total, sub_mul, one_mul, add_mul, map_sub, map_add]
    ring
  have hxu : ‖(x : D)‖ ≤ 1 := by
    have h := CStarRing.norm_coe_unitary_mul x (1 : D)
    rw [mul_one] at h
    exact h.le.trans (IsStarProjection.one D).norm_le
  have hr := trace_norm_projection_mul_le τ Q.total_projection.one_sub (x : D)
  have hrem : 0 ≤ Q.remaining τ := Complex.nonneg_iff.mp
    (τ.functional.map_nonneg Q.total_projection.one_sub.nonneg) |>.1
  have hr' : ‖τ.functional ((1 - Q.total) * (x : D))‖ ≤ Q.remaining τ := by
    apply hr.trans
    exact (mul_le_mul_of_nonneg_right hxu hrem).trans_eq (one_mul _)
  rw [hid, norm_mul]
  norm_num only [norm_div, norm_one, Complex.norm_ofNat]
  calc
    _ ≤ (1 / 2 : ℝ) * (Q.balance τ (x : D) + Q.remaining τ) := by
      gcongr
      exact (norm_sub_le _ _).trans (add_le_add le_rfl hr')
    _ = _ := by ring

end PairBounds

theorem finite_set_central_splitting
    {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [TraceFamily D]
    [Nonempty (RestrictedTracialState D)]
    (ι : A →⋆ₐ[ℂ] D) (hA : IsNuclear A)
    (hsupply : SpectralProjectionSupply (fun τ : RestrictedTracialState D => (τ : TracialState D)))
    (hcoef : CoefficientSupply (D := D)) (hinsert : InsertionSupply (D := D))
    (K : Finset (unitary A)) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : D, IsStarProjection P ∧ ∀ u ∈ K,
      familyTwoNorm (fun τ : RestrictedTracialState D => (τ : TracialState D))
        (P*ι (u:A)-ι (u:A)*P) < ε ∧
      familyTraceNorm (fun τ : RestrictedTracialState D => (τ : TracialState D))
        (P*ι (u:A)-(1/2:ℂ) • ι (u:A)) < ε := by
  have hT : Nonempty (TracialState D) := ⟨(Classical.ofNonempty : RestrictedTracialState D).val⟩
  obtain ⟨η,n,hη,hη1,henergy,hbalance⟩ := exists_packing_parameters hε
  obtain ⟨Q,hQ,_⟩ := finite_packing_from_nuclearity hA.small ι hsupply hT hcoef hinsert hη hη1 n K ∅
  refine ⟨Q.left,Q.left_projection,?_⟩
  intro x hx
  constructor
  · apply lt_of_le_of_lt ?_ henergy
    apply ciSup_le
    intro τ
    rw [traceTwoNorm_sub_swap]
    have h := hQ.energy x hx τ
    have hs : traceTwoNorm τ (ι (x:A)*Q.left-Q.left*ι (x:A))^2 ≤ packingEnergy η n :=
      (le_add_of_nonneg_right (sq_nonneg _)).trans h
    exact (Real.le_sqrt (traceTwoNorm_nonneg (τ : TracialState D) (ι (x:A)*Q.left-Q.left*ι (x:A))) (packingEnergy_nonneg hη.le n)).mpr hs
  · apply lt_of_le_of_lt ?_ hbalance
    apply ciSup_le
    intro τ
    simp only [map_sub,map_smul,smul_eq_mul]
    exact (Q.halving_le τ (mapUnitary ι x)).trans
      (div_le_div_of_nonneg_right (add_le_add (hQ.remaining τ) (hQ.balance x hx τ)) (by norm_num))

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] [Nonempty (TracialState A)]
variable (U : Ultrafilter ℕ) (hfree : (U : Filter ℕ) ≤ atTop)
variable (hsimple : TopologicallySimple A) (hinf : ¬FiniteDimensional ℂ A)
variable (hcmp : StrictComparison A) (hnuc : IsNuclear A)
local notation "D" => FamilyUltrapower (fun τ : TracialState A => τ) U
local notation "Λ" => familyLimitTrace (fun τ : TracialState A => τ) U
local notation "ι" => familyUltrapowerMap (fun τ : TracialState A => τ) U

include hfree hsimple hinf hcmp hnuc in

theorem comparison_finite_central_splitting
    (K : Finset (unitary A)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : D, IsStarProjection p ∧ ∀ u ∈ K,
      familyTwoNorm Λ (p*ι (u:A)-ι (u:A)*p) < ε ∧
      familyTraceNorm Λ (p*ι (u:A)-(1/2:ℂ) • ι (u:A)) < ε := by
  let := limitTraceFamily (A := A) U
  let := limitTraceFamily_nonempty (A := A) U
  obtain ⟨hs,hc,hi⟩ := source_tools U hfree hsimple hinf hcmp
  obtain ⟨p,hp,ht⟩ := finite_set_central_splitting ι hnuc hs hc hi K hε
  refine ⟨p,hp,?_⟩
  intro u hu
  have h2 (a : D) : familyTwoNorm Λ a ≤
      familyTwoNorm (fun τ : RestrictedTracialState D => (τ : TracialState D)) a := by
    apply ciSup_le
    intro s
    exact traceTwoNorm_le_family (fun τ : RestrictedTracialState D => (τ : TracialState D))
      ⟨Λ s,⟨s,rfl⟩⟩ a
  have h1 (a : D) : familyTraceNorm Λ a ≤
      familyTraceNorm (fun τ : RestrictedTracialState D => (τ : TracialState D)) a := by
    apply ciSup_le
    intro s
    exact traceNorm_le_family (fun τ : RestrictedTracialState D => (τ : TracialState D))
      ⟨Λ s,⟨s,rfl⟩⟩ a
  exact ⟨(h2 _).trans_lt (ht u hu).1,(h1 _).trans_lt (ht u hu).2⟩

end DirectPacking
end

end OAI
