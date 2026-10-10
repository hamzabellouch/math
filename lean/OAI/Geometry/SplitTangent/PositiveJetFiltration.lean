import Mathlib
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.PositiveTangentCurves
import OAI.Geometry.SplitTangent.FormalBoxes
import OAI.Geometry.SplitTangent.SymmetricConormalBound
import OAI.Geometry.SplitTangent.TensorSectionSpace

namespace OAI

/-! Positive Jet Filtration. -/

noncomputable section
open Set Filter Topology Bundle
open scoped Manifold ContDiff
universe u
namespace SplitTangent.PositiveJetFiltration
variable {X : ComplexManifold.{u}} {g : RationalCurve X} {S : TangentSplitting X}
  {V : Type*} [AddCommGroup V] [Module ℂ V] {d : ℕ}
  (F : ℕ → Submodule ℂ V) (hF : Antitone F)
  (L : ∀m,F m →ₗ[ℂ] symmetricSupportedTensors g S (d : ℤ) m)
  (hker : ∀m s,L m s=0 ↔ s.val∈F (m+1))

include hF hker L

 

def kernelEquiv (m : ℕ) : LinearMap.ker (L m) ≃ₗ[ℂ] F (m+1) where
  toFun s := ⟨s.val.val,(hker m s.val).mp s.property⟩
  invFun s := ⟨⟨s.val,hF (Nat.le_succ m) s.property⟩,
    (hker m _).mpr s.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem high_eq_zero (hg : PointedGenerated g S.first)
    (hsep : ∀v,(∀m,v∈F m) → v=0) {k : ℕ} (hk : d < k) (s : F k) : s=0 := by
  have hs (n : ℕ) : s.val∈F n := by
    induction n with
    | zero => exact hF (Nat.zero_le k) s.property
    | succ n ih =>
      by_cases hn : n+1≤k
      · exact hF hn s.property
      · exact (hker n ⟨s.val,ih⟩).mp
          (symmetricSupportedTensors.eq_zero_of_degree_lt_order hg (by omega) _)
  exact Subtype.ext (hsep s.val hs)

 

theorem finite_and_bound (hg : PointedGenerated g S.first)
    (hsep : ∀v,(∀m,v∈F m) → v=0) (N k : ℕ) (hk : d < k+N) :
    Module.Finite ℂ (F k) ∧ Module.finrank ℂ (F k) ≤
      ∑j∈Finset.range N,
        (Module.finrank ℂ (S.first (g.finite 1))+(k+j)-1).choose (k+j)*(d+1) := by
  induction N generalizing k with
  | zero =>
    have : Subsingleton (F k) := ⟨fun s t =>
      (high_eq_zero F hF L hker hg hsep (by simpa using hk) s).trans
        (high_eq_zero F hF L hker hg hsep (by simpa using hk) t).symm⟩
    exact ⟨inferInstance,by simp [Module.finrank_zero_of_subsingleton]⟩
  | succ N ih =>
    obtain ⟨hf,hb⟩ := ih (k+1) (by omega)
    let : Module.Finite ℂ (F (k+1)) := hf
    let : AddCommGroup (symmetricSupportedTensors g S (d : ℤ) k) :=
      Module.addCommMonoidToAddCommGroup ℂ
    obtain ⟨ht,htb⟩ := symmetricSupportedTensors.finite_and_finrank_le hg d k
    let : Module.Finite ℂ (symmetricSupportedTensors g S (d : ℤ) k) := ht
    let : Module.Finite ℂ (LinearMap.ker (L k)) :=
      Module.Finite.equiv (kernelEquiv F hF L hker k).symm
    let : Module.Finite ℂ (F k) := DiagonalRationality.finite_of_kernel (L k)
    refine ⟨inferInstance,?_⟩
    have hrank := LinearMap.finrank_range_add_finrank_ker (K := ℂ) (L k)
    have hrange := (LinearMap.range (L k)).finrank_le
    have hkernel := (kernelEquiv F hF L hker k).finrank_eq
    rw [Finset.sum_range_succ']
    have hshift : (∑j∈Finset.range N,
        (Module.finrank ℂ (S.first (g.finite 1))+(k+(j+1))-1).choose (k+(j+1))*(d+1)) =
        ∑j∈Finset.range N,
        (Module.finrank ℂ (S.first (g.finite 1))+(k+1+j)-1).choose (k+1+j)*(d+1) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    rw [hshift]
    simp only [Nat.add_zero]
    omega

 

theorem polynomial_bound (hg : PointedGenerated g S.first)
    (hsep : ∀v,(∀m,v∈F m) → v=0) :
    Module.Finite ℂ (F 0) ∧ Module.finrank ℂ (F 0) ≤
      (d+Module.finrank ℂ (S.first (g.finite 1))).choose
        (Module.finrank ℂ (S.first (g.finite 1)))*(d+1) := by
  obtain ⟨hf,hb⟩ := finite_and_bound F hF L hker hg hsep (d+1) 0 (by omega)
  refine ⟨hf,?_⟩
  simpa only [Nat.zero_add,←Nat.multichoose_eq,←Finset.sum_mul,Nat.sum_range_multichoose]
    using hb

end SplitTangent.PositiveJetFiltration

end

end OAI
