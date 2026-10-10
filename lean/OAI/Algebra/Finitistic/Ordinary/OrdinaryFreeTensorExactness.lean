import OAI.Algebra.Finitistic.Ordinary.OrdinaryFreeTensor
import Mathlib.LinearAlgebra.Finsupp.Defs

namespace OAI
noncomputable section
namespace LittleFinitistic.BalancedTensor.Free
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable (I : Type u)
variable {N N' N'' : Type u}
variable [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
variable [AddCommGroup N'] [Module k N'] [Module A N'] [IsScalarTower k A N']
variable [AddCommGroup N''] [Module k N''] [Module A N''] [IsScalarTower k A N'']

theorem evaluation_naturality (f : N →ₗ[A] N') (z : Tensor k A (I →₀ Aᵐᵒᵖ) N) :
    evaluation (k := k) I N' (mapRightTo f z) =
      Finsupp.mapRange.linearMap (f.restrictScalars k) (evaluation (k := k) I N z) := by
  induction z using BalancedTensor.induction_on with
  | hz => simp only [map_zero]
  | ht m n =>
    induction m using Finsupp.induction_linear with
    | zero => simp only [map_zero,LinearMap.zero_apply]
    | add x y hx hy => simp only [map_add,LinearMap.add_apply,hx,hy]
    | single i x =>
      simp only [mapRightTo_mk,evaluation_single]
      change Finsupp.single i (MulOpposite.unop x • f n) =
        Finsupp.mapRange f f.map_zero (Finsupp.single i (MulOpposite.unop x • n))
      rw [Finsupp.mapRange_single, f.map_smul]
  | ha x y hx hy => simp only [map_add,hx,hy]

/-- Direct sums preserve exactness, with a preimage supported on the given finite support. -/
theorem finsupp_exact (f : N →ₗ[A] N') (g : N' →ₗ[A] N'') (h : Function.Exact f g) :
    Function.Exact (Finsupp.mapRange.linearMap (f.restrictScalars k) : (I →₀ N) →ₗ[k] (I →₀ N'))
      (Finsupp.mapRange.linearMap (g.restrictScalars k)) := by
  classical
  intro z
  constructor
  · intro hz
    have hg (i : I) : g (z i) = 0 := congrArg (fun x : I →₀ N'' => x i) hz
    let y : I →₀ N := Finsupp.onFinset z.support
      (fun i => if hi : z i = 0 then 0 else Classical.choose ((h (z i)).mp (hg i))) (by
        intro i hi
        by_contra hn
        have hz0 : z i = 0 := by simpa only [Finsupp.mem_support_iff,not_not] using hn
        exact hi (by simp [hz0]))
    refine ⟨y, ?_⟩
    ext i
    change f (if hi : z i = 0 then 0 else Classical.choose ((h (z i)).mp (hg i))) = z i
    split_ifs with hi
    · rw [map_zero,hi]
    · exact Classical.choose_spec ((h (z i)).mp (hg i))
  · rintro ⟨y,rfl⟩
    ext i
    exact (h (f (y i))).mpr ⟨y i,rfl⟩

/-- Tensor by an arbitrary free right module preserves every exact module sequence. -/
theorem tensor_exact (f : N →ₗ[A] N') (g : N' →ₗ[A] N'') (h : Function.Exact f g) :
    Function.Exact (mapRightTo (k := k) (M := I →₀ Aᵐᵒᵖ) f)
      (mapRightTo (k := k) (M := I →₀ Aᵐᵒᵖ) g) := by
  intro z
  constructor
  · intro hz
    have hz' : Finsupp.mapRange.linearMap (g.restrictScalars k) (evaluation (k := k) I N' z) = 0 := by
      rw [← evaluation_naturality,hz,map_zero]
    obtain ⟨y,hy⟩ := (finsupp_exact (k := k) I f g h _).mp hz'
    refine ⟨(equivalence (k := k) (A := A) I N).symm y, ?_⟩
    apply (equivalence (k := k) (A := A) I N').injective
    change evaluation (k := k) I N' (mapRightTo f ((equivalence (k := k) (A := A) I N).symm y)) = _
    rw [evaluation_naturality]
    change Finsupp.mapRange.linearMap (f.restrictScalars k)
      ((equivalence (k := k) (A := A) I N) ((equivalence (k := k) (A := A) I N).symm y)) = _
    rw [LinearEquiv.apply_symm_apply]
    exact hy
  · rintro ⟨y,rfl⟩
    induction y using BalancedTensor.induction_on with
    | hz => simp only [map_zero]
    | ht m n => rw [mapRightTo_mk,mapRightTo_mk,(h (f n)).mpr ⟨n,rfl⟩,map_zero]
    | ha x y hx hy => simp only [map_add,hx,hy,add_zero]
end LittleFinitistic.BalancedTensor.Free

end

end OAI
