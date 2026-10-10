import OAI.GroupTheory.PolycyclicRecognition.Analysis.MeanSubgroup
import OAI.GroupTheory.PolycyclicRecognition.Analysis.FolnerInvariantMean
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Index

namespace OAI

/-! # Invariant means on extensions

Average first on each kernel coset and then on the quotient. All averages
act on the actual bounded real functions used in the height correction.
-/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability
open scoped ENNReal

def boundedFunctionPull {X Y : Type*} (u : X → Y) : BoundedReal Y →ₗ[ℝ] BoundedReal X where
  toFun f := ⟨fun x => f (u x), memℓp_infty ⟨‖f‖, by
    rintro y ⟨x, rfl⟩
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero f (u x)⟩⟩
  map_add' _ _ := by apply lp.ext; funext x; rfl
  map_smul' _ _ := by apply lp.ext; funext x; rfl

@[simp]
theorem boundedFunctionPull_apply {X Y : Type*} (u : X → Y) (f : BoundedReal Y) (x : X) :
    boundedFunctionPull u f x = f (u x) := rfl

@[simp]
theorem boundedFunctionPull_one {X Y : Type*} (u : X → Y) :
    boundedFunctionPull u 1 = 1 := by apply lp.ext; funext x; rfl

theorem boundedFunctionPull_norm_le {X Y : Type*} (u : X → Y) (f : BoundedReal Y) :
    ‖boundedFunctionPull u f‖ ≤ ‖f‖ :=
  lp.norm_le_of_forall_le (norm_nonneg f)
    (fun x => lp.norm_apply_le_norm ENNReal.top_ne_zero f (u x))

variable {G Q : Type*} [Group G] [Group Q]

/-- An invariant mean descends along a surjective group homomorphism. -/
def imageInvariantMean (φ : G →* Q) (hφ : Function.Surjective φ)
    (M : InvariantMean G) : InvariantMean Q where
  toLinearMap := M.toLinearMap.comp (boundedFunctionPull φ)
  positive f hf := M.positive _ (fun g => hf (φ g))
  normalized := by
    change M (boundedFunctionPull φ 1) = 1
    rw [boundedFunctionPull_one]
    exact M.normalized
  left_invariant q f := by
    obtain ⟨g, rfl⟩ := hφ q
    change M (boundedFunctionPull φ (leftPull (φ g) f)) = M (boundedFunctionPull φ f)
    have he : boundedFunctionPull φ (leftPull (φ g) f) =
        leftPull g (boundedFunctionPull φ f) := by
      apply lp.ext
      funext x
      exact congrArg f (φ.map_mul g x).symm
    rw [he, M.left_invariant]

def kernelSlice (φ : G →* Q) (s : Q → G) (q : Q) :
    BoundedReal G →ₗ[ℝ] BoundedReal φ.ker :=
  boundedFunctionPull (fun n : φ.ker => s q * n)

def kernelAverage (φ : G →* Q) (s : Q → G) (M : InvariantMean φ.ker) :
    BoundedReal G →ₗ[ℝ] BoundedReal Q where
  toFun f := ⟨fun q => M (kernelSlice φ s q f), memℓp_infty ⟨‖f‖, by
    rintro y ⟨q, rfl⟩
    have hb : ‖M (kernelSlice φ s q f)‖ ≤ ‖kernelSlice φ s q f‖ := by
      simpa only [Real.norm_eq_abs] using M.abs_apply_le_norm (kernelSlice φ s q f)
    exact hb.trans (boundedFunctionPull_norm_le _ _)⟩⟩
  map_add' f h := by
    apply lp.ext
    funext q
    exact (congrArg M ((kernelSlice φ s q).map_add f h)).trans (M.map_add _ _)
  map_smul' r f := by
    apply lp.ext
    funext q
    exact (congrArg M ((kernelSlice φ s q).map_smul r f)).trans (M.map_smul _ _)

@[simp]
theorem kernelAverage_one (φ : G →* Q) (s : Q → G) (M : InvariantMean φ.ker) :
    kernelAverage φ s M 1 = 1 := by
  apply lp.ext
  funext q
  change M (boundedFunctionPull _ 1) = 1
  rw [boundedFunctionPull_one]
  exact M.normalized

/-- Changing a representative inserts a kernel translation, which disappears
under the inner mean. -/
theorem kernelAverage_leftPull (φ : G →* Q) (s : Q → G) (hs : ∀ q, φ (s q) = q)
    (M : InvariantMean φ.ker) (g : G) (f : BoundedReal G) :
    kernelAverage φ s M (leftPull g f) = leftPull (φ g) (kernelAverage φ s M f) := by
  apply lp.ext
  funext q
  let c : φ.ker := ⟨(s (φ g * q))⁻¹ * g * s q, by
    change φ ((s (φ g * q))⁻¹ * g * s q) = 1
    simp only [map_mul, map_inv, hs]
    group⟩
  have he : kernelSlice φ s q (leftPull g f) =
      leftPull c (kernelSlice φ s (φ g * q) f) := by
    apply lp.ext
    funext n
    change f (g * (s q * n)) = f (s (φ g * q) * ((c : G) * n))
    dsimp only [c]
    group
  change M (kernelSlice φ s q (leftPull g f)) = M (kernelSlice φ s (φ g * q) f)
  rw [he, M.left_invariant]

def extensionInvariantMean (φ : G →* Q) (s : Q → G) (hs : ∀ q, φ (s q) = q)
    (MN : InvariantMean φ.ker) (MQ : InvariantMean Q) : InvariantMean G where
  toLinearMap := MQ.toLinearMap.comp (kernelAverage φ s MN)
  positive f hf := MQ.positive _ (fun q => MN.positive _ (fun n => hf (s q * n)))
  normalized := by
    change MQ (kernelAverage φ s MN 1) = 1
    rw [kernelAverage_one]
    exact MQ.normalized
  left_invariant g f := by
    change MQ (kernelAverage φ s MN (leftPull g f)) = MQ (kernelAverage φ s MN f)
    rw [kernelAverage_leftPull φ s hs, MQ.left_invariant]

theorem invariantMean_of_extension (φ : G →* Q) (hφ : Function.Surjective φ)
    (hN : Nonempty (InvariantMean φ.ker)) (hQ : Nonempty (InvariantMean Q)) :
    Nonempty (InvariantMean G) := by
  choose s hs using hφ
  exact ⟨extensionInvariantMean φ s hs hN.some hQ.some⟩

/-- The normalized counting mean on a finite group. -/
def finiteInvariantMean [Finite G] : InvariantMean G := by
  classical
  letI := Fintype.ofFinite G
  refine ⟨finiteMeanState Finset.univ, finiteMeanState_positive _,
    finiteMeanState_one _ Finset.univ_nonempty, ?_⟩
  intro g f
  change realAvg Finset.univ (fun x => f (g * x)) = realAvg Finset.univ f
  unfold realAvg
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun _ => rfl)

theorem invariantMean_of_normal_subgroup (N : Subgroup G) [N.Normal]
    (hN : Nonempty (InvariantMean N)) (hQ : Nonempty (InvariantMean (G ⧸ N))) :
    Nonempty (InvariantMean G) := by
  apply invariantMean_of_extension (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
    _ hQ
  rw [QuotientGroup.ker_mk']
  exact hN

/-- No normality assumption is needed for a finite extension: restrict to
the normal core, then average over its finite quotient. -/
theorem invariantMean_of_finiteIndex (K : Subgroup G) [K.FiniteIndex]
    (hK : Nonempty (InvariantMean K)) : Nonempty (InvariantMean G) := by
  let N := K.normalCore
  let i : N →* K := Subgroup.inclusion K.normalCore_le
  let MN := subgroupInvariantMean hK.some i.range
  let e : N ≃* i.range := MonoidHom.ofInjective (Subgroup.inclusion_injective _)
  have hN : Nonempty (InvariantMean N) :=
    ⟨imageInvariantMean e.symm.toMonoidHom e.symm.surjective MN⟩
  exact invariantMean_of_normal_subgroup N hN ⟨finiteInvariantMean⟩

end PolycyclicRecognition

end

end OAI
