import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorFunctor
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Exact.Basic

namespace OAI

noncomputable section

namespace ArExplicit.BalancedTensor

variable {k R F : Type*} [CommRing k] [Ring R] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F]
variable [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F]
variable {M N L : Type*}
variable [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M] [SMulCommClass k R M]
variable [AddCommGroup N] [Module k N] [Module R N] [IsScalarTower k R N] [SMulCommClass k R N]
variable [AddCommGroup L] [Module k L] [Module R L] [IsScalarTower k R L] [SMulCommClass k R L]
variable {n : ℕ}

def rightCoefficients (s : F →ₗ[Rᵐᵒᵖ] (Fin n → Rᵐᵒᵖ)) :
    BalancedTensor k R F M →ₗ[k] (Fin n → M) :=
  lift
    { toFun f :=
        { toFun m i := (s f i).unop • m
          map_add' m m' := by ext i; exact smul_add _ _ _
          map_smul' c m := by ext i; exact (smul_comm c (s f i).unop m).symm }
      map_add' f f' := by
        ext m i
        change (s (f + f') i).unop • m = (s f i).unop • m + (s f' i).unop • m
        simp only [map_add, Pi.add_apply, MulOpposite.unop_add, add_smul]
      map_smul' c f := by
        ext m i
        change (s (c • f) i).unop • m = c • (s f i).unop • m
        simp only [LinearMap.map_smul_of_tower, Pi.smul_apply, MulOpposite.unop_smul,
          smul_assoc] }
    (by
      intro f r m
      ext i
      change (s (MulOpposite.op r • f) i).unop • m = (s f i).unop • (r • m)
      simp only [map_smul, Pi.smul_apply, smul_eq_mul, MulOpposite.unop_mul,
        MulOpposite.unop_op, mul_smul])

omit [SMulCommClass k Rᵐᵒᵖ F] in
@[simp] theorem rightCoefficients_tmul (s : F →ₗ[Rᵐᵒᵖ] (Fin n → Rᵐᵒᵖ))
    (f : F) (m : M) (i : Fin n) :
    rightCoefficients (k := k) s (tmul f m) i = (s f i).unop • m := rfl

def freeRecombine (p : (Fin n → Rᵐᵒᵖ) →ₗ[Rᵐᵒᵖ] F) :
    (Fin n → M) →ₗ[k] BalancedTensor k R F M :=
  ∑ i, (mk (p (Pi.single i 1))).comp (LinearMap.proj i)

omit [Algebra k R] [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F]
  [IsScalarTower k R M] [SMulCommClass k R M] in
@[simp] theorem freeRecombine_apply (p : (Fin n → Rᵐᵒᵖ) →ₗ[Rᵐᵒᵖ] F) (m : Fin n → M) :
    freeRecombine (k := k) p m = ∑ i, tmul (p (Pi.single i 1)) (m i) := by
  simp [freeRecombine, mk]

omit [SMulCommClass k Rᵐᵒᵖ F] in
theorem freeRecombine_rightCoefficients
    (s : F →ₗ[Rᵐᵒᵖ] (Fin n → Rᵐᵒᵖ)) (p : (Fin n → Rᵐᵒᵖ) →ₗ[Rᵐᵒᵖ] F)
    (h : p.comp s = LinearMap.id) (z : BalancedTensor k R F M) :
    freeRecombine p (rightCoefficients s z) = z := by
  induction z using induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul f m =>
    rw [freeRecombine_apply]
    calc
      (∑ i, tmul (p (Pi.single i 1)) (rightCoefficients s (tmul f m) i)) =
          ∑ i, tmul (p (Pi.single i (s f i))) m := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [rightCoefficients_tmul, ← balance]
        congr 1
        rw [MulOpposite.op_unop, ← p.map_smul]
        congr 1
        ext j
        by_cases hij : j = i
        · subst j; simp
        · simp [hij]
      _ = tmul (p (∑ i, Pi.single i (s f i))) m := by
        simp only [map_sum]
        exact (map_sum ((mk (k := k) (R := R)).flip m) _ _).symm
      _ = tmul f m := by
        rw [Finset.univ_sum_single]
        exact congrArg (fun f => tmul (k := k) (R := R) f m) (DFunLike.congr_fun h f)

variable {S : Type*} [Ring S] [Module S F]
variable [SMulCommClass k S F] [SMulCommClass S Rᵐᵒᵖ F]

omit [SMulCommClass k Rᵐᵒᵖ F] in
theorem rightCoefficients_natural (s : F →ₗ[Rᵐᵒᵖ] (Fin n → Rᵐᵒᵖ)) (b : M →ₗ[R] N)
    (z : BalancedTensor k R F M) :
    rightCoefficients s (mapRight (S := S) b z) = fun i => b (rightCoefficients s z i) := by
  induction z using induction_on with
  | zero => ext i; simp
  | tmul f m => ext i; simp
  | add x y hx hy =>
    ext i
    simp only [map_add, Pi.add_apply, hx, hy]

omit [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F]
  [SMulCommClass k R M] [SMulCommClass k R N] in
theorem freeRecombine_natural (p : (Fin n → Rᵐᵒᵖ) →ₗ[Rᵐᵒᵖ] F) (b : M →ₗ[R] N)
    (z : Fin n → M) :
    mapRight (S := S) b (freeRecombine p z) = freeRecombine (k := k) p (fun i => b (z i)) := by
  simp only [freeRecombine_apply, map_sum, mapRight_tmul]

omit [SMulCommClass k Rᵐᵒᵖ F] [SMulCommClass k R M] in
theorem mapRight_exact [Module.Finite Rᵐᵒᵖ F] [Module.Projective Rᵐᵒᵖ F]
    (e : M →ₗ[R] N) (d : N →ₗ[R] L) (hex : Function.Exact e d) :
    Function.Exact (mapRight (k := k) (F := F) (S := S) e) (mapRight (S := S) d) := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' Rᵐᵒᵖ F
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p (LinearMap.id : F →ₗ[Rᵐᵒᵖ] F) hp
  intro z
  constructor
  · intro hz
    have hcoords : ∀ i, d (rightCoefficients s z i) = 0 := by
      have hnat := rightCoefficients_natural (S := S) s d z
      rw [hz, map_zero] at hnat
      intro i
      exact (congrFun hnat i).symm
    choose w hw using fun i => (hex (rightCoefficients s z i)).mp (hcoords i)
    refine ⟨freeRecombine p w, ?_⟩
    rw [freeRecombine_natural]
    convert freeRecombine_rightCoefficients s p hs z using 1
    exact congrArg (freeRecombine (k := k) p) (funext hw)
  · rintro ⟨w, rfl⟩
    have hde : d.comp e = 0 := by ext m; exact (hex (e m)).mpr ⟨m, rfl⟩
    change ((mapRight (S := S) d).comp (mapRight (S := S) e)) w = 0
    rw [← mapRight_comp, hde, mapRight_zero, LinearMap.zero_apply]

end ArExplicit.BalancedTensor

end

end OAI
