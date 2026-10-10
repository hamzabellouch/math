import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.ToricCoordinates
import OAI.AlgebraicGeometry.Seshadri.Cohomology.ToricSpan

namespace OAI


                                         
section

namespace MaximalSeshadri.PlaneCech
noncomputable section
open LaurentPlane
variable {K : Type*} [Field K]

def vertexPolynomial (i : Fin 3) : MvPolynomial (Fin 3) K →ₐ[K] LaurentPlane.Ring K :=
  MvPolynomial.aeval (fun j => T (weight j-weight i))

lemma vertexPolynomial_X (i j : Fin 3) :
    vertexPolynomial (K := K) i (MvPolynomial.X j) = T (weight j-weight i) := by
  simp [vertexPolynomial]

lemma vertexPolynomial_monomial (i : Fin 3) (z : ℤ × ℤ) (hz : z ∈ vertexCone i) :
    ∃ p : MvPolynomial (Fin 3) K, vertexPolynomial i p = T z := by
  have lift (j l : Fin 3) (n m : ℕ) (he : n • (weight j-weight i) + m • (weight l-weight i) = z) :
      ∃ p : MvPolynomial (Fin 3) K, vertexPolynomial i p = T z := by
    refine ⟨MvPolynomial.X j ^ n * MvPolynomial.X l ^ m,?_⟩
    rw [map_mul,map_pow,map_pow,vertexPolynomial_X,vertexPolynomial_X,← T_nsmul,← T_nsmul,← T_add,he]
  fin_cases i
  · apply lift 1 2 z.1.toNat z.2.toNat
    have ha : 0 ≤ z.1 := hz.2
    have hb : 0 ≤ z.2 := hz.1
    ext <;> simp [weight,Int.toNat_of_nonneg ha,Int.toNat_of_nonneg hb]
  · apply lift 0 2 (-(z.1+z.2)).toNat z.2.toNat
    have ha : 0 ≤ -(z.1+z.2) := by have := hz.2; change z.1+z.2 ≤ 0 at this; omega
    have hb : 0 ≤ z.2 := hz.1
    ext <;> simp [weight,Int.toNat_of_nonneg hb]
    omega
  · apply lift 0 1 (-(z.1+z.2)).toNat z.1.toNat
    have ha : 0 ≤ -(z.1+z.2) := by have := hz.2; change z.1+z.2 ≤ 0 at this; omega
    have hb : 0 ≤ z.1 := hz.1
    ext <;> simp [weight,Int.toNat_of_nonneg hb]
    omega

variable {M : Type*} [AddCommGroup M] [Module K M]
  [Module (LaurentPlane.Ring K) M] [IsScalarTower K (LaurentPlane.Ring K) M]

abbrev vertexModule (i : Fin 3) : Module (MvPolynomial (Fin 3) K) M :=
  Module.compHom M (vertexPolynomial i).toRingHom

lemma vertexModule_tower (i : Fin 3) :
    letI := vertexModule (K := K) (M := M) i
    IsScalarTower K (MvPolynomial (Fin 3) K) M := by
  let := vertexModule (K := K) (M := M) i
  apply IsScalarTower.of_algebraMap_smul
  intro a m
  change vertexPolynomial i (algebraMap K (MvPolynomial (Fin 3) K) a) • m = a • m
  rw [AlgHom.commutes,IsScalarTower.algebraMap_smul]

def vertexSubmodule (i : Fin 3) (V : Submodule K M)
    (stable : ∀ z ∈ vertexCone i, ∀ x ∈ V, T (K := K) z • x ∈ V) :
    letI := vertexModule (K := K) (M := M) i
    Submodule (MvPolynomial (Fin 3) K) M := by
  letI := vertexModule (K := K) (M := M) i
  refine { V.toAddSubgroup with smul_mem' := ?_ }
  intro p m hm
  change vertexPolynomial i p • m ∈ V
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [← MvPolynomial.algebraMap_eq,AlgHom.commutes,IsScalarTower.algebraMap_smul]
    exact V.smul_mem a hm
  | add p q hp hq => simpa only [map_add,add_smul] using V.add_mem hp hq
  | mul_X p j hp =>
    rw [map_mul,vertexPolynomial_X,mul_comm,mul_smul]
    exact stable _ (by simpa using direction_mem i j 1) _ hp

lemma vertexSubmodule_finite (i : Fin 3) (V : Submodule K M)
    (stable : ∀ z ∈ vertexCone i, ∀ x ∈ V, T (K := K) z • x ∈ V)
    {ι : Type*} [Finite ι] (g : ι → M) (hg : ∀ a, g a ∈ V)
    (hgen : V = monomialSpan (K := K) (vertexCone i) g) :
    letI := vertexModule (K := K) (M := M) i
    Module.Finite (MvPolynomial (Fin 3) K) (vertexSubmodule i V stable) := by
  let := vertexModule (K := K) (M := M) i
  let := vertexModule_tower (K := K) (M := M) i
  let W := vertexSubmodule i V stable
  let H := Submodule.span (MvPolynomial (Fin 3) K) (Set.range g)
  have he : W = H := by
    apply le_antisymm
    · intro x hx
      change x ∈ V at hx
      rw [hgen] at hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a,z,hz,rfl⟩ := hx
        obtain ⟨p,hp⟩ := vertexPolynomial_monomial (K := K) i z hz
        have hh := H.smul_mem p (Submodule.subset_span (Set.mem_range_self a))
        change vertexPolynomial i p • g a ∈ H at hh
        rwa [hp] at hh
      | zero => exact H.zero_mem
      | add x y hx hy ih ih' => exact H.add_mem ih ih'
      | smul a x hx ih => exact (H.restrictScalars K).smul_mem a ih
    · apply Submodule.span_le.mpr
      rintro _ ⟨a,rfl⟩
      exact hg a
  change Module.Finite (MvPolynomial (Fin 3) K) W
  rw [he]
  exact Module.Finite.span_of_finite _ (Set.finite_range g)

end
end MaximalSeshadri.PlaneCech

end

end OAI
