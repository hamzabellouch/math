import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.PlaneCechLinear

namespace OAI


                                          
section

namespace MaximalSeshadri.PlaneCech
noncomputable section
variable {K M P : Type*} [Field K] [AddCommGroup M] [Module K M]
  [AddCommGroup P] [Module K P]

def cycleMap (f : P →ₗ[K] M) (A B C : Submodule K P) (D E F : Submodule K M)
    (hA : ∀ x ∈ A, f x ∈ D) (hB : ∀ x ∈ B, f x ∈ E)
    (hC : ∀ x ∈ C, f x ∈ F) : cycles A B C →ₗ[K] cycles D E F where
  toFun x := ⟨(⟨f x.1.1,hA _ x.1.1.2⟩,⟨f x.1.2.1,hB _ x.1.2.1.2⟩,
      ⟨f x.1.2.2,hC _ x.1.2.2.2⟩),by
    change f (x.1.1 : P) + f (x.1.2.1 : P) + f (x.1.2.2 : P) = 0
    rw [← map_add,← map_add]
    rw [show (x.1.1 : P) + (x.1.2.1 : P) + (x.1.2.2 : P) = 0 from x.2, map_zero]⟩
  map_add' := by intros; ext <;> simp
  map_smul' := by intros; ext <;> simp

theorem finite_quotient_of_kernel_le {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Module.Finite K W]
    (f : V →ₗ[K] W) (B : Submodule K V) (h : LinearMap.ker f ≤ B) :
    Module.Finite K (V ⧸ B) := by
  let : Module.Finite K (V ⧸ LinearMap.ker f) := Module.Finite.equiv f.quotKerEquivRange.symm
  let q : (V ⧸ LinearMap.ker f) →ₗ[K] (V ⧸ B) :=
    Submodule.mapQ (LinearMap.ker f) B LinearMap.id h
  apply Module.Finite.of_surjective q
  intro x
  obtain ⟨v,rfl⟩ := B.mkQ_surjective x
  exact ⟨(LinearMap.ker f).mkQ v,rfl⟩

theorem finite_H1_of_presentation
    (f : P →ₗ[K] M) (A B C : Submodule K P) (D E F : Submodule K M)
    (hA : ∀ x ∈ A, f x ∈ D) (hB : ∀ x ∈ B, f x ∈ E)
    (hC : ∀ x ∈ C, f x ∈ F)
    (sA : A →ₗ[K] D) (sB : B →ₗ[K] E) (sC : C →ₗ[K] F)
    (eA : ∀ x, (sA x : M) = f x) (eB : ∀ x, (sB x : M) = f x)
    (eC : ∀ x, (sC x : M) = f x)
    (surA : Function.Surjective sA) (surB : Function.Surjective sB)
    (surC : Function.Surjective sC)
    (Q : Submodule K (cycles D E F))
    (hQ : (fullBoundaries A B C).map (cycleMap f A B C D E F hA hB hC) ≤ Q)
    (acyclic : fullBoundaries A B C = ⊤)
    (hfinite : Module.Finite K ((LinearMap.ker f) ⧸
      (((A.comap (LinearMap.ker f).subtype) ⊔ (B.comap (LinearMap.ker f).subtype)) ⊔
        (C.comap (LinearMap.ker f).subtype)))) :
    Module.Finite K ((cycles D E F) ⧸ Q) := by
  obtain ⟨lA,hlA⟩ := sA.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr surA)
  obtain ⟨lB,hlB⟩ := sB.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr surB)
  obtain ⟨lC,hlC⟩ := sC.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr surC)
  have eltA (x : D) : f (lA x) = x := (eA _).symm.trans (congrArg Subtype.val (LinearMap.congr_fun hlA x))
  have eltB (x : E) : f (lB x) = x := (eB _).symm.trans (congrArg Subtype.val (LinearMap.congr_fun hlB x))
  have eltC (x : F) : f (lC x) = x := (eC _).symm.trans (congrArg Subtype.val (LinearMap.congr_fun hlC x))
  let g : cycles D E F →ₗ[K] LinearMap.ker f :=
    { toFun := fun x => ⟨(lA x.1.1 : P) + (lB x.1.2.1 : P) + (lC x.1.2.2 : P),by
        change f _ = 0
        rw [map_add,map_add,eltA,eltB,eltC]
        exact x.2⟩
      map_add' := by intros; ext; simp; abel
      map_smul' := by intros; ext; simp [smul_add] }
  let R := ((A.comap (LinearMap.ker f).subtype) ⊔ (B.comap (LinearMap.ker f).subtype)) ⊔
    (C.comap (LinearMap.ker f).subtype)
  let := hfinite
  apply finite_quotient_of_kernel_le (R.mkQ.comp g) Q
  intro x hx
  have hxR : g x ∈ R := (Submodule.Quotient.mk_eq_zero R).mp hx
  obtain ⟨ab,hab,c,hc,habc⟩ := Submodule.mem_sup.mp hxR
  obtain ⟨a,ha,b,hb,hab'⟩ := Submodule.mem_sup.mp hab
  have heq : (a : P) + (b : P) + (c : P) =
      (lA x.1.1 : P) + (lB x.1.2.1 : P) + (lC x.1.2.2 : P) := by
    change _ = (g x : P)
    rw [← habc,← hab']; rfl
  let y : cycles A B C := ⟨(⟨(lA x.1.1 : P)-a,A.sub_mem (lA _).2 ha⟩,
    ⟨(lB x.1.2.1 : P)-b,B.sub_mem (lB _).2 hb⟩,
    ⟨(lC x.1.2.2 : P)-c,C.sub_mem (lC _).2 hc⟩),by
    change ((lA x.1.1 : P) - a) + ((lB x.1.2.1 : P) - b) + ((lC x.1.2.2 : P) - c) = 0
    calc
      _ = ((lA x.1.1 : P)+(lB x.1.2.1 : P)+(lC x.1.2.2 : P)) - (a+b+c : P) := by abel
      _ = 0 := by rw [heq]; simp⟩
  have hy : cycleMap f A B C D E F hA hB hC y = x := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      change f ((lA x.1.1 : P)-a) = (x.1.1 : M)
      rw [map_sub,eltA,show f a = 0 from a.2,sub_zero]
    apply Prod.ext
    · apply Subtype.ext
      change f ((lB x.1.2.1 : P)-b) = (x.1.2.1 : M)
      rw [map_sub,eltB,show f b = 0 from b.2,sub_zero]
    · apply Subtype.ext
      change f ((lC x.1.2.2 : P)-c) = (x.1.2.2 : M)
      rw [map_sub,eltC,show f c = 0 from c.2,sub_zero]
  exact hQ (Submodule.mem_map.mpr ⟨y,acyclic ▸ Submodule.mem_top,hy⟩)

end
end MaximalSeshadri.PlaneCech

end


end OAI
