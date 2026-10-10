import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.LaurentPlane
import OAI.AlgebraicGeometry.Seshadri.Cohomology.PlaneCechLinear

namespace OAI


                                       
section

namespace MaximalSeshadri.PlaneCech
noncomputable section
variable {K : Type*} [Field K]

lemma supported_distrib {ι V : Type*} [AddCommGroup V] [Module K V]
    (S T U : Set ι) :
    Finsupp.supported V K S ⊓ (Finsupp.supported V K T ⊔ Finsupp.supported V K U) =
      (Finsupp.supported V K S ⊓ Finsupp.supported V K T) ⊔
        (Finsupp.supported V K S ⊓ Finsupp.supported V K U) := by
  rw [← Finsupp.supported_union, ← Finsupp.supported_inter,
    Set.inter_union_distrib_left, Finsupp.supported_union,
    Finsupp.supported_inter, Finsupp.supported_inter]

lemma pi_inf_sup_distrib {ι : Type*} {V : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    (A B C : ∀ i, Submodule K (V i))
    (h : ∀ i, A i ⊓ (B i ⊔ C i) ≤ (A i ⊓ B i) ⊔ (A i ⊓ C i)) :
    Submodule.pi Set.univ A ⊓ (Submodule.pi Set.univ B ⊔ Submodule.pi Set.univ C) ≤
      (Submodule.pi Set.univ A ⊓ Submodule.pi Set.univ B) ⊔
        (Submodule.pi Set.univ A ⊓ Submodule.pi Set.univ C) := by
  classical
  rintro m ⟨hm,hBC⟩
  obtain ⟨b,hb,c,hc,hbc⟩ := Submodule.mem_sup.mp hBC
  have hm' (i : ι) : m i ∈ (A i ⊓ B i) ⊔ (A i ⊓ C i) := by
    apply h i
    refine ⟨hm i (Set.mem_univ i),?_⟩
    rw [← hbc]
    exact Submodule.add_mem_sup (hb i (Set.mem_univ i)) (hc i (Set.mem_univ i))
  choose x hx y hy hxy using fun i => Submodule.mem_sup.mp (hm' i)
  apply Submodule.mem_sup.mpr
  refine ⟨x,⟨?_,?_⟩,y,⟨?_,?_⟩,?_⟩
  · exact fun i _ => (hx i).1
  · exact fun i _ => (hx i).2
  · exact fun i _ => (hy i).1
  · exact fun i _ => (hy i).2
  · exact funext hxy

def laurentSupported (S : Set (ℤ × ℤ)) : Submodule K (LaurentPlane.Ring K) :=
  (Finsupp.supported K K S).comap (AddMonoidAlgebra.coeffLinearEquiv K).toLinearMap

lemma laurentSupported_distrib (S T U : Set (ℤ × ℤ)) :
    laurentSupported (K := K) S ⊓ (laurentSupported T ⊔ laurentSupported U) =
      (laurentSupported S ⊓ laurentSupported T) ⊔
        (laurentSupported S ⊓ laurentSupported U) := by
  let e : LaurentPlane.Ring K ≃ₗ[K] (ℤ × ℤ →₀ K) := AddMonoidAlgebra.coeffLinearEquiv K
  have hsup (P Q : Submodule K (ℤ × ℤ →₀ K)) :
      (P ⊔ Q).comap e.toLinearMap = P.comap e.toLinearMap ⊔ Q.comap e.toLinearMap := by
    simp only [Submodule.comap_equiv_eq_map_symm, Submodule.map_sup]
  change (Finsupp.supported K K S).comap e.toLinearMap ⊓
      ((Finsupp.supported K K T).comap e.toLinearMap ⊔
        (Finsupp.supported K K U).comap e.toLinearMap) = _
  rw [← hsup, ← Submodule.comap_inf, supported_distrib, hsup,
    Submodule.comap_inf, Submodule.comap_inf]
  rfl

def coneA : Set (ℤ × ℤ) := {z | 0 ≤ z.2}
def coneB : Set (ℤ × ℤ) := {z | 0 ≤ z.1}
def coneC (d : ℤ) : Set (ℤ × ℤ) := {z | z.1 + z.2 ≤ d}

def freeA (ι : Type*) : Submodule K (ι → LaurentPlane.Ring K) :=
  Submodule.pi Set.univ (fun _ => laurentSupported coneA)
def freeB (ι : Type*) : Submodule K (ι → LaurentPlane.Ring K) :=
  Submodule.pi Set.univ (fun _ => laurentSupported coneB)
def freeC (ι : Type*) (d : ℤ) : Submodule K (ι → LaurentPlane.Ring K) :=
  Submodule.pi Set.univ (fun _ => laurentSupported (coneC d))

theorem free_H1_zero (ι : Type*) (d : ℤ) :
    fullBoundaries (freeA (K := K) ι) (freeB ι) (freeC ι d) = ⊤ := by
  apply fullBoundaries_eq_top
  apply pi_inf_sup_distrib
  intro i
  exact le_of_eq (laurentSupported_distrib coneA coneB (coneC d))

lemma triangle_finite (d : ℤ) : (coneA ∩ coneB ∩ coneC d).Finite := by
  apply (Set.finite_Icc (0,0) (d,d)).subset
  rintro ⟨a,b⟩ ⟨⟨ha,hb⟩,hc⟩
  change 0 ≤ b at ha
  change 0 ≤ a at hb
  change a+b ≤ d at hc
  exact ⟨⟨hb,ha⟩,⟨by omega,by omega⟩⟩

theorem free_H0_finite (ι : Type*) [Finite ι] (d : ℤ) :
    Module.Finite K ↥((freeA (K := K) ι ⊓ freeB ι) ⊓ freeC ι d) := by
  let := Fintype.ofFinite ι
  let Q := Finsupp.supported K K (coneA ∩ coneB ∩ coneC d)
  let : Finite ↥(coneA ∩ coneB ∩ coneC d) := (triangle_finite d).to_subtype
  let : Module.Finite K Q := Module.Finite.equiv
    (Finsupp.supportedEquivFinsupp (M := K) (R := K) (coneA ∩ coneB ∩ coneC d)).symm
  let F : ↥((freeA (K := K) ι ⊓ freeB ι) ⊓ freeC ι d) →ₗ[K] (ι → Q) :=
    { toFun := fun m i => ⟨(m.1 i).coeff, by
        change _ ∈ Finsupp.supported K K (coneA ∩ coneB ∩ coneC d)
        rw [Finsupp.supported_inter,Finsupp.supported_inter]
        exact ⟨⟨m.2.1.1 i (Set.mem_univ i),m.2.1.2 i (Set.mem_univ i)⟩,
          m.2.2 i (Set.mem_univ i)⟩⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let : Module.Finite K (ι → Q) := inferInstance
  let : IsNoetherian K (ι → Q) := isNoetherian_of_isNoetherianRing_of_finite K (ι → Q)
  apply Module.Finite.of_injective F
  intro m n h
  apply Subtype.ext
  exact funext fun i => (AddMonoidAlgebra.coeffLinearEquiv K).injective
    (congrArg Subtype.val (congrFun h i))

end
end MaximalSeshadri.PlaneCech

end


end OAI
