import Mathlib

namespace OAI


                                         
section

namespace MaximalSeshadri.PlaneCech
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

def cycles (A B C : Submodule K M) : Submodule K (A × B × C) :=
  LinearMap.ker
    ({ toFun := fun x => (x.1 : M) + (x.2.1 : M) + (x.2.2 : M)
       map_add' := by intros; simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add]; abel
       map_smul' := by intros; simp only [Prod.smul_fst, Prod.smul_snd,
        Submodule.coe_smul_of_tower, smul_add, RingHom.id_apply] } :
        (A × B × C) →ₗ[K] M)

def edgeAB (A B C : Submodule K M) : ↥(A ⊓ B) →ₗ[K] cycles A B C where
  toFun x := ⟨(⟨x,x.property.1⟩,⟨-x,B.neg_mem x.property.2⟩,0), by
    change (x : M) + -(x : M) + 0 = 0; simp⟩
  map_add' := by intros; ext <;> simp; all_goals abel
  map_smul' := by intros; ext <;> simp

def edgeAC (A B C : Submodule K M) : ↥(A ⊓ C) →ₗ[K] cycles A B C where
  toFun x := ⟨(⟨x,x.property.1⟩,0,⟨-x,C.neg_mem x.property.2⟩), by
    change (x : M) + 0 + -(x : M) = 0; simp⟩
  map_add' := by intros; ext <;> simp; all_goals abel
  map_smul' := by intros; ext <;> simp

def edgeBC (A B C : Submodule K M) : ↥(B ⊓ C) →ₗ[K] cycles A B C where
  toFun x := ⟨(0,⟨x,x.property.1⟩,⟨-x,C.neg_mem x.property.2⟩), by
    change 0 + (x : M) + -(x : M) = 0; simp⟩
  map_add' := by intros; ext <;> simp; all_goals abel
  map_smul' := by intros; ext <;> simp

def boundaries (A B C : Submodule K M)
    (N₀ : Submodule K ↥(A ⊓ B)) (N₁ : Submodule K ↥(A ⊓ C))
    (N₂ : Submodule K ↥(B ⊓ C)) : Submodule K (cycles A B C) :=
  N₀.map (edgeAB A B C) ⊔ N₁.map (edgeAC A B C) ⊔ N₂.map (edgeBC A B C)

def fullBoundaries (A B C : Submodule K M) : Submodule K (cycles A B C) :=
  (edgeAB A B C).range ⊔ (edgeAC A B C).range ⊔ (edgeBC A B C).range

theorem fullBoundaries_eq_top (A B C : Submodule K M)
    (h : A ⊓ (B ⊔ C) ≤ (A ⊓ B) ⊔ (A ⊓ C)) :
    fullBoundaries A B C = ⊤ := by
  apply top_unique
  rintro ⟨⟨a,b,c⟩,hx⟩ _
  have he : (a : M) + (b : M) + (c : M) = 0 := by exact hx
  have ha : (a : M) ∈ A ⊓ (B ⊔ C) := by
    refine ⟨a.property,?_⟩
    have haa : (a : M) = -(b : M) + -(c : M) := by
      calc
        _ = (a : M) + b + c - b - c := by abel
        _ = _ := by rw [he]; abel
    rw [haa]
    exact Submodule.add_mem_sup (B.neg_mem b.property) (C.neg_mem c.property)
  obtain ⟨u,hu,v,hv,huv⟩ := Submodule.mem_sup.mp (h ha)
  have hb : (b : M) + u ∈ B ⊓ C := by
    refine ⟨B.add_mem b.property hu.2,?_⟩
    have heq : (b : M) + u = -((c : M) + v) := by
      apply eq_neg_iff_add_eq_zero.mpr
      calc
        _ = (a : M) + b + c := by rw [← huv]; abel
        _ = 0 := he
    rw [heq]
    exact C.neg_mem (C.add_mem c.property hv.2)
  have heq : (⟨⟨a,b,c⟩,hx⟩ : cycles A B C) =
      edgeAB A B C ⟨u,hu⟩ + edgeAC A B C ⟨v,hv⟩ +
        edgeBC A B C ⟨(b : M)+u,hb⟩ := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      change (a : M) = u + v + 0
      simpa using huv.symm
    apply Prod.ext
    · apply Subtype.ext; change (b : M) = -u + 0 + ((b : M)+u); abel
    · apply Subtype.ext
      change (c : M) = 0 + -v + -((b : M)+u)
      calc
        _ = -(v + (b : M) + u) := by
          apply eq_neg_iff_add_eq_zero.mpr
          calc
            _ = (a : M) + b + c := by rw [← huv]; abel
            _ = 0 := he
        _ = _ := by abel
  rw [heq]
  exact (fullBoundaries A B C).add_mem
    ((fullBoundaries A B C).add_mem
      ((show (edgeAB A B C).range ≤ fullBoundaries A B C from
        le_sup_of_le_left le_sup_left) ⟨_,rfl⟩)
      ((show (edgeAC A B C).range ≤ fullBoundaries A B C from
        le_sup_of_le_left le_sup_right) ⟨_,rfl⟩))
    ((show (edgeBC A B C).range ≤ fullBoundaries A B C from le_sup_right) ⟨_,rfl⟩)

end
end MaximalSeshadri.PlaneCech

end



end OAI
