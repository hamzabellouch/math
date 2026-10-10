import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.HomologicalComplexBiprod
import Mathlib.Algebra.Category.ModuleCat.Biproducts

namespace OAI
noncomputable section
open CategoryTheory Limits
namespace LittleFinitistic.PairComplex
universe u
variable {k : Type u} [Ring k]
variable (O T : CochainComplex (ModuleCat.{u} k) ℤ)

def complex : CochainComplex (ModuleCat.{u} k) ℤ :=
  CochainComplex.of (fun n => ModuleCat.of k (O.X n × T.X n))
    (fun n => ModuleCat.ofHom ((O.d n (n+1)).hom.prodMap (T.d n (n+1)).hom)) (by
      intro n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact Prod.ext (congrArg (fun h => h.hom x.1) (O.d_comp_d n (n+1) ((n+1)+1)))
        (congrArg (fun h => h.hom x.2) (T.d_comp_d n (n+1) ((n+1)+1))))

theorem complex_d (n : ℤ) : (complex O T).d n (n+1) =
    ModuleCat.ofHom ((O.d n (n+1)).hom.prodMap (T.d n (n+1)).hom) :=
  CochainComplex.of_d (fun n => ModuleCat.of k (O.X n × T.X n))
    (fun n => ModuleCat.ofHom ((O.d n (n+1)).hom.prodMap (T.d n (n+1)).hom)) n

def fst : complex O T ⟶ O where
  f n := ModuleCat.ofHom (LinearMap.fst k (O.X n) (T.X n))
  comm' n m h := by
    change n+1=m at h
    subst m
    rw [complex_d]
    rfl

def snd : complex O T ⟶ T where
  f n := ModuleCat.ofHom (LinearMap.snd k (O.X n) (T.X n))
  comm' n m h := by
    change n+1=m at h
    subst m
    rw [complex_d]
    rfl

def inl : O ⟶ complex O T where
  f n := ModuleCat.ofHom (LinearMap.inl k (O.X n) (T.X n))
  comm' n m h := by
    change n+1=m at h
    subst m
    rw [complex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Prod.ext rfl ((T.d n (n+1)).hom.map_zero)

def inr : T ⟶ complex O T where
  f n := ModuleCat.ofHom (LinearMap.inr k (O.X n) (T.X n))
  comm' n m h := by
    change n+1=m at h
    subst m
    rw [complex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Prod.ext ((O.d n (n+1)).hom.map_zero) rfl

@[simp] theorem inl_fst : inl O T ≫ fst O T = 𝟙 O := by ext degree element; rfl
@[simp] theorem inl_snd : inl O T ≫ snd O T = 0 := by ext degree element; rfl
@[simp] theorem inr_fst : inr O T ≫ fst O T = 0 := by ext degree element; rfl
@[simp] theorem inr_snd : inr O T ≫ snd O T = 𝟙 T := by ext degree element; rfl

/-- The actual coordinate complex is the native binary biproduct. -/
def biprodIso : complex O T ≅ O ⊞ T where
  hom := biprod.lift (fst O T) (snd O T)
  inv := biprod.desc (inl O T) (inr O T)
  hom_inv_id := by
    rw [biprod.lift_desc]
    ext n x
    exact Prod.ext (add_zero _) (zero_add _)
  inv_hom_id := by
    apply biprod.hom_ext <;> apply biprod.hom_ext' <;> simp [Category.assoc]
end LittleFinitistic.PairComplex

end

end OAI
