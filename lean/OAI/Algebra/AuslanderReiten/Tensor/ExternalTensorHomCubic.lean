import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorHomDifferential
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorCubicChain

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (P : ChainComplex (ModuleCat.{u} A) ℕ) (Q : ChainComplex (ModuleCat.{u} B) ℕ)
variable (U : ModuleCat.{u} A) (V : ModuleCat.{u} B)
variable [∀ n, Module.Finite A (P.X n)] [∀ n, Module.Projective A (P.X n)]
variable [∀ n, Module.Finite B (Q.X n)] [∀ n, Module.Projective B (Q.X n)]

theorem elementary_cubicInsert_same (i j n : ℕ) (h : i+j=n)
    (f : P.X i →ₗ[A] U) (g : Q.X j →ₗ[B] V)
    (x : moduleObject k A B (P.X i) (Q.X j)) :
    elementaryHom k A B P Q U V i j n h f g
      (cubicInsert k A B P Q n ⟨(i,j),h⟩ x) = map k A B f g x := by
  have hh := homCochainTermEquiv_inclusion_same k A B P Q U V i j n h (f ⊗ₜ[k] g)
  rw [inclusion_eq_cubicInsert, homMap_tmul] at hh
  exact DFunLike.congr_fun hh x

theorem elementary_cubicInsert_ne (i j n : ℕ) (h : i+j=n)
    (f : P.X i →ₗ[A] U) (g : Q.X j →ₗ[B] V)
    (a b : ℕ) (hab : a+b=n) (hne : (a,b) ≠ (i,j))
    (x : moduleObject k A B (P.X a) (Q.X b)) :
    elementaryHom k A B P Q U V i j n h f g
      (cubicInsert k A B P Q n ⟨(a,b),hab⟩ x) = 0 := by
  have hh := homCochainTermEquiv_inclusion_ne k A B P Q U V i j n h (f ⊗ₜ[k] g) a b hab hne
  rw [inclusion_eq_cubicInsert] at hh
  exact DFunLike.congr_fun hh x

private theorem map_first_comp {M M' : ModuleCat.{u} A} {N : ModuleCat.{u} B}
    (f : M →ₗ[A] U) (g : N →ₗ[B] V) (p : M' →ₗ[A] M)
    (x : moduleObject k A B M' N) :
    map k A B f g (map k A B p (LinearMap.id : N →ₗ[B] N) x) =
      map k A B (f.comp p) g x := by
  have h : (map k A B f g).comp (map k A B p (LinearMap.id : N →ₗ[B] N)) =
      map k A B (f.comp p) g := by
    apply LinearMap.restrictScalars_injective k
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    rfl
  exact DFunLike.congr_fun h x

theorem elementary_firstCubic
    (p : ∀ n, P.X (n+3) ⟶ P.X n)
    (i j n : ℕ) (h : i+j=n) (f : P.X i →ₗ[A] U) (g : Q.X j →ₗ[B] V) :
    (elementaryHom k A B P Q U V i j n h f g).comp (firstCubic k A B P Q p n) =
      elementaryHom k A B P Q U V (i+3) j (n+3) (by omega) (f.comp (p i).hom) g := by
  apply cubic_hom_ext k A B P Q (n+3)
  rintro ⟨⟨a,b⟩,hab⟩ x
  simp only [LinearMap.comp_apply, firstCubic_insert]
  rcases a with _ | (_ | (_ | a))
  · simp only [firstCubicEntry, LinearMap.zero_apply, map_zero]
    exact (elementary_cubicInsert_ne k A B P Q U V (i+3) j (n+3) (by omega)
      (f.comp (p i).hom) g 0 b hab (by intro he; have := congrArg Prod.fst he; omega) x).symm
  · simp only [firstCubicEntry, LinearMap.zero_apply, map_zero]
    exact (elementary_cubicInsert_ne k A B P Q U V (i+3) j (n+3) (by omega)
      (f.comp (p i).hom) g 1 b hab (by intro he; have := congrArg Prod.fst he; omega) x).symm
  · simp only [firstCubicEntry, LinearMap.zero_apply, map_zero]
    exact (elementary_cubicInsert_ne k A B P Q U V (i+3) j (n+3) (by omega)
      (f.comp (p i).hom) g 2 b hab (by intro he; have := congrArg Prod.fst he; omega) x).symm
  · by_cases ha : a=i
    · subst a
      have hb : b=j := by omega
      subst b
      simp only [firstCubicEntry, LinearMap.comp_apply, elementary_cubicInsert_same]
      exact map_first_comp k A B U V f g (p i).hom x
    · have hn : (a,b)≠(i,j) := by intro he; exact ha (congrArg Prod.fst he)
      have hn' : (a+3,b)≠(i+3,j) := by intro he; have := congrArg Prod.fst he; omega
      simp only [firstCubicEntry, LinearMap.comp_apply]
      rw [elementary_cubicInsert_ne k A B P Q U V i j n h f g a b (by omega) hn,
        elementary_cubicInsert_ne k A B P Q U V (i+3) j (n+3) (by omega)
          (f.comp (p i).hom) g (a+3) b hab hn']

private theorem map_second_comp {M : ModuleCat.{u} A} {N N' : ModuleCat.{u} B}
    (f : M →ₗ[A] U) (g : N →ₗ[B] V) (r : N' →ₗ[B] N)
    (x : moduleObject k A B M N') :
    map k A B f g (map k A B (LinearMap.id : M →ₗ[A] M) r x) =
      map k A B f (g.comp r) x := by
  have h : (map k A B f g).comp (map k A B (LinearMap.id : M →ₗ[A] M) r) =
      map k A B f (g.comp r) := by
    apply LinearMap.restrictScalars_injective k
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    rfl
  exact DFunLike.congr_fun h x

theorem elementary_secondCubic
    (r : ∀ n, Q.X (n+3) ⟶ Q.X n)
    (i j n : ℕ) (h : i+j=n) (f : P.X i →ₗ[A] U) (g : Q.X j →ₗ[B] V) :
    (elementaryHom k A B P Q U V i j n h f g).comp (secondCubic k A B P Q r n) =
      elementaryHom k A B P Q U V i (j+3) (n+3) (by omega) f (g.comp (r j).hom) := by
  apply cubic_hom_ext k A B P Q (n+3)
  rintro ⟨⟨a,b⟩,hab⟩ x
  simp only [LinearMap.comp_apply, secondCubic_insert]
  rcases b with _ | (_ | (_ | b))
  · simp only [secondCubicEntry, LinearMap.zero_apply, map_zero]
    exact (elementary_cubicInsert_ne k A B P Q U V i (j+3) (n+3) (by omega)
      f (g.comp (r j).hom) a 0 hab (by intro he; have := congrArg Prod.snd he; omega) x).symm
  · simp only [secondCubicEntry, LinearMap.zero_apply, map_zero]
    exact (elementary_cubicInsert_ne k A B P Q U V i (j+3) (n+3) (by omega)
      f (g.comp (r j).hom) a 1 hab (by intro he; have := congrArg Prod.snd he; omega) x).symm
  · simp only [secondCubicEntry, LinearMap.zero_apply, map_zero]
    exact (elementary_cubicInsert_ne k A B P Q U V i (j+3) (n+3) (by omega)
      f (g.comp (r j).hom) a 2 hab (by intro he; have := congrArg Prod.snd he; omega) x).symm
  · by_cases hb : b=j
    · subst b
      have ha : a=i := by omega
      subst a
      simp only [secondCubicEntry, LinearMap.comp_apply, elementary_cubicInsert_same]
      exact map_second_comp k A B U V f g (r j).hom x
    · have hn : (a,b)≠(i,j) := by intro he; exact hb (congrArg Prod.snd he)
      have hn' : (a,b+3)≠(i,j+3) := by intro he; have := congrArg Prod.snd he; omega
      simp only [secondCubicEntry, LinearMap.comp_apply]
      rw [elementary_cubicInsert_ne k A B P Q U V i j n h f g a b (by omega) hn,
        elementary_cubicInsert_ne k A B P Q U V i (j+3) (n+3) (by omega)
          f (g.comp (r j).hom) a (b+3) hab hn']

end ArExplicit.ExternalTensor

end

end OAI
