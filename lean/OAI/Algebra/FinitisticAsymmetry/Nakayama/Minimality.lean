import Mathlib
import OAI.Algebra.Finitistic.Dimension.PDMinimalData
import OAI.Algebra.FinitisticAsymmetry.Nakayama.Modules

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.Nakayama
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]

lemma split_of_dual_surjective {P Q : ModuleCat.{u} R} (F : Frame R P)
    (d : P ⟶ Q) (h : Function.Surjective (LinearMap.lcomp k R d.hom)) :
    ∃ s : Q ⟶ P, d ≫ s = 𝟙 P := by
  classical
  choose c hc using fun i => h (F.c i)
  let s : Q →ₗ[R] P := ∑ i, (c i).smulRight (F.b i)
  refine ⟨ModuleCat.ofHom s, ?_⟩
  apply ModuleCat.hom_ext
  ext x
  change s (d x) = x
  simp only [s, LinearMap.sum_apply, LinearMap.smulRight_apply]
  have hh (i : Fin F.n) : c i (d x) = F.c i x := LinearMap.congr_fun (hc i) x
  simp only [hh]
  exact F.expand x

lemma nakayama_map_not_injective {P Q : ModuleCat.{u} R}
    [Module.Finite R P] [Module.Projective R P] [Nontrivial P]
    (d : P ⟶ Q) (h : ¬ ∃ s : Q ⟶ P, d ≫ s = 𝟙 P) :
    ¬ Function.Injective (map (k := k) d) := by
  intro hd
  apply h
  obtain ⟨F⟩ := frame_nonempty R P
  apply split_of_dual_surjective (k := k) F d
  apply LinearMap.dualMap_injective_iff.mp
  exact hd

variable [FiniteDimensional k R]

lemma minimal_differential_not_split (M : PDMinimal.FiniteModule k R) (n : ℕ)
    [Nontrivial (PDMinimal.term M (n+1))] :
    ¬ ∃ s : (PDMinimal.term M n).cat ⟶ (PDMinimal.term M (n+1)).cat,
      ModuleCat.ofHom (PDMinimal.differential M n) ≫ s = 𝟙 _ := by
  rintro ⟨s, hs⟩
  let d := PDMinimal.differential M n
  let e : PDMinimal.term M n →ₗ[R] PDMinimal.term M n := LinearMap.id - d.comp s.hom
  have he : (PDMinimal.augment M n).comp e = PDMinimal.augment M n := by
    ext x
    change PDMinimal.augment M n (x - d (s x)) = PDMinimal.augment M n x
    rw [map_sub]
    have hh := LinearMap.congr_fun (PDMinimal.augment_differential M n) (s x)
    change PDMinimal.augment M n (d (s x)) = 0 at hh
    rw [hh, sub_zero]
  have hes : Function.Surjective e := (PDMinimal.cover _).minimal e he
  have hei : Function.Injective e :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := e.restrictScalars k) rfl).mpr hes
  have hd (x : PDMinimal.term M (n+1)) : d x = 0 := by
    have hh : s (d x) = x := ConcreteCategory.congr_hom hs x
    apply hei
    change d x - d (s (d x)) = 0 - d (s 0)
    erw [hh, sub_self, map_zero, map_zero, sub_self]
  have hz (x : PDMinimal.term M (n+1)) : x=0 := by
    have hh : s (d x) = x := ConcreteCategory.congr_hom hs x
    erw [hd, map_zero] at hh
    exact hh.symm
  obtain ⟨x,y,hxy⟩ := exists_pair_ne (PDMinimal.term M (n+1))
  exact hxy ((hz x).trans (hz y).symm)

lemma minimal_nakayama_differential_noninjective (M : PDMinimal.FiniteModule k R) (n : ℕ)
    [Nontrivial (PDMinimal.term M (n+1))] :
    ¬ Function.Injective (map (k := k) (ModuleCat.ofHom (PDMinimal.differential M n))) := by
  apply nakayama_map_not_injective
  exact minimal_differential_not_split M n

end LittleFinitistic.Nakayama

end

end OAI
