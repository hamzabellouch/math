import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.Tactic.Abel

namespace OAI

namespace PiExponentSiegelAux.W30

variable {R X Y Z W Q : Type*} [CommRing R]
variable [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
variable [AddCommGroup W] [AddCommGroup Q]
variable [Module R X] [Module R Y] [Module R Z] [Module R W] [Module R Q]

def coneDifferential (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z) (r : R) :
    (X × Y) →ₗ[R] (Y × Z) :=
  ((f.comp (LinearMap.fst R X Y)) + r • LinearMap.snd R X Y).prod
    (-(g.comp (LinearMap.snd R X Y)))

@[simp] theorem coneDifferential_apply (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z)
    (r : R) (x : X) (y : Y) :
    coneDifferential f g r (x, y) = (f x + r • y, -g y) := rfl

def coneBottom (g : Y →ₗ[R] Z) (r : R) : (Y × Z) →ₗ[R] Z :=
  g.comp (LinearMap.fst R Y Z) + r • LinearMap.snd R Y Z

@[simp] theorem coneBottom_apply (g : Y →ₗ[R] Z) (r : R) (y : Y) (z : Z) :
    coneBottom g r (y, z) = g y + r • z := rfl

lemma comp_zero_of_range_eq_ker (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z)
    (h : LinearMap.range f = LinearMap.ker g) : g.comp f = 0 := by
  apply LinearMap.ext
  intro x
  change g (f x) = 0
  apply LinearMap.mem_ker.mp
  rw [← h]
  exact LinearMap.mem_range_self f x

theorem coneDifferential_comp (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z)
    (h : Z →ₗ[R] W) (r : R) (hgf : g.comp f = 0) (hhg : h.comp g = 0) :
    (coneDifferential g h r).comp (coneDifferential f g r) = 0 := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · change g (f x.1 + r • x.2) + r • (-g x.2) = 0
    have hz : g (f x.1) = 0 := LinearMap.congr_fun hgf x.1
    simp [map_add, map_smul, hz]
  · change -h (-g x.2) = 0
    have hz : h (g x.2) = 0 := LinearMap.congr_fun hhg x.2
    simp [hz]

theorem coneDifferential_exact (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z)
    (h : Z →ₗ[R] W) (r : R)
    (hfg : LinearMap.range f = LinearMap.ker g)
    (hgh : LinearMap.range g = LinearMap.ker h) :
    LinearMap.range (coneDifferential f g r) =
      LinearMap.ker (coneDifferential g h r) := by
  ext yz
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨xy, rfl⟩
    exact LinearMap.congr_fun
      (coneDifferential_comp f g h r (comp_zero_of_range_eq_ker f g hfg)
        (comp_zero_of_range_eq_ker g h hgh)) xy
  · intro hyz
    have hfirst : g yz.1 + r • yz.2 = 0 := congrArg Prod.fst hyz
    have hsecond : h yz.2 = 0 := by
      have hn : -h yz.2 = 0 := congrArg Prod.snd hyz
      exact neg_eq_zero.mp hn
    have hzrange : yz.2 ∈ LinearMap.range g := by
      rw [hgh]
      exact hsecond
    obtain ⟨t, ht⟩ := LinearMap.mem_range.mp hzrange
    have hcycle : g (yz.1 + r • t) = 0 := by
      simpa only [map_add, map_smul, ht] using hfirst
    have hyrange : yz.1 + r • t ∈ LinearMap.range f := by
      rw [hfg]
      exact hcycle
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hyrange
    refine ⟨(x, -t), ?_⟩
    apply Prod.ext
    · change f x + r • (-t) = yz.1
      rw [hx, smul_neg]
      abel
    · change -g (-t) = yz.2
      simp [ht]

theorem coneBottom_exact (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z)
    (π : Z →ₗ[R] Q) (r : R)
    (hfg : LinearMap.range f = LinearMap.ker g)
    (hgπ : LinearMap.range g = LinearMap.ker π)
    (hr : IsSMulRegular Q r) :
    LinearMap.range (coneDifferential f g r) = LinearMap.ker (coneBottom g r) := by
  ext yz
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨⟨x, y⟩, rfl⟩
    have hz : g (f x) = 0 := LinearMap.congr_fun (comp_zero_of_range_eq_ker f g hfg) x
    change g (f x + r • y) + r • (-g y) = 0
    simp [map_add, map_smul, hz]
  · intro hyz
    have hfirst : g yz.1 + r • yz.2 = 0 := hyz
    have hπg : π (g yz.1) = 0 :=
      LinearMap.congr_fun (comp_zero_of_range_eq_ker g π hgπ) yz.1
    have hrπ : r • π yz.2 = 0 := by
      have heq := congrArg π hfirst
      simpa only [map_add, map_smul, hπg, zero_add, map_zero] using heq
    have hz : π yz.2 = 0 := hr (by simpa only [smul_zero] using hrπ)
    have hzrange : yz.2 ∈ LinearMap.range g := by
      rw [hgπ]
      exact hz
    obtain ⟨t, ht⟩ := LinearMap.mem_range.mp hzrange
    have hcycle : g (yz.1 + r • t) = 0 := by
      simpa only [map_add, map_smul, ht] using hfirst
    have hyrange : yz.1 + r • t ∈ LinearMap.range f := by
      rw [hfg]
      exact hcycle
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hyrange
    refine ⟨(x, -t), ?_⟩
    apply Prod.ext
    · change f x + r • (-t) = yz.1
      rw [hx, smul_neg]
      abel
    · change -g (-t) = yz.2
      simp [ht]

end PiExponentSiegelAux.W30

end OAI
