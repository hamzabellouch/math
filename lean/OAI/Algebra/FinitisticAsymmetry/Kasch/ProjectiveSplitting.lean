import Mathlib
import OAI.Algebra.FinitisticAsymmetry.Kasch.Radical

namespace OAI

section
section
noncomputable section
open CategoryTheory
namespace LittleFinitistic
universe u
variable (A : Type u) [Ring A]
namespace Kasch
universe v w
variable {R : Type u} [Ring R]
section SplitBasic
variable {k : Type u} [Field k] [Algebra k R]
variable {ι : Type u} (χ : R →ₐ[k] (ι → k))
variable (a : ι → R) (ha : ∀ i, a i ≠ 0)
  (hmul : ∀ i r, a i * r = χ r i • a i)

include hmul in
lemma annihilates_radical {P : Type v} [AddCommGroup P] [Module R P]
    {x : P} (hx : x ∈ radicalPart (RingHom.ker χ.toRingHom) P) (i : ι) : a i • x = 0 := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr y hy
    rw [← mul_smul, hmul]
    have h : χ r = 0 := hr
    simp [h]
  · intro x y hx hy
    simp only [smul_add, hx, hy, add_zero]

include ha hmul in
lemma finsupp_mem_radical_of_annihilated {σ : Type v} (x : σ →₀ R)
    (hx : ∀ i, a i • x = 0) : x ∈ radicalPart (RingHom.ker χ.toRingHom) (σ →₀ R) := by
  classical
  have hcoef (s : σ) : χ (x s) = 0 := by
    ext i
    have hi : a i * x s = 0 := congrArg (fun y : σ →₀ R => y s) (hx i)
    rw [hmul] at hi
    exact (smul_eq_zero.mp hi).resolve_right (ha i)
  rw [← Finsupp.sum_single x]
  apply Submodule.sum_mem
  intro s hs
  have heq : Finsupp.single s (x s) = x s • Finsupp.single s (1 : R) := by simp
  rw [heq]
  exact Submodule.smul_mem_smul (hcoef s) (Submodule.mem_top)

include ha hmul in
lemma projective_mem_radical_iff {P : Type v} [AddCommGroup P] [Module R P]
    [Module.Projective R P] (x : P) :
    x ∈ radicalPart (RingHom.ker χ.toRingHom) P ↔ ∀ i, a i • x = 0 := by
  constructor
  · exact fun hx i => annihilates_radical χ a hmul hx i
  · intro hx
    obtain ⟨s, hs⟩ := (Module.projective_def' (R := R) (P := P)).mp inferInstance
    have hx' : s x ∈ radicalPart (RingHom.ker χ.toRingHom) (P →₀ R) :=
      finsupp_mem_radical_of_annihilated χ a ha hmul (s x) (fun i => by
        rw [← s.map_smul, hx i, map_zero])
    have he : (Finsupp.linearCombination R id) (s x) = x := DFunLike.congr_fun hs x
    rw [← he]
    exact map_radical_le (RingHom.ker χ.toRingHom) (Finsupp.linearCombination R id)
      (Submodule.mem_map_of_mem hx')

include ha hmul in
lemma projective_mono_reflects_radical {P : Type v} {Q : Type w}
    [AddCommGroup P] [Module R P] [Module.Projective R P]
    [AddCommGroup Q] [Module R Q]
    (f : P →ₗ[R] Q) (hf : Function.Injective f) {x : P}
    (hx : f x ∈ radicalPart (RingHom.ker χ.toRingHom) Q) :
    x ∈ radicalPart (RingHom.ker χ.toRingHom) P := by
  rw [projective_mem_radical_iff χ a ha hmul]
  intro i
  apply hf
  rw [map_smul, map_zero]
  exact annihilates_radical χ a hmul hx i

include ha hmul in
lemma projective_mono_splits [Finite ι]
    (hχ : Function.Surjective χ) (hJ : ∃ n : ℕ, (RingHom.ker χ.toRingHom) ^ n = ⊥)
    {P : Type v} {Q : Type w} [AddCommGroup P] [Module R P] [Module.Projective R P]
    [AddCommGroup Q] [Module R Q] [Module.Projective R Q]
    (f : P →ₗ[R] Q) (hf : Function.Injective f) :
    ∃ g : Q →ₗ[R] P, g.comp f = LinearMap.id := by
  let J := RingHom.ker χ.toRingHom
  let p := radicalPart J P
  let q := radicalPart J Q
  let fbar : P ⧸ p →ₗ[R] Q ⧸ q := p.mapQ q f
    (Submodule.map_le_iff_le_comap.mp (map_radical_le J f))
  have hfbar : Function.Injective fbar := by
    apply LinearMap.ker_eq_bot.mp
    apply le_bot_iff.mp
    intro x hx
    obtain ⟨x, rfl⟩ := p.mkQ_surjective x
    have hx' : f x ∈ q := (Submodule.Quotient.mk_eq_zero q).mp hx
    exact (Submodule.Quotient.mk_eq_zero p).mpr
      (projective_mono_reflects_radical χ a ha hmul f hf hx')
  let : IsSemisimpleModule R (Q ⧸ q) := top_semisimple χ.toRingHom hχ Q
  obtain ⟨gbar, hgbar⟩ := IsSemisimpleModule.extension_property fbar hfbar
    (LinearMap.id : P ⧸ p →ₗ[R] P ⧸ p)
  obtain ⟨g, hg⟩ := Module.projective_lifting_property p.mkQ (gbar.comp q.mkQ)
    p.mkQ_surjective
  have hnil : IsNilpotent (1 - g.comp f : Module.End R P) := by
    apply isNilpotent_of_range_le_radical J hJ
    rintro _ ⟨x, rfl⟩
    apply (Submodule.Quotient.mk_eq_zero p).mp
    change p.mkQ (x - g (f x)) = 0
    rw [map_sub]
    have hg' := DFunLike.congr_fun hg (f x)
    have hgbar' := DFunLike.congr_fun hgbar (p.mkQ x)
    change p.mkQ (g (f x)) = gbar (q.mkQ (f x)) at hg'
    change gbar (q.mkQ (f x)) = p.mkQ x at hgbar'
    rw [hg', hgbar', sub_self]
  have hu : IsUnit (g.comp f) := by simpa using hnil.isUnit_one_sub
  obtain ⟨u, hu⟩ := hu.exists_left_inv
  refine ⟨u.comp g, ?_⟩
  simpa only [Module.End.mul_eq_comp, Module.End.one_eq_id, LinearMap.comp_assoc] using hu

end SplitBasic
end Kasch
end LittleFinitistic
end
end
end

end OAI
