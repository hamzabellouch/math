import OAI.Algebra.AuslanderReiten.Complete.CompleteResolution
import OAI.Algebra.AuslanderReiten.Basic
import Mathlib.RingTheory.Finiteness.Finsupp

namespace OAI

noncomputable section
namespace ArExplicit
universe u v w x y
variable {R : Type u} [Ring R]
variable {K : Type v} [AddCommGroup K] [Module R K]
variable {L : Type w} [AddCommGroup L] [Module R L]
variable {M : Type x} [AddCommGroup M] [Module R M]
variable {Q : Type y} [AddCommGroup Q] [Module R Q]

theorem HomExactAt.arbitrary_projective [Module.Finite R L] [Module.Projective R Q]
    {e : K →ₗ[R] L} {d : L →ₗ[R] M} (h : HomExactAt e d)
    (f : L →ₗ[R] Q) (hf : f.comp e = 0) :
    ∃ g : M →ₗ[R] Q, g.comp d = f := by
  classical
  obtain ⟨s,hs⟩ := Module.projective_def'.mp (inferInstance : Module.Projective R Q)
  obtain ⟨c,hc⟩ := (LinearMap.finsuppLinearMap_bijective_of_moduleFinite
    R L R Q ℤ).surjective (s.comp f)
  have he (q : Q) : (c q).comp e = 0 := by
    ext z
    have hh := congrArg (fun F : L →ₗ[R] (Q →₀ R) => F (e z) q) hc
    change (c q) (e z) = (s (f (e z))) q at hh
    rw [show f (e z) = 0 from DFunLike.congr_fun hf z, map_zero] at hh
    exact hh
  choose g hg using fun q => h (c q) (he q)
  let G : M →ₗ[R] (Q →₀ R) := ∑ q ∈ c.support, (Finsupp.lsingle q).comp (g q)
  have hG : G.comp d = s.comp f := by
    ext z q
    have hh := congrArg (fun F : L →ₗ[R] (Q →₀ R) => F z q) hc
    change (c q) z = (s (f z)) q at hh
    change G (d z) q = (s (f z)) q
    rw [← hh]
    change (∑ j ∈ c.support, (Finsupp.lsingle j).comp (g j)) (d z) q = (c q) z
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, Finsupp.finsetSum_apply]
    have hg' (j : Q) : g j (d z) = (c j) z := DFunLike.congr_fun (hg j) z
    simp only [hg', Finsupp.lsingle_apply]
    rw [Finset.sum_eq_single q]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · intro hq
      have hcz : c q = 0 := Finsupp.notMem_support_iff.mp hq
      simp [hcz]
  refine ⟨(Finsupp.linearCombination R id).comp G, ?_⟩
  rw [LinearMap.comp_assoc, hG, ← LinearMap.comp_assoc, hs, LinearMap.id_comp]

def GorensteinProjectiveAllTargets (R : Type u) [Ring R]
    (M : Type v) [AddCommGroup M] [Module R M] : Prop :=
  ∃ P : ChainComplex (ModuleCat.{max u v} R) ℤ,
    (∀ n : ℤ, Module.Finite R (P.X n) ∧ Module.Projective R (P.X n)) ∧
    (∀ n : ℤ, LinearMap.range (P.d (n+1) n).hom = LinearMap.ker (P.d n (n-1)).hom) ∧
    (∀ (Q : Type y) [AddCommGroup Q] [Module R Q] [Module.Projective R Q]
      (n : ℤ) (f : P.X n →ₗ[R] Q), f.comp (P.d (n+1) n).hom = 0 →
        ∃ g : P.X (n-1) →ₗ[R] Q, f = g.comp (P.d n (n-1)).hom) ∧
    Nonempty (M ≃ₗ[R] (P.X 0 ⧸ LinearMap.range (P.d 1 0).hom))

theorem GorensteinProjective.all_projective_targets
    {M : Type v} [AddCommGroup M] [Module R M]
    (h : GorensteinProjective R M) : GorensteinProjectiveAllTargets.{u,v,y} R M := by
  obtain ⟨P,hP,he,hd,hi⟩ := h
  refine ⟨P,hP,he,?_,hi⟩
  intro Q _ _ _ n f hf
  let := (hP n).1
  have hn : HomExactAt (P.d (n+1) n).hom (P.d n (n-1)).hom := by
    intro f hf
    obtain ⟨g,hg⟩ := hd n f hf
    exact ⟨g,hg.symm⟩
  obtain ⟨g,hg⟩ := hn.arbitrary_projective f hf
  exact ⟨g,hg.symm⟩

theorem gorensteinProjective_iff_all_projective_targets
    {M : Type v} [AddCommGroup M] [Module R M] :
    GorensteinProjective R M ↔ GorensteinProjectiveAllTargets.{u,v,u} R M := by
  refine ⟨GorensteinProjective.all_projective_targets, ?_⟩
  rintro ⟨P,hP,he,hd,hi⟩
  exact ⟨P,hP,he,hd R,hi⟩

end ArExplicit

end

end OAI
