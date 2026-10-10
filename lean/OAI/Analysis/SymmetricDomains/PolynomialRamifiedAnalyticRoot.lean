import Mathlib
import OAI.Analysis.SymmetricDomains.FiniteCoveringRamifiedSection
import OAI.Analysis.SymmetricDomains.PolynomialRootFiberFinite

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Filter Set Complex UpperHalfPlane Function
open scoped Topology
instance : T2Space PuncturedUnitDisk := inferInstanceAs (T2Space {z : ℂ // z ≠ 0 ∧ ‖z‖ < 1})

theorem polynomial_ramified_continuous_root {d : ℕ} {S : Type*}
    [TopologicalSpace S] [T2Space S] [ContractibleSpace S] [LocallyPathConnectedSpace S]
    (P : Polynomial (MvPolynomial (Fin d) ℂ)) (A : S × PuncturedUnitDisk → (Fin d → ℂ))
    (hA : Continuous A)
    (hlead : ∀ x, MvPolynomial.eval (A x) P.leadingCoeff ≠ 0)
    (hsep : ∀ x, (P.map (MvPolynomial.eval (A x))).Separable)
    (s₀ : S) (z₀ : ℍ) (b₀ : ℂ)
    (hb : Polynomial.eval₂ (MvPolynomial.eval (A (s₀,halfPlaneQ 1 one_pos z₀))) b₀ P = 0) :
    ∃ l : ℕ, ∃ hl : 0 < l, ∃ g : S × PuncturedUnitDisk → ℂ,
      Continuous g ∧
      (∀ s q, Polynomial.eval₂ (MvPolynomial.eval (A (s,puncturedPower l hl q))) (g (s,q)) P = 0) ∧
      g (s₀,halfPlaneQ l (by exact_mod_cast hl) z₀) = b₀ := by
  let R := {r : (S × PuncturedUnitDisk) × ℂ | Polynomial.eval₂ (MvPolynomial.eval (A r.1)) r.2 P = 0}
  let p : R → S × PuncturedUnitDisk := fun r => r.val.1
  let e₀ : R := ⟨((s₀,halfPlaneQ 1 one_pos z₀),b₀),hb⟩
  obtain ⟨l,hl,G,hGc,hpG,hG₀⟩ := finite_covering_ramified_section p
    (polynomial_root_covering P A hA hlead hsep) s₀ z₀ e₀ rfl
    (polynomial_root_fiber_finite P A _ (hlead _))
  refine ⟨l,hl,fun x => (G x).val.2,continuous_snd.comp (continuous_subtype_val.comp hGc),?_,?_⟩
  · intro s q
    have h := (G (s,q)).property
    change Polynomial.eval₂ (MvPolynomial.eval (A (p (G (s,q))))) ((G (s,q)).val.2) P = 0 at h
    rwa [hpG] at h
  · exact congrArg (fun r : R => r.val.2) hG₀

theorem simple_root_analytic_extension {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (P : Polynomial (MvPolynomial (Fin d) ℂ)) (A : E → (Fin d → ℂ))
    (Ω : Set E) (hΩ : IsOpen Ω) (hA : AnalyticOnNhd ℂ A Ω)
    (g : Ω → ℂ) (hg : Continuous g)
    (hroot : ∀ x, Polynomial.eval₂ (MvPolynomial.eval (A x.val)) (g x) P = 0)
    (hsimple : ∀ x, Polynomial.eval₂ (MvPolynomial.eval (A x.val)) (g x) P.derivative ≠ 0) :
    ∃ G : E → ℂ, AnalyticOnNhd ℂ G Ω ∧ ∀ x : Ω, G x.val = g x := by
  classical
  let G := Function.extend (Subtype.val : Ω → E) g (fun _ => 0)
  have hG (x : Ω) : G x.val = g x := Subtype.val_injective.extend_apply _ _ _
  have hGc : ContinuousOn G Ω := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    convert hg using 1
    funext x
    exact hG x
  refine ⟨G,?_,hG⟩
  intro x hx
  apply continuous_polynomial_root_analyticAt P A G x (hA x hx) (hGc.continuousAt (hΩ.mem_nhds hx))
  · filter_upwards [hΩ.mem_nhds hx] with y hy
    simpa only [hG ⟨y,hy⟩] using hroot ⟨y,hy⟩
  · simpa only [hG ⟨x,hx⟩] using hsimple ⟨x,hx⟩

theorem polynomial_ramified_analytic_root {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (P : Polynomial (MvPolynomial (Fin d) ℂ)) (A : E × ℂ → (Fin d → ℂ))
    (S : Set E) (hS : IsOpen S) [ContractibleSpace S] [LocallyPathConnectedSpace S]
    (hA : AnalyticOnNhd ℂ A (S ×ˢ {q : ℂ | q ≠ 0 ∧ ‖q‖ < 1}))
    (hlead : ∀ x ∈ S ×ˢ {q : ℂ | q ≠ 0 ∧ ‖q‖ < 1},
      MvPolynomial.eval (A x) P.leadingCoeff ≠ 0)
    (hsep : ∀ x ∈ S ×ˢ {q : ℂ | q ≠ 0 ∧ ‖q‖ < 1},
      (P.map (MvPolynomial.eval (A x))).Separable)
    (s₀ : S) (z₀ : ℍ) (b₀ : ℂ)
    (hb : Polynomial.eval₂ (MvPolynomial.eval (A (s₀.val,(halfPlaneQ 1 one_pos z₀).val))) b₀ P = 0) :
    ∃ l : ℕ, ∃ hl : 0 < l, ∃ G : E × ℂ → ℂ,
      AnalyticOnNhd ℂ G (S ×ˢ {q : ℂ | q ≠ 0 ∧ ‖q‖ < 1}) ∧
      (∀ x ∈ S ×ˢ {q : ℂ | q ≠ 0 ∧ ‖q‖ < 1},
        Polynomial.eval₂ (MvPolynomial.eval (A (x.1,x.2^l))) (G x) P = 0) ∧
      G (s₀.val,(halfPlaneQ l (by exact_mod_cast hl) z₀).val) = b₀ := by
  let Ω : Set (E × ℂ) := S ×ˢ {q : ℂ | q ≠ 0 ∧ ‖q‖ < 1}
  let α : S × PuncturedUnitDisk → E × ℂ := fun x => (x.1.val,x.2.val)
  have hαc : Continuous α :=
    (continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)
  have hα : ∀ x, α x ∈ Ω := fun x => ⟨x.1.property,x.2.property⟩
  have hAc : Continuous (A ∘ α) := hA.continuousOn.comp_continuous hαc hα
  obtain ⟨l,hl,g,hgc,hgr,hg₀⟩ := polynomial_ramified_continuous_root P (A ∘ α) hAc
    (fun x => hlead (α x) (hα x)) (fun x => hsep (α x) (hα x)) s₀ z₀ b₀ hb
  let ψ : Ω ≃ₜ S × PuncturedUnitDisk := Homeomorph.Set.prod S _
  let K : E × ℂ → E × ℂ := fun x => (x.1,x.2^l)
  have hK : AnalyticOnNhd ℂ K Set.univ := fun x _ => analyticAt_fst.prod (analyticAt_snd.pow l)
  have hKΩ (x : E × ℂ) (hx : x ∈ Ω) : K x ∈ Ω :=
    ⟨hx.1,pow_ne_zero l hx.2.1,by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) hx.2.2 hl.ne'⟩
  have hAK : AnalyticOnNhd ℂ (A ∘ K) Ω := fun x hx =>
    (hA (K x) (hKΩ x hx)).comp (hK x (mem_univ _))
  have hrg (x : Ω) : Polynomial.eval₂ (MvPolynomial.eval ((A ∘ K) x.val)) (g (ψ x)) P = 0 :=
    hgr (ψ x).1 (ψ x).2
  have hsg (x : Ω) : Polynomial.eval₂ (MvPolynomial.eval ((A ∘ K) x.val)) (g (ψ x)) P.derivative ≠ 0 := by
    have hh := (hsep (K x.val) (hKΩ x.val x.property)).eval₂_derivative_ne_zero
      (RingHom.id ℂ) (x := g (ψ x))
    simpa only [Polynomial.eval₂_id,Polynomial.eval₂_at_apply,Polynomial.derivative_map,
      Polynomial.eval_map,Function.comp_def] using hh (by
        simpa only [Polynomial.eval₂_id,Polynomial.eval₂_at_apply,Polynomial.eval_map,Function.comp_def] using hrg x)
  have hΩ : IsOpen Ω := hS.prod (isOpen_ne_fun continuous_id continuous_const |>.inter
    (isOpen_lt (continuous_norm) continuous_const))
  obtain ⟨G,hGa,hGg⟩ := simple_root_analytic_extension P (A ∘ K) Ω hΩ hAK
    (g ∘ ψ) (hgc.comp ψ.continuous) hrg hsg
  refine ⟨l,hl,G,hGa,?_,?_⟩
  · intro x hx
    rw [hGg ⟨x,hx⟩]
    exact hrg ⟨x,hx⟩
  · rw [hGg ⟨(s₀.val,(halfPlaneQ l (by exact_mod_cast hl) z₀).val),s₀.property,
      (halfPlaneQ l (by exact_mod_cast hl) z₀).property⟩]
    exact hg₀

end Release061

end

end OAI
