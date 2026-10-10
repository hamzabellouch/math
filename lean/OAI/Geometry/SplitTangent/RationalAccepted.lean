import Mathlib
import OAI.Geometry.SplitTangent.RationalFamilies
import OAI.Geometry.SplitTangent.Basic

namespace OAI

/-! Rational Accepted. -/

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold

universe u
namespace SplitTangent.RationalParameters
open AnalyticZeroCover

variable {X : ComplexManifold.{u}} (e : ProjectiveEmbedding X) [CompactSpace X.Carrier]

 

lemma analyticSetOn_incidenceAlternative {m : ℕ} {U : Set (Space m)} (hU : IsOpen U)
    {Q : Space m → Fin (e.N+1) → ℂ} (hQ : AnalyticOnNhd ℂ Q U)
    (hnz : ∀ z∈U, Q z≠0) :
    AnalyticSetOn U {z | z∈U ∧ ∃ x, e.Incidence x (Q z)} where
  subset := fun _ h => h.1
  closed := by
    intro z hz
    refine ⟨hz.2,?_⟩
    change Q z ∈ {v | ∃ x, e.Incidence x v}
    rw [← e.isClosed_cone.closure_eq]
    exact (closure_mono (show Q '' {z | z∈U ∧ ∃ x, e.Incidence x (Q z)} ⊆
        {v | ∃ x, e.Incidence x v} from by rintro _ ⟨y,hy,rfl⟩; exact hy.2)
        (mem_closure_image (hQ z hz.2).continuousAt hz.1))
  local_equations := by
    intro z hz
    obtain ⟨D,hD,hDeq⟩ := e.cone_local_equations_any (hnz z hz.1)
    have hcomp : AnalyticAt ℂ (D ∘ Q) z := hD.comp (hQ z hz.1)
    have heq := (hQ z hz.1).continuousAt.eventually hDeq
    obtain ⟨V,hV,hVo,hVz⟩ := eventually_nhds_iff.mp
      (Filter.Eventually.and (hU.mem_nhds hz.1) (hcomp.eventually_analyticAt.and heq))
    let f : Fin (e.N+1) → Space m → ℂ := fun i y => D (Q y) i
    refine ⟨V,hVo,hVz,fun y hy => (hV y hy).1,Set.range f,?_,?_⟩
    · rintro g ⟨i,rfl⟩ y hy
      exact ((ContinuousLinearMap.proj i).analyticAt _).comp (hV y hy).2.1
    · intro y hy
      simp only [mem_ofPred_eq,forall_mem_range]
      have hyU : y∈U := (hV y hy).1
      simp only [hyU,true_and]
      rw [(hV y hy).2.2]
      exact ⟨fun h i => congrFun h i,fun h => funext h⟩

lemma accepted_test {d : ℕ} (P : Patch (Coeff e.N d))
    (hPM : P.image ⊆ regular e.N d) (hPA : ¬P.image ⊆ accepted e d) :
    ∃ B : Set (Space P.dim), AnalyticSetOn P.domain B ∧
      (∃ x∈P.domain, x∉B) ∧ {x | x∈P.domain ∧ P.map x∈accepted e d} ⊆ B := by
  classical
  obtain ⟨τ,hτ,hτA⟩ := Set.not_subset.mp hPA
  obtain ⟨x,hx,rfl⟩ := hτ
  have hn : ∃ b : Bool, ∃ z : ℂ, ¬∃ y, e.Incidence y (ev b (P.map x) z) := by
    simpa only [accepted,mem_ofPred_eq,not_forall] using hτA
  obtain ⟨b,z,hbad⟩ := hn
  let Q : Space P.dim → (Fin (e.N+1) → ℂ) := fun y => ev b (P.map y) z
  have hQ : AnalyticOnNhd ℂ Q P.domain := fun y hy =>
    AnalyticAt.comp (f := fun y => (z,P.map y)) (x := y) (ev_analytic b (z,P.map y))
      (analyticAt_const.prod (P.analytic y hy))
  refine ⟨{y | y∈P.domain ∧ ∃ q, e.Incidence q (Q y)},
    analyticSetOn_incidenceAlternative e P.isOpen_domain hQ
      (fun y hy => regular_nonzero (hPM ⟨y,hy,rfl⟩) b z),?_,?_⟩
  · exact ⟨x,hx,fun h => hbad h.2⟩
  · intro y hy
    exact ⟨hy.1,hy.2 b z⟩

 

theorem countable_accepted {d : ℕ} :
    ∃ C : Set (Patch (Coeff e.N d)), C.Countable ∧
      (∀ P∈C, P.image ⊆ regular e.N d ∩ accepted e d) ∧
      regular e.N d ∩ accepted e d ⊆ ⋃ P∈C,P.image := by
  classical
  obtain ⟨D,hD,hDdim,hcover⟩ := countable_open_patches (isOpen_regular e.N d)
  have H (i : D) := i.val.countable_accepted_cover (accepted_test e) (hDdim i.val i.property).2
  choose C hC hCp hCc using H
  let : Countable D := hD.to_subtype
  refine ⟨⋃ i,C i,Set.countable_iUnion hC,?_,?_⟩
  · intro P hP
    obtain ⟨i,hi⟩ := mem_iUnion.mp hP
    exact (hCp i P hi).2
  · intro τ hτ
    obtain ⟨P,hP,hτP⟩ := mem_iUnion₂.mp (hcover hτ.1)
    obtain ⟨Q,hQ,hτQ⟩ := mem_iUnion₂.mp (hCc ⟨P,hP⟩ ⟨hτP,hτ.2⟩)
    exact mem_iUnion₂.mpr ⟨Q,mem_iUnion.mpr ⟨⟨P,hP⟩,hQ⟩,hτQ⟩

end SplitTangent.RationalParameters

end

end OAI
