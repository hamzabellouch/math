import OAI.Analysis.BernoulliCone.SeamHeight

namespace OAI

universe uE uG

section
noncomputable section
open Set Filter
open scoped Topology ContDiff Manifold
namespace Bernoulli.LocalExtension
variable {E : Type uE} {G : Type uG} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
/-- C1 germs agreeing on a closed subset glue to a global C1 extension.
This is an application of the actual smooth partition of unity, not a Whitney
extension premise. -/
lemma exists_contDiff_one_of_closed_germs {S:Set E} (hS:IsClosed S) {F:E→G}
    (hg:∀x∈S,∃B:E→G,ContDiffAt ℝ 1 B x ∧ ∀ᶠ y in 𝓝 x,y∈S→B y=F y) :
    ∃B:E→G,ContDiff ℝ 1 B ∧ EqOn B F S := by
  classical
  let t:E→Set G:=fun x=>if x∈S then {F x} else univ
  have ht(x:E):Convex ℝ (t x):=by
    by_cases hx:x∈S
    · simpa only [t,ite_eq_left hx] using convex_singleton (F x)
    · simpa only [t,ite_eq_right hx] using (convex_univ : Convex ℝ (univ:Set G))
  have hl(x:E):∃U∈𝓝 x,∃g:E→G,ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,G) 1 g U ∧
      ∀y∈U,g y∈t y := by
    by_cases hx:x∈S
    · obtain ⟨g,hgc,hge⟩:=hg x hx
      obtain ⟨V,hV,hgV⟩:=hgc.contDiffOn le_rfl (by norm_num)
      refine ⟨V∩{y|y∈S → g y=F y},inter_mem hV hge,g,?_,?_⟩
      · exact (hgV.mono inter_subset_left).contMDiffOn
      · intro y hy
        by_cases hyS:y∈S
        · simp only [t,ite_eq_left hyS,mem_singleton_iff]
          exact hy.2 hyS
        · simp only [t,ite_eq_right hyS,mem_univ]
    · refine ⟨Sᶜ,hS.isOpen_compl.mem_nhds hx,fun _=>0,contMDiffOn_const,?_⟩
      intro y hy
      simp only [t,ite_eq_right hy,mem_univ]
  obtain ⟨B,hB⟩:=exists_contMDiffMap_forall_mem_convex_of_local 𝓘(ℝ,E) ht hl
  refine ⟨B,B.contMDiff.contDiff,?_⟩
  intro x hx
  simpa only [t,ite_eq_left hx,mem_singleton_iff] using hB x
end Bernoulli.LocalExtension

end
end

end OAI
