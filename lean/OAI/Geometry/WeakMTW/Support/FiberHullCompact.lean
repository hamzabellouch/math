import Mathlib
import OAI.Geometry.WeakMTW.Support.ConvexRepresentation

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set
open scoped BigOperators
namespace ConvexRepresentation
noncomputable section
variable {B E : Type*} [TopologicalSpace B] [T2Space B]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

 def fiberHull (K : Set (B × E)) : Set (B × E) :=
    {q | q.2 ∈ convexHull ℝ {v | (q.1,v) ∈ K}}

 theorem fiberHull_compact {K : Set (B × E)} (hK : IsCompact K) :
    IsCompact (fiberHull K) := by
  classical
  let N := Module.finrank ℝ E + 1
  let i₀ : Fin N := ⟨0,Nat.zero_lt_succ _⟩
  let simplex : Set (Fin N → ℝ) :=
    {weights | (∀ index, 0 ≤ weights index) ∧ ∑ index, weights index = 1}
  have simplex_compact : IsCompact simplex := by
    simpa only [simplex, Convexity.StdSimplex.range_toFun_comp_weights,
      Set.ofPred_and, Set.ofPred_forall] using
      isCompact_range (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin N)).continuous
  let D : Set ((Fin N → ℝ) × (Fin N → B × E)) :=
    (simplex ×ˢ {z | ∀ i, z i ∈ K}) ∩ {q | ∀ i, (q.2 i).1 = (q.2 i₀).1}
  let F : ((Fin N → ℝ) × (Fin N → B × E)) → B × E :=
    fun q => ((q.2 i₀).1,∑ i, q.1 i • (q.2 i).2)
  have hD : IsCompact D := by
    apply (simplex_compact.prod (isCompact_pi_infinite (fun _ : Fin N => hK))).inter_right
    have hc (i : Fin N) : Continuous (fun q : (Fin N → ℝ) × (Fin N → B × E) => (q.2 i).1) :=
      ((continuous_apply i).comp continuous_snd).fst
    simpa only [Set.ofPred_forall] using isClosed_iInter (fun i => isClosed_eq (hc i) (hc i₀))
  have hF : Continuous F := by
    apply Continuous.prodMk
    · exact ((continuous_apply i₀).comp continuous_snd).fst
    · exact continuous_finsetSum Finset.univ (fun i _ =>
        ((continuous_apply i).comp continuous_fst).smul
          (((continuous_apply i).comp continuous_snd).snd))
  have heq : F '' D = fiberHull K := by
    ext q
    constructor
    · rintro ⟨⟨w,z⟩,⟨⟨hw,hz⟩,hbase⟩,rfl⟩
      change (∑ i, w i • (z i).2) ∈ convexHull ℝ {v | ((z i₀).1,v) ∈ K}
      apply (convex_convexHull ℝ _).sum_mem
      · intro i _
        exact hw.1 i
      · exact hw.2
      · intro i _
        apply subset_convexHull
        have hi : z i ∈ K := hz i
        change ((z i₀).1,(z i).2) ∈ K
        rw [← hbase i]
        exact hi
    · intro hq
      obtain ⟨z,w,hz,hw,hws,hwz⟩ := fixed_size hq (le_refl (Module.finrank ℝ E+1))
      refine ⟨(w,fun i => (q.1,z i)),⟨⟨⟨hw,hws⟩,?_⟩,?_⟩,?_⟩
      · intro i
        exact hz i
      · intro i
        rfl
      · exact Prod.ext rfl hwz
  rw [← heq]
  exact hD.image hF

 theorem convexHull_compact {S : Set E} (hS : IsCompact S) : IsCompact (convexHull ℝ S) := by
  have hK : IsCompact (({()} : Set Unit) ×ˢ S) := isCompact_singleton.prod hS
  have hh := (fiberHull_compact hK).image continuous_snd
  convert hh using 1
  ext x
  simp only [mem_image,fiberHull,mem_ofPred_eq,mem_prod,mem_singleton_iff]
  constructor
  · intro hx
    exact ⟨((),x),by simpa using hx,rfl⟩
  · rintro ⟨⟨u,v⟩,hv,rfl⟩
    simpa using hv

end
end ConvexRepresentation
end

end WeakMTWGlobalSupport

end OAI
