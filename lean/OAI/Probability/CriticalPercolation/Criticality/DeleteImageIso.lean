import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.InfiniteEscapeLowerBound

namespace OAI

section
section CurrentModule9
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
open ClusterDeletion

variable {V E : Type*} (G : BondGraph V E)

lemma measurableSet_boundary (hl : G.LocallyFinite)
    (o : V) (S : Set V) (hS : S.Finite) (e : E) :
    MeasurableSet {ω | boundaryReach G Sᶜ (delete (G.openGraph ω) Sᶜ) o e} := by
  let K := G.incidentEdges S
  have hK : K.Finite := finite_incident G hl hS
  let := hK.fintype
  have hm : Measurable (fun ω : Set E => (Subtype.val ⁻¹' ω : Set K)) :=
    Measurable.of_eval (fun edge => measurable_set_mem edge.val)
  have he : {ω | boundaryReach G Sᶜ (delete (G.openGraph ω) Sᶜ) o e} =
      (fun ω : Set E => (Subtype.val ⁻¹' ω : Set K)) ⁻¹'
        {η | boundaryReach G Sᶜ
          (delete ((G.restrictEdges K).openGraph η) Sᶜ) o e} := by
    ext ω
    simp only [Set.mem_preimage,Set.mem_ofPred_eq,G.restrictEdges_openGraph,
      delete_restrict_incident G (K := K) Subset.rfl]
  rw [he]
  exact hm (.of_discrete)

noncomputable def deleteImageIso (φ : G.Aut) (ω : Set E) (S : Set V) :
    delete (G.openGraph ω) S ≃g delete (G.openGraph (φ.edge '' ω)) (φ.vertex '' S) where
  toEquiv := φ.vertex
  map_rel_iff' := by
    intro x y
    change ((G.openGraph (φ.edge '' ω)).Adj (φ.vertex x) (φ.vertex y) ∧
      φ.vertex x ∉ φ.vertex '' S ∧ φ.vertex y ∉ φ.vertex '' S) ↔ _
    simp only [BondGraph.Aut.adj_map,Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right]
    rfl

lemma boundary_image (φ : G.Aut) (S : Set V) (o : V) (e : E) (ω : Set E) :
    boundaryReach G (φ.vertex '' S)ᶜ
      (delete (G.openGraph (φ.edge '' ω)) (φ.vertex '' S)ᶜ) (φ.vertex o) (φ.edge e) ↔
      boundaryReach G Sᶜ (delete (G.openGraph ω) Sᶜ) o e := by
  have himg : (φ.vertex '' S)ᶜ = φ.vertex '' Sᶜ := by
    ext v
    obtain ⟨x,rfl⟩ := φ.vertex.surjective v
    simp only [Set.mem_compl_iff,Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right]
  rw [himg]
  constructor
  · rintro ⟨a,b,he,ha,hb,hr⟩
    obtain ⟨x,rfl⟩ := φ.vertex.surjective a
    obtain ⟨y,rfl⟩ := φ.vertex.surjective b
    have hx : x ∉ Sᶜ := by simpa only [Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right] using ha
    have hy : y ∈ Sᶜ := by simpa only [Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right] using hb
    rw [φ.preserves,← Sym2.map_mk] at he
    exact ⟨x,y,Sym2.map.injective φ.vertex.injective he,hx,hy,
      (SimpleGraph.Iso.reachable_iff (φ := deleteImageIso G φ ω Sᶜ)).mp hr⟩
  · rintro ⟨x,y,he,hx,hy,hr⟩
    refine ⟨φ.vertex x,φ.vertex y,?_,?_,?_,?_⟩
    · rw [φ.preserves,he,Sym2.map_mk]
    · simpa only [Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right] using hx
    · exact ⟨y,hy,rfl⟩
    · exact (SimpleGraph.Iso.reachable_iff (φ := deleteImageIso G φ ω Sᶜ)).mpr hr

lemma boundary_real_image (hl : G.LocallyFinite) (φ : G.Aut) (p : unitInterval)
    (S : Set V) (hS : S.Finite) (o : V) (e : E) :
    (G.law p).real {ω | boundaryReach G (φ.vertex '' S)ᶜ
      (delete (G.openGraph ω) (φ.vertex '' S)ᶜ) (φ.vertex o) (φ.edge e)} =
    (G.law p).real {ω | boundaryReach G Sᶜ (delete (G.openGraph ω) Sᶜ) o e} := by
  change (G.law p _).toReal = (G.law p _).toReal
  congr 1
  calc
    _ = (G.law p).map (fun ω : Set E => φ.edge '' ω)
        {ω | boundaryReach G (φ.vertex '' S)ᶜ
          (delete (G.openGraph ω) (φ.vertex '' S)ᶜ) (φ.vertex o) (φ.edge e)} := by
      rw [G.law_map_aut p φ]
    _ = _ := by
      rw [Measure.map_apply (BernoulliProduct.measurable_image_equiv φ.edge)
        (measurableSet_boundary G hl _ _ (hS.image _) _)]
      congr 1
      ext ω
      exact boundary_image G φ S o e ω

lemma phi_image (hl : G.LocallyFinite) (φ : G.Aut) (p : unitInterval)
    (S : Set V) (hS : S.Finite) (o : V) :
    phi G p (φ.vertex o) (φ.vertex '' S) = phi G p o S := by
  unfold phi
  congr 1
  rw [← φ.edge.tsum_eq]
  apply tsum_congr
  intro e
  exact boundary_real_image G hl φ p S hS o e

theorem uniform_subcritical_domains [Countable V] [Countable E] [Nonempty V]
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (hp : p < G.criticalProbability) :
    ∃ N : ℕ, ∃ a : ℝ, a < 1 ∧ ∀ o : V,
      ∃ S : Set V, S.Finite ∧ o ∈ S ∧ S.ncard ≤ N ∧ phi G p o S ≤ a := by
  obtain ⟨R,hR,horbit⟩ := hq
  have hne : R.Nonempty := by
    obtain ⟨v⟩ := ‹Nonempty V›
    obtain ⟨r,hr,_⟩ := horbit v
    exact ⟨r,hr⟩
  choose D hD hoD hphi using subcritical_finite_size G hl p hp
  obtain ⟨r,hr,hmax⟩ := Set.exists_max_image R (fun o => phi G p o (D o)) hR hne
  let N := ∑ o ∈ hR.toFinset, (D o).ncard
  refine ⟨N,phi G p r (D r),hphi r,?_⟩
  intro o
  obtain ⟨s,hs,φ,rfl⟩ := horbit o
  refine ⟨φ.vertex '' D s,(hD s).image _,⟨s,hoD s,rfl⟩,?_,?_⟩
  · rw [Set.ncard_image_of_injective _ φ.vertex.injective]
    exact Finset.single_le_sum (f := fun o => (D o).ncard)
      (fun _ _ => Nat.zero_le _) (hR.mem_toFinset.mpr hs)
  · rw [phi_image G hl φ p (D s) (hD s) s]
    exact hmax s hs

end CriticalPercolation.Sharpness
end
end CurrentModule9

end

end OAI
