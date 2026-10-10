import Mathlib
import OAI.Probability.CriticalPercolation.Gluing.FreshCollar
import OAI.Probability.CriticalPercolation.Gluing.SourceGraph

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

omit [Countable V] [Countable E] in
lemma withSource_edge_cases (A : Set V) (e : E⊕A) (v w : Option V)
    (he : (G.withSource A).ends e=s(v,w)) :
    (∃ b x y, e=Sum.inl b ∧ v=some x ∧ w=some y ∧ G.ends b=s(x,y)) ∨
    (∃ a : A, e=Sum.inr a ∧ ((v=none ∧ w=some a.val) ∨ (w=none ∧ v=some a.val))) := by
  cases e with
  | inl e =>
    obtain ⟨⟨x,y⟩,hxy⟩ := Sym2.mk_surjective (G.ends e)
    change s(x,y)=G.ends e at hxy
    have hh : s(some x,some y)=s(v,w) := by simpa [withSource,← hxy] using he
    rcases Sym2.eq_iff.mp hh with hh|hh
    · exact Or.inl ⟨e,x,y,rfl,hh.1.symm,hh.2.symm,hxy.symm⟩
    · exact Or.inl ⟨e,y,x,rfl,hh.2.symm,hh.1.symm,by simpa only [Sym2.eq_swap] using hxy.symm⟩
  | inr a =>
    right
    refine ⟨a,rfl,?_⟩
    have hh : s(none,some a.val)=s(v,w) := he
    rcases Sym2.eq_iff.mp hh with hh|hh
    · exact Or.inl ⟨hh.1.symm,hh.2.symm⟩
    · exact Or.inr ⟨hh.1.symm,hh.2.symm⟩

theorem withSource_transfer_from_geometry (hlocal : G.LocallyFinite)
    (A Input T : Set V) (hA : A.Finite) (q : (E⊕A) → unitInterval)
    (π : V → ℤ) (H : ℤ) (J : Finset ℤ) (hJ : J.Nonempty)
    (hH : ∀ j∈J, j<H) (hAlevel : ∀ a∈A, H ≤ π a)
    (hInput : ∀ j∈J, ∀ v∈Input, π v<j)
    (hcross : ∀ j∈J, ∀ e v w, G.ends e=s(v,w) → j ≤ π v → π w<j → π v=j)
    (p : unitInterval) (hp : (p : ℝ)<1)
    (hq : ∀ j∈J, ∀ e v w, G.ends e=s(v,w) → π v=j → π w<j → (q (Sum.inl e) : ℝ) ≤ p)
    (D k M N : ℕ) (hD : ∀ j∈J, ∀ v, π v=j → (G.incidentEdges {v}).ncard ≤ D)
    (hM : 0 < M) (hk : M*N ≤ k)
    (C : V → V → Prop) (hrefl : ∀ v, C v v) (hsymm : ∀ {v w}, C v w → C w v)
    (hfinite : ∀ v, {w | C v w}.Finite) (hbound : ∀ v, {w | C v w}.ncard ≤ M)
    (F : ℤ → V → Set E) (B : ℤ → V → Set V)
    (hF : ∀ j∈J, ∀ v, F j v ⊆ (G.inducedEdges {w | j ≤ π w})ᶜ)
    (hconnect : ∀ j∈J, ∀ v, π v=j → ∀ b∈B j v, (G.openGraph (F j v)).Reachable v b)
    (hdis : ∀ j∈J, ∀ v w, ¬C v w → Disjoint (F j v) (F j w))
    (s₀ K η lam : ℝ) (hK : 0 ≤ K) (hη : 0 ≤ η) (hlam : 0 < lam)
    (hs : ∀ j∈J, ∀ v, π v=j → s₀ ≤ (BernoulliProduct.law (fun e => q (Sum.inl e))).real (allOpen (F j v)))
    (hN : K ≤ N*s₀)
    (hmean : ∀ j∈J, ∀ v, π v=j →
      1-η ≤ (BernoulliProduct.law (fun e => q (Sum.inl e))).real (G.seedHitEvent (B j v) T)) :
    (BernoulliProduct.law q).real ((G.withSource A).hitEvent none (some '' Input)\
      (G.withSource A).hitEvent none (some '' T)) ≤
      1/((J.card : ℝ)*(1-(p : ℝ))^(D*k))+Real.exp (-K)+(K+1)*η/lam+lam := by
  let π' : Option V → ℤ := Option.elim' H π
  let C' : Option V → Option V → Prop := fun v w => match v,w with
    | none,none => True
    | some v,some w => C v w
    | _,_ => False
  let F' : ℤ → Option V → Set (E⊕A) := fun j => Option.elim' ∅ (fun v => Sum.inl '' F j v)
  let B' : ℤ → Option V → Set (Option V) := fun j => Option.elim' ∅ (fun v => some '' B j v)
  have hvA (j : ℤ) (hj : j∈J) (v : V) (hv : π v=j) : v∉A := by
    intro hva
    have := hAlevel v hva
    have := hH j hj
    omega
  have hcross' (j : ℤ) (hj : j∈J) (e : E⊕A) (v w : Option V)
      (he : (G.withSource A).ends e=s(v,w)) (hv : j ≤ π' v) (hw : π' w<j) : π' v=j := by
    rcases G.withSource_edge_cases A e v w he with ⟨b,x,y,rfl,rfl,rfl,hb⟩|⟨a,rfl,hh⟩
    · exact hcross j hj b x y hb hv hw
    · obtain hh|hh := hh
      · obtain ⟨rfl,rfl⟩ := hh
        have := hAlevel a a.property
        have := hH j hj
        change π a<j at hw
        omega
      · obtain ⟨rfl,rfl⟩ := hh
        change H<j at hw
        have := hH j hj
        omega
  have hs' (j : ℤ) (hj : j∈J) (v : V) (hv : π v=j) :
      s₀ ≤ (BernoulliProduct.law q).real (allOpen (Sum.inl '' F j v)) := by
    have hm : Measurable (fun ω : Set (E⊕A) => Sum.inl ⁻¹' ω : Set (E⊕A) → Set E) :=
      Measurable.of_eval (fun edge => measurable_set_mem (Sum.inl edge))
    have lawproj := BernoulliProduct.law_map_preimage q Sum.inl Sum.inl_injective
    have heq : allOpen (Sum.inl '' F j v)=(fun ω : Set (E⊕A) => Sum.inl ⁻¹' ω) ⁻¹' allOpen (F j v) := by
      ext ω
      simp only [allOpen,mem_ofPred_eq,mem_preimage]
      exact Set.image_subset_iff
    rw [heq,measureReal_def,← Measure.map_apply hm ((blockSigma_le _) _ (measurable_allOpen_block (F j v))),lawproj]
    exact hs j hj v hv
  apply (G.withSource A).fresh_collar_transfer_from_geometry (G.withSource_local hlocal hA)
    q π' none (some '' Input) (some '' T) J hJ (fun j hj => (hH j hj).le)
    (by rintro j hj _ ⟨v,hv,rfl⟩; exact hInput j hj v hv) hcross' p hp
    (by
      intro j hj e v w he hv hw
      rcases G.withSource_edge_cases A e v w he with ⟨b,x,y,rfl,rfl,rfl,hb⟩|⟨a,rfl,hh⟩
      · exact hq j hj b x y hb hv hw
      · obtain hh|hh := hh
        · obtain ⟨rfl,rfl⟩ := hh
          change H=j at hv
          have := hH j hj
          omega
        · obtain ⟨rfl,rfl⟩ := hh
          change H<j at hw
          have := hH j hj
          omega)
    D k M N
    (by
      intro j hj v hv
      cases v with
      | none => have := hH j hj; change H=j at hv; omega
      | some v =>
        rw [G.withSource_incident A (hvA j hj v hv),Set.ncard_image_of_injective _ Sum.inl_injective]
        exact hD j hj v hv)
    hM hk C'
    (by intro v; cases v; trivial; exact hrefl _)
    (by intro v w h; cases v <;> cases w <;> simp_all only [C'])
    (by
      intro v
      cases v with
      | none =>
        have he : {w | C' none w}={none} := by ext w; cases w <;> simp [C']
        rw [he]
        exact Set.finite_singleton _
      | some v =>
        have he : {w | C' (some v) w}=some '' {w | C v w} := by ext w; cases w <;> simp [C']
        rw [he]
        exact (hfinite v).image _)
    (by
      intro v
      cases v with
      | none =>
        have he : {w | C' none w}={none} := by ext w; cases w <;> simp [C']
        rw [he,Set.ncard_singleton]
        omega
      | some v =>
        have he : {w | C' (some v) w}=some '' {w | C v w} := by ext w; cases w <;> simp [C']
        rw [he,Set.ncard_image_of_injective _ (Option.some_injective V)]
        exact hbound v)
    F' B'
    (by
      intro j hj v
      cases v with
      | none => exact Set.empty_subset _
      | some v =>
        rintro e ⟨b,hb,rfl⟩ he
        apply hF j hj v hb
        intro z hz
        exact he (some z) (by simpa [withSource] using hz))
    (by
      intro j hj v hv b hb
      cases v with
      | none => have := hH j hj; change H=j at hv; omega
      | some v =>
        obtain ⟨z,hz,rfl⟩ := hb
        exact G.withSource_trial_reachable A (F j v) (hconnect j hj v hv z hz))
    (by
      intro j hj v w h
      cases v <;> cases w
      · simp [F']
      · simp [F']
      · simp [F']
      · exact Set.disjoint_image_of_injective Sum.inl_injective (hdis j hj _ _ h))
    s₀ K η lam hK hη hlam
    (by
      intro j hj v hv
      cases v with
      | none => have := hH j hj; change H=j at hv; omega
      | some v => exact hs' j hj v hv)
    hN
    (by
      intro j hj v hv
      cases v with
      | none => have := hH j hj; change H=j at hv; omega
      | some v => exact (hmean j hj v hv).trans (G.withSource_seedHit A (B j v) T q))

end CriticalPercolation.BondGraph
end
end
end

end OAI
