import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.MeasurableSetRestrict
import OAI.Probability.CriticalPercolation.GraphGeometry.GraphBalls
import OAI.Probability.CriticalPercolation.GraphGeometry.FiniteInduced

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma event_eq_restrict_of_dependsOn (A : Set (Set E)) (F : Set E)
    (hA : DependsOn (fun ω : Set E => ω∈A) F) :
    A={ω | F∩ω∈A} := by
  ext ω
  exact (hA (x := ω) (y := (show Set E from F∩ω)) (fun e he =>
    propext (show e∈ω ↔ e∈F∩ω from by simp [he]))).to_iff

lemma measurableSet_of_finite_dependsOn (A : Set (Set E)) (F : Set E) (hF : F.Finite)
    (hA : DependsOn (fun ω : Set E => ω∈A) F) : MeasurableSet A := by
  rw [event_eq_restrict_of_dependsOn A F hA]
  exact measurableSet_restrict F hF A

lemma eventually_uniform_finite_events (p : unitInterval) (F : Set E) (hF : F.Finite)
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ q in 𝓝 p, ∀ A : Set (Set E), DependsOn (fun ω : Set E => ω∈A) F →
      |(law (fun _ : E => q)).real A-(law (fun _ : E => p)).real A|<ε := by
  let := hF.fintype
  have hh : ∀ᶠ q in 𝓝 p, ∀ B : Set (Set F),
      |(law (fun _ : F => q)).real B-(law (fun _ : F => p)).real B|<ε := by
    apply Filter.eventually_all.mpr
    intro B
    have hc : ContinuousAt (fun q : unitInterval =>
        |(law (fun _ : F => q)).real B-(law (fun _ : F => p)).real B|) p :=
      ((continuous_real_law_finite B).sub continuous_const).abs.continuousAt
    exact hc.eventually (gt_mem_nhds (by simpa using hε))
  filter_upwards [hh] with q hq
  intro A hA
  have he (t : unitInterval) : (law (fun _ : E => t)).real A=
      (law (fun _ : F => t)).real {s : Set F | Subtype.val '' s∈A} := by
    conv_lhs => rw [event_eq_restrict_of_dependsOn A F hA]
    exact real_law_restrict t F hF A
  rw [he q,he p]
  exact hq _

end CriticalPercolation.BernoulliProduct
namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)
open BernoulliProduct

lemma Aut.incidentEdges_image (φ : G.Aut) (S : Set V) :
    φ.edge '' G.incidentEdges S=G.incidentEdges (φ.vertex '' S) := by
  ext e
  obtain ⟨f,rfl⟩ := φ.edge.surjective e
  simp only [Set.mem_image,φ.edge.injective.eq_iff,exists_eq_right]
  constructor
  · rintro ⟨v,hv,hve⟩
    exact ⟨φ.vertex v,⟨v,hv,rfl⟩,by rw [φ.preserves]; exact Sym2.mem_map.mpr ⟨v,hve,rfl⟩⟩
  · rintro ⟨u,⟨v,hv,rfl⟩,hue⟩
    refine ⟨v,hv,?_⟩
    rw [φ.preserves] at hue
    obtain ⟨w,hw,heq⟩ := Sym2.mem_map.mp hue
    simpa only [φ.vertex.injective heq] using hw

lemma dependsOn_preimage_aut (φ : G.Aut) (A : Set (Set E)) (F : Set E)
    (hA : DependsOn (fun ω : Set E => ω∈A) (φ.edge '' F)) :
    DependsOn (fun ω : Set E => φ.edge '' ω∈A) F := by
  intro ω η h
  apply hA
  rintro e ⟨f,hf,rfl⟩
  apply propext
  change φ.edge f∈φ.edge '' ω ↔ φ.edge f∈φ.edge '' η
  constructor
  · rintro ⟨a,ha,heq⟩
    have heq' : a=f := φ.edge.injective heq
    subst a
    exact ⟨f,(h f hf).to_iff.mp ha,rfl⟩
  · rintro ⟨a,ha,heq⟩
    have heq' : a=f := φ.edge.injective heq
    subst a
    exact ⟨f,(h f hf).to_iff.mpr ha,rfl⟩

lemma eventually_uniform_local_events
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive) (p : unitInterval)
    (B : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ q in 𝓝 p, ∀ v : V, ∀ A : Set (Set E),
      DependsOn (fun ω : Set E => ω∈A) (G.incidentEdges (G.vertexBall v B)) →
      |(G.law q).real A-(G.law p).real A|<ε := by
  obtain ⟨S,hS,horbit⟩ := hq
  have hh : ∀ᶠ q in 𝓝 p, ∀ v∈S, ∀ A : Set (Set E),
      DependsOn (fun ω : Set E => ω∈A) (G.incidentEdges (G.vertexBall v B)) →
      |(G.law q).real A-(G.law p).real A|<ε := by
    apply hS.eventually_all.mpr
    intro v hv
    simpa only [law,←law_const] using eventually_uniform_finite_events p
      (G.incidentEdges (G.vertexBall v B)) (G.finite_incident hl (G.vertexBall_finite hl v B)) ε hε
  filter_upwards [hh] with q hq
  intro v A hA
  obtain ⟨s,hs,φ,rfl⟩ := horbit v
  let A' : Set (Set E) := (fun ω : Set E => φ.edge '' ω) ⁻¹' A
  have hA' : DependsOn (fun ω : Set E => ω∈A') (G.incidentEdges (G.vertexBall s B)) := by
    apply G.dependsOn_preimage_aut φ
    simpa only [Aut.incidentEdges_image,Aut.vertexBall_image] using hA
  have hmeas : MeasurableSet A := measurableSet_of_finite_dependsOn A _
    (G.finite_incident hl (G.vertexBall_finite hl _ B)) hA
  have he (t : unitInterval) : (G.law t).real A=(G.law t).real A' := by
    simp only [Measure.real]
    conv_lhs => rw [←G.law_map_aut t φ,Measure.map_apply (measurable_image_equiv φ.edge) hmeas]
  rw [he q,he p]
  exact hq s hs A' hA'

end CriticalPercolation.BondGraph
end
end

end OAI
