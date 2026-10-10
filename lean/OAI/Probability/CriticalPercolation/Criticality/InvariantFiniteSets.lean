import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.AutDisplacement
import OAI.Probability.CriticalPercolation.GraphGeometry.GraphBalls
import OAI.Probability.CriticalPercolation.GraphGeometry.OpenGraphIso

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma vertex_aut_orbit_infinite [Infinite V] (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive) (v : V) :
    (Set.range (fun φ : G.Aut => φ.vertex v)).Infinite := by
  intro hf
  obtain ⟨R,hR⟩ := G.finite_subset_vertexBall hc v hf
  obtain ⟨φ,hφ⟩ := G.aut_moves_vertex_outside_ball hc hl hq v R
  exact hφ (hR ⟨φ,rfl⟩)

lemma bounded_invariant_marks_null [Infinite V] [Countable V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (M : Set E → V → Prop)
    (hm : ∀ v, Measurable (fun ω => M ω v))
    (ha : ∀ (φ : G.Aut) ω v, M (φ.edge '' ω) (φ.vertex v) ↔ M ω v)
    (N : ℕ) (hb : ∀ ω, ∃ S : Finset V, S.card≤N ∧ ∀ v, M ω v → v∈S) (v : V) :
    G.law p {ω | M ω v}=0 := by
  have hmeas (x : V) : Measurable (fun ω => if M ω x then (1:ℝ≥0∞) else 0) :=
    measurable_const.ite (hm x).setOf measurable_const
  have he (x : V) : (∫⁻ ω, if M ω x then (1:ℝ≥0∞) else 0 ∂G.law p) =
      G.law p {ω | M ω x} := by
    simpa only [Set.indicator,Pi.one_apply,Set.mem_ofPred_eq] using
      (lintegral_indicator_one (μ := G.law p) (hm x).setOf)
  have hpoint (ω : Set E) : (∑' x, if M ω x then (1:ℝ≥0∞) else 0) ≤ N := by
    obtain ⟨S,hS,hcover⟩ := hb ω
    calc
      _ ≤ ∑' x, if x∈S then (1:ℝ≥0∞) else 0 := by
        apply ENNReal.tsum_le_tsum
        intro x
        split_ifs with hx hs
        · rfl
        · exact False.elim (hs (hcover x hx))
        · exact zero_le
        · rfl
      _ = (S.card:ℝ≥0∞) := by
        rw [tsum_eq_sum (s := S) (fun x hx => ite_eq_right hx)]
        simp
      _ ≤ N := by exact_mod_cast hS
  have hsum : (∑' x, G.law p {ω | M ω x}) ≤ N := by
    calc
      _ = ∫⁻ ω, ∑' x, if M ω x then (1:ℝ≥0∞) else 0 ∂G.law p := by
        rw [lintegral_tsum (fun x => (hmeas x).aemeasurable)]
        simp only [he]
      _ ≤ ∫⁻ _ : Set E, (N:ℝ≥0∞) ∂G.law p := lintegral_mono hpoint
      _ = N := by simp
  have hinv (φ : G.Aut) : G.law p {ω | M ω (φ.vertex v)} = G.law p {ω | M ω v} := by
    conv_lhs => rw [←G.law_map_aut p φ]
    rw [Measure.map_apply (BernoulliProduct.measurable_image_equiv φ.edge) (hm _).setOf]
    congr 1
    ext ω
    exact ha φ ω v
  by_contra hn
  have hf := ENNReal.finite_const_le_of_tsum_ne_top
    ((hsum.trans_lt (ENNReal.natCast_lt_top N)).ne) hn
  apply G.vertex_aut_orbit_infinite hc hl hq v
  apply hf.subset
  rintro x ⟨φ,rfl⟩
  change G.law p {ω | M ω v} ≤ G.law p {ω | M ω (φ.vertex v)}
  rw [hinv]

def vertexSetBound (_G : BondGraph V E) (A : Set E → Set V) (N : ℕ) (ω : Set E) : Prop :=
  ∃ S : Finset V, S.card≤N ∧ A ω ⊆ S

lemma measurable_vertexSetBound [Countable V] (A : Set E → Set V)
    (hm : ∀ v, Measurable (fun ω => v∈A ω)) (N : ℕ) :
    Measurable (G.vertexSetBound A N) := by
  exact .exists fun S : Finset V => measurable_const.and
    (.forall fun v => (hm v).imp measurable_const)

lemma vertexSetBound_aut (A : Set E → Set V)
    (ha : ∀ (φ : G.Aut) ω, A (φ.edge '' ω)=φ.vertex '' A ω)
    (N : ℕ) (φ : G.Aut) (ω : Set E) :
    G.vertexSetBound A N (φ.edge '' ω) ↔ G.vertexSetBound A N ω := by
  change (∃ S : Finset V, S.card≤N ∧ A (φ.edge '' ω)⊆S) ↔ _
  rw [ha]
  constructor
  · rintro ⟨S,hS,h⟩
    refine ⟨S.image φ.vertex.symm,Finset.card_image_le.trans hS,?_⟩
    intro x hx
    exact Finset.mem_image.mpr ⟨φ.vertex x,h ⟨x,hx,rfl⟩,φ.vertex.symm_apply_apply x⟩
  · rintro ⟨S,hS,h⟩
    refine ⟨S.image φ.vertex,Finset.card_image_le.trans hS,?_⟩
    rintro y ⟨x,hx,rfl⟩
    exact Finset.mem_image.mpr ⟨x,h hx,rfl⟩

theorem invariant_finite_vertex_set_empty_ae [Infinite V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (A : Set E → Set V)
    (hm : ∀ v, Measurable (fun ω => v∈A ω))
    (ha : ∀ (φ : G.Aut) ω, A (φ.edge '' ω)=φ.vertex '' A ω) :
    ∀ᵐ ω ∂G.law p, (A ω).Finite → A ω=∅ := by
  let := G.countable_vertices hc hl
  have hn (N : ℕ) (v : V) : ∀ᵐ ω ∂G.law p, ¬(G.vertexSetBound A N ω ∧ v∈A ω) := by
    rw [ae_iff]
    simp only [not_not]
    apply G.bounded_invariant_marks_null hc hl hq p
      (fun ω v => G.vertexSetBound A N ω ∧ v∈A ω)
      (fun v => (G.measurable_vertexSetBound A hm N).and (hm v))
      (fun φ ω v => by
        rw [G.vertexSetBound_aut A ha N φ ω,ha]
        simp only [Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right]) N
    intro ω
    by_cases hh : G.vertexSetBound A N ω
    · obtain ⟨S,hS,hcover⟩ := hh
      exact ⟨S,hS,fun x hx => hcover hx.2⟩
    · exact ⟨∅,Nat.zero_le N,fun x hx => (hh hx.1).elim⟩
  have hall : ∀ᵐ ω ∂G.law p, ∀ N : ℕ, ∀ v : V,
      ¬(G.vertexSetBound A N ω ∧ v∈A ω) :=
    ae_all_iff.mpr (fun N => ae_all_iff.mpr (hn N))
  filter_upwards [hall] with ω hω hf
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro v hv
  exact hω hf.toFinset.card v ⟨⟨hf.toFinset,le_rfl,fun _ hx => hf.mem_toFinset.mpr hx⟩,hv⟩

end CriticalPercolation.BondGraph
end
end

end OAI
