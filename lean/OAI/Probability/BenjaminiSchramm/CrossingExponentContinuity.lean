import OAI.Probability.BenjaminiSchramm.CrossingPositivity

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma infimalAdjustedCrossing_lower_parameter [Countable E] [Nonempty V]
    (hq : G.QuasiTransitive) (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x) = a x)
    (p : unitInterval) (hp : 0 < p) (t c : ℝ) (hc : 0 ≤ c)
    (hlt : c < (G.infimalAdjustedCrossing a p t).toReal) :
    ∃ q : unitInterval, (p : ℝ)/2 ≤ q ∧ q < p ∧ c < (G.infimalAdjustedCrossing a q t).toReal := by
  let d := (c+(G.infimalAdjustedCrossing a p t).toReal)/2
  have hcd : c < d := by dsimp [d]; linarith
  have hdp : d < (G.infimalAdjustedCrossing a p t).toReal := by dsimp [d]; linarith
  obtain ⟨S,hS,hcover⟩ := hq
  let : Finite S := hS.to_subtype
  have hroot (x : V) : d < (G.law p).real (G.adjustedHalfspaceHit a x 0 t) :=
    hdp.trans_le (ENNReal.toReal_mono (measure_ne_top _ _)
      (iInf_le (fun y => G.law p (G.adjustedHalfspaceHit a y 0 t)) x))
  obtain ⟨q,hhalf,hqp,hqroot⟩ := BernoulliProduct.exists_lower_parameter
    (fun x : S => G.adjustedHalfspaceHit a x 0 t) (fun x => G.adjustedHalfspaceHit_upper a x 0 t)
    (fun x => G.adjustedHalfspaceHit_hasFiniteOpenWitness a x 0 t) p hp (fun _ => d)
    (fun x => by simpa only [BernoulliProduct.law_const,law] using hroot x)
  refine ⟨q,hhalf,hqp,hcd.trans_le ?_⟩
  have he : ENNReal.ofReal d ≤ G.infimalAdjustedCrossing a q t := by
    apply le_iInf
    intro x
    obtain ⟨o,ho,φ,rfl⟩ := hcover x
    rw [Aut.adjustedHalfspaceHit_measure G a ha φ]
    have hr := hqroot ⟨o,ho⟩
    rw [BernoulliProduct.law_const] at hr
    exact ENNReal.ofReal_le_of_le_toReal hr.le
  have hf := ENNReal.toReal_mono
    (ne_top_of_le_ne_top ENNReal.one_ne_top (G.infimalAdjustedCrossing_le_one a q t)) he
  rwa [ENNReal.toReal_ofReal (hc.trans hcd.le)] at hf

theorem normalized_crossing_exponent_approximation [Fintype G.VertexOrbit] [Nontrivial V]
    [Encodable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep (G.orbitWalkKernel hl) μ = μ) (hu : ¬ G.CombinatoriallyUnimodular)
    (p : unitInterval) (hp : 0 < p) (α : ℝ)
    (hlim : Tendsto (fun n : ℕ => -Real.log
      (G.infimalAdjustedCrossing (G.stationaryOrbitWeight μ) p n).toReal/n) atTop (𝓝 α))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ q : unitInterval, (p : ℝ)/2 ≤ q ∧ q < p ∧ ∃ β : ℝ, 0 ≤ β ∧ β < α+ε ∧
      (∀ n : ℕ, (G.infimalAdjustedCrossing (G.stationaryOrbitWeight μ) q n).toReal ≤ Real.exp (-β*n)) ∧
      (∀ δ : ℝ, 0 < δ → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
        c*Real.exp (-(β+δ)*n) ≤ (G.infimalAdjustedCrossing (G.stationaryOrbitWeight μ) q n).toReal) := by
  let a := G.stationaryOrbitWeight μ
  obtain ⟨A,B,_hA,_hB,hpos⟩ := G.infimalAdjustedCrossing_finite_energy hc hl hq μ hμ hstat hu p hp
  obtain ⟨n,hn,hsl⟩ := ((eventually_ge_atTop (1 : ℕ)).and
    (hlim.eventually (gt_mem_nhds (lt_add_of_pos_right α hε)))).exists
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hPn : 0 < (G.infimalAdjustedCrossing a p n).toReal :=
    (Real.rpow_pos_of_pos hp _).trans_le (hpos n (Nat.cast_nonneg n))
  have hlog : -(α+ε)*(n : ℝ) < Real.log (G.infimalAdjustedCrossing a p n).toReal := by
    have hh := (div_lt_iff₀ hnpos).mp hsl
    linarith
  have he := Real.exp_lt_exp.mpr hlog
  rw [Real.exp_log hPn] at he
  obtain ⟨q,hhalf,hqp,hqprob⟩ := G.infimalAdjustedCrossing_lower_parameter hq a
    (G.stationaryOrbitWeight_aut μ) p hp n (Real.exp (-(α+ε)*n)) (Real.exp_pos _).le he
  have hqpos : (0 : ℝ) < q := (half_pos (show (0 : ℝ) < p from hp)).trans_le hhalf
  obtain ⟨β,hβ,hβupper,hβlower,_hβlim⟩ := G.normalized_crossing_exponent hc hl hq μ hμ hstat hu q hqpos
  refine ⟨q,hhalf,hqp,β,hβ,?_,hβupper,hβlower⟩
  have hle := Real.exp_lt_exp.mp (hqprob.trans_le (hβupper n))
  nlinarith

end CriticalPercolation.BondGraph

end

end OAI
