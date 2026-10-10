import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.GraphBalls
import OAI.Probability.CriticalPercolation.Gluing.CorridorNormalization
import OAI.Probability.CriticalPercolation.Gluing.MoveWitness

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma boxMove_aut_subset (t z : V → ℝ) (m : ℕ) (q B : ℝ) (o : V) (s : ℝ)
    (φ : G.Aut) (ht : ∀ x y, t (φ.vertex x)-t (φ.vertex y)=t x-t y)
    (hz : ∀ x y, z (φ.vertex x)-z (φ.vertex y)=z x-z y) :
    G.boxMove t z m q B o s ⊆ (fun ω => φ.edge '' ω) ⁻¹'
      G.boxMove t z m q B (φ.vertex o) s := by
  rintro ω ⟨a,ha,b,w,hw,hbt,hbz⟩
  let w' := w.map (Aut.openGraphIso G φ ω).toHom
  refine ⟨φ.vertex a,(Aut.vertexBall_mem G φ o a m).mpr ha,φ.vertex b,w',?_,?_,?_⟩
  · intro x hx
    change x∈(w.map (Aut.openGraphIso G φ ω).toHom).support at hx
    rw [SimpleGraph.Walk.support_map] at hx
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    change |t (φ.vertex v)-t (φ.vertex o)|≤B ∧ |z (φ.vertex v)-z (φ.vertex o)|≤B
    rw [ht,hz]
    exact hw v hv
  · have h : t (φ.vertex b)-(t (φ.vertex o)+1)=t b-(t o+1) := by linarith [ht b o]
    rwa [h]
  · have h : z (φ.vertex b)-(z (φ.vertex o)+s)=z b-(z o+s) := by linarith [hz b o]
    rwa [h]

lemma boxMove_aut_probability [Countable V] [Countable E]
    (t z : V → ℝ) (m : ℕ) (q B : ℝ) (o : V) (s : ℝ) (p : unitInterval)
    (φ : G.Aut) (ht : ∀ x y, t (φ.vertex x)-t (φ.vertex y)=t x-t y)
    (hz : ∀ x y, z (φ.vertex x)-z (φ.vertex y)=z x-z y) :
    (G.law p).real (G.boxMove t z m q B o s) ≤
      (G.law p).real (G.boxMove t z m q B (φ.vertex o) s) := by
  have hm : G.law p (G.boxMove t z m q B o s) ≤
      G.law p (G.boxMove t z m q B (φ.vertex o) s) := by
    conv_rhs => rw [← G.law_map_aut p φ]
    rw [Measure.map_apply (BernoulliProduct.measurable_image_equiv φ.edge)
      (G.boxMove_measurable _ _ _ _ _ _ _)]
    exact measure_mono (G.boxMove_aut_subset t z m q B o s φ ht hz)
  exact ENNReal.toReal_mono (measure_ne_top _ _) hm

lemma boxMove_close_center (t z : V → ℝ) (m c : ℕ) (e s : ℝ) (he : e<1/10)
    {x y : V} (hxy : x∈G.vertexBall y c)
    (ht : |t x-t y|≤e/8) (hz : |z x-z y|≤e/8) :
    G.boxMove t z m (e/8) 30 x s ⊆ G.coordinateMove t z (m+c) e y s := by
  rintro ω ⟨a,ha,b,w,hw,hbt,hbz⟩
  refine ⟨a,?_,b,w,?_,?_,?_⟩
  · simpa only [Nat.add_comm c m] using G.vertexBall_add hxy m ha
  · intro v hv
    have hvb := hw v hv
    constructor
    · have := abs_sub_le (t v) (t x) (t y)
      linarith [hvb.1]
    · have := abs_sub_le (z v) (z x) (z y)
      linarith [hvb.2]
  · have hh := abs_sub_le (t b) (t x+1) (t y+1)
    rw [add_sub_add_right_eq_sub] at hh
    linarith
  · have hh := abs_sub_le (z b) (z x+s) (z y+s)
    rw [add_sub_add_right_eq_sub] at hh
    linarith

theorem uniform_moves_of_origin [Countable V] [Countable E]
    (t z : V → ℝ) (o : V) (m c : ℕ) (e eta rho : ℝ)
    (he : e<1/10) (hrho : 0≤rho) (hmesh : c*rho≤e/8)
    (ht : ∀ ⦃x y⦄, G.fullGraph.Adj x y → |t x-t y|≤rho)
    (hz : ∀ ⦃x y⦄, G.fullGraph.Adj x y → |z x-z y|≤rho)
    (hdense : ∀ y, ∃ φ : G.Aut, φ.vertex o∈G.vertexBall y c ∧
      (∀ x y, t (φ.vertex x)-t (φ.vertex y)=t x-t y) ∧
      (∀ x y, z (φ.vertex x)-z (φ.vertex y)=z x-z y))
    (pc : unitInterval) (hpc : 0<pc)
    (horigin : ∀ b : Bool, 1-eta<(BernoulliProduct.law (fun _ : E => pc)).real
      (G.boxMove t z m (e/8) 30 o (Corridor.sign b))) :
    ∃ p : unitInterval, (pc : ℝ)/2≤p ∧ p<pc ∧ ∀ y s, |s|=1 →
      1-eta≤(BernoulliProduct.law (fun _ : E => p)).real
        (G.coordinateMove t z (m+c) e y s) := by
  obtain ⟨p,hpl,hpu,hp⟩ := G.lower_two_boxMoves t z m (e/8) 30 o pc hpc eta horigin
  refine ⟨p,hpl,hpu,?_⟩
  intro y s hs
  obtain ⟨b,hb⟩ : ∃ b : Bool, Corridor.sign b=s := by
    rcases (abs_eq (by norm_num : (0 : ℝ)≤1)).mp hs with h|h
    · exact ⟨true,by simpa [Corridor.sign] using h.symm⟩
    · exact ⟨false,by simpa [Corridor.sign] using h.symm⟩
  obtain ⟨φ,hφ,hφt,hφz⟩ := hdense y
  have htt := (G.coordinate_ball_bound t rho hrho ht hφ).trans hmesh
  have hzz := (G.coordinate_ball_bound z rho hrho hz hφ).trans hmesh
  have hsub := G.boxMove_close_center t z m c e s he hφ htt hzz
  have hm : (G.law p).real (G.boxMove t z m (e/8) 30 (φ.vertex o) s)≤
      (G.law p).real (G.coordinateMove t z (m+c) e y s) :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
  have hp' := hp b
  rw [hb] at hp'
  have hp'' : 1-eta≤(G.law p).real (G.boxMove t z m (e/8) 30 o s) := by
    simpa only [law,BernoulliProduct.law_const] using hp'.le
  simpa only [law,BernoulliProduct.law_const] using
    hp''.trans ((G.boxMove_aut_probability t z m (e/8) 30 o s p φ hφt hφz).trans hm)

end CriticalPercolation.BondGraph
end
end
end

end OAI
