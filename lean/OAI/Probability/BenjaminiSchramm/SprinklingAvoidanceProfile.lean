import OAI.Probability.BenjaminiSchramm.NormalizedEscapeRisk
import OAI.Probability.BenjaminiSchramm.AvoidanceCostProfile
import OAI.Probability.BenjaminiSchramm.PeakSprinklingCell

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology BigOperators

namespace CriticalPercolation.BondGraph
open BernoulliProduct Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma nonpositive_height_depth (a : V → ℝ) (R : ℝ) (hR : 0 < R) (x u : V)
    (hu : G.orbitAdjustedHeight a x u ≤ 0) :
    G.adjustedLayerIndex a R 0 x u ≤ 0 ∧
      R*(((-G.adjustedLayerIndex a R 0 x u).toNat-1 : ℕ) : ℝ) ≤
        -G.orbitAdjustedHeight a x u := by
  have hf : G.adjustedLayerIndex a R 0 x u ≤ 0 := by
    simpa only [adjustedLayerIndex,add_zero,Int.floor_zero,sub_zero] using
      (Int.floor_mono (div_nonpos_of_nonpos_of_nonneg hu hR.le))
  refine ⟨hf,?_⟩
  let n := (-G.adjustedLayerIndex a R 0 x u).toNat
  change R*((n-1 : ℕ) : ℝ) ≤ -G.orbitAdjustedHeight a x u
  by_cases hn : n=0
  · simpa only [hn,Nat.zero_sub,Nat.cast_zero,mul_zero] using neg_nonneg.mpr hu
  · have hn1 : 1 ≤ n := by omega
    have hd : (n : ℤ)= -G.adjustedLayerIndex a R 0 x u := Int.toNat_of_nonneg (neg_nonneg.mpr hf)
    have hheight := (G.adjustedLayerIndex_height_bounds a R 0 hR x u).2
    have he : (G.adjustedLayerIndex a R 0 x u : ℝ)= -(n : ℝ) := by exact_mod_cast (show G.adjustedLayerIndex a R 0 x u= -(n : ℤ) by omega)
    change G.orbitAdjustedHeight a x u < R*((G.adjustedLayerIndex a R 0 x u : ℝ)+1) at hheight
    rw [he] at hheight
    change R*((n-1 : ℕ) : ℝ) ≤ -G.orbitAdjustedHeight a x u
    rw [Nat.cast_sub hn1,Nat.cast_one]
    nlinarith

variable [Countable V] [Countable E]

theorem sprinkling_avoidance_cost_profile
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (O : G.OrbitRepresentatives) (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x)
    (p q b : unitInterval) (hparam : Percolation.sprinkleParameter q b=p)
    (hb0 : 0 < (b : ℝ)) (hb1 : (b : ℝ) < 1)
    (R : ℝ) (hR : 0 < R) (d : ℕ) (hd : ∀ x, Percolation.degree G.ends x ≤ d)
    (hfin : ∀ x, ∀ᵐ ω ∂G.law p, (G.cluster ω x).Finite) :
    ∃ g : ℕ → ℝ, (∀ l, 0 ≤ g l) ∧ (∃ C : ℝ, ∀ l, g l ≤ C) ∧
      Tendsto g atTop (𝓝 0) ∧ ∀ (x : V) (S : Finset V) (u : V), u ∈ S →
        G.orbitAdjustedHeight a x u ≤ 0 →
        Real.exp (-g (-G.adjustedLayerIndex a R 0 x u).toNat) ≤
          (BernoulliProduct.law (fun e => Percolation.sprinkleParameter
            (erasedWhiteParameters (fun _ => q) (G.incidentEdges (S : Set V)) e) b)).real
              (exteriorEscape G.ends (S : Set V) (G.orbitAdjustedHeight a x) x u)ᶜ := by
  let h : ℕ → ℝ := fun n => G.rootHeightHitProfile O a R p (n-1)
  have hh : ∀ n, 0 ≤ h n := fun n => G.rootHeightHitProfile_nonneg O a R p (n-1)
  have hlim : Tendsto h atTop (𝓝 0) :=
    (G.rootHeightHitProfile_tendsto_zero O a p R hR hfin).comp (tendsto_sub_atTop_nat 1)
  let t : ℝ := min (b : ℝ) (1-b)
  have ht : 0 < t := lt_min hb0 (sub_pos.mpr hb1)
  have ht1 : t ≤ 1 := (min_le_left _ _).trans b.2.2
  let κ : ℝ := t^d
  have hκ : 0 < κ := pow_pos ht _
  have hκ1 : κ ≤ 1 := pow_le_one₀ ht.le ht1
  obtain ⟨g,hg,hgb,hglim,havoid⟩ := exists_vanishing_avoidance_cost h hh O.roots.card
    (fun n => G.rootHeightHitProfile_le_card O a R p (n-1)) hlim κ hκ hκ1
  refine ⟨g,hg,hgb,hglim,?_⟩
  intro x S u hu hxu
  let r : E → unitInterval := fun e => Percolation.sprinkleParameter
    (erasedWhiteParameters (fun _ => q) (G.incidentEdges (S : Set V)) e) b
  let F := Percolation.incidentSupport G.ends hl {u}
  have hF (e : E) (he : u ∈ G.ends e) : e ∈ F :=
    (Percolation.mem_incidentSupport G.ends hl {u} e).mpr ⟨u,Finset.mem_singleton_self u,he⟩
  have hFe (e : E) (he : e ∈ F) : r e=b := by
    obtain ⟨v,hv,hve⟩ := (Percolation.mem_incidentSupport G.ends hl {u} e).mp he
    have hvu : v=u := Finset.mem_singleton.mp hv
    have heQ : e ∈ G.incidentEdges (S : Set V) := ⟨v,hvu ▸ hu,hve⟩
    apply Subtype.ext
    simp only [r,erasedWhiteParameters,ite_eq_left heQ,Percolation.sprinkleParameter,
      Set.Icc.coe_zero,sub_zero,one_mul,zero_add]
  have hcard : F.card ≤ d := by
    simpa only [Finset.card_singleton,one_mul] using
      Percolation.incidentSupport_card_le G.ends hl d hd {u}
  have henergy : κ ≤ (BernoulliProduct.law r).real
      (exteriorEscape G.ends (S : Set V) (G.orbitAdjustedHeight a x) x u)ᶜ := by
    apply (show κ ≤ t^F.card from pow_le_pow_of_le_one ht.le ht1 hcard).trans
    exact exteriorEscape_avoidance_finite_energy G.ends r b (S : Set V)
      (G.orbitAdjustedHeight a x) x u hu F hF hFe
  have hr (e : E) : r e ≤ p := by
    rw [←hparam]
    apply Subtype.coe_le_coe.mp
    have hq' : (erasedWhiteParameters (fun _ => q) (G.incidentEdges (S : Set V)) e : ℝ) ≤ q := by
      unfold erasedWhiteParameters
      split_ifs
      · exact q.2.1
      · rfl
    dsimp [r,Percolation.sprinkleParameter]
    nlinarith [b.2.2]
  have hdepth := G.nonpositive_height_depth a R hR x u hxu
  exact havoid _ _ henergy (G.exteriorEscape_avoidance_profile hc hl O a ha r p hr
    R _ (S : Set V) x u hdepth.2)

end CriticalPercolation.BondGraph

end

end OAI
