import OAI.Probability.BenjaminiSchramm.PeakOrbitComparison

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem full_peak_lower_slab_comparison
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x)
    (d N : ℕ) (hd : ∀ z, Percolation.degree G.ends z ≤ d)
    (p : unitInterval) (R M k r ell : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hk : 0 ≤ k) (hr : 0 ≤ r) (hell : 0 < ell)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e → |G.orbitAdjustedHeight a v w| ≤ R)
    (hpaths : ∀ u (j : G.VertexOrbit), ∃ v, ∃ q : G.fullGraph.Walk u v,
      G.vertexOrbit v=j ∧ q.length ≤ N ∧
      (∀ z ∈ q.support, -M ≤ G.orbitAdjustedHeight a u z ∧ G.orbitAdjustedHeight a u z ≤ 0) ∧
      G.orbitAdjustedHeight a u v ≤ -R)
    (hfin : ∀ v, ∀ᵐ ω ∂G.law p, (Percolation.cluster G.ends ω v).Finite)
    (x v₀ : V) :
    (G.law p (G.fullPeakDownHit a ell x))*
      ENNReal.ofReal ((min (p : ℝ) (1-p))^(d*(N+1)))*
        G.mixedHeightLayerMoment a p (-k-r) 0 (-k-R) (-k+R) (-k-r-2*M-2*R) ell v₀ ≤
      ∫⁻ ω, G.strictPeakSlabBandCount a (r+R+M) (-ell-k-M-2*R) (-ell-k) ω x ∂G.law p := by
  let f := G.orbitAdjustedHeight a x
  let D := Percolation.internalEdges G.ends {z | -ell-k-r-2*M-3*R ≤ f z}
  let D' := Percolation.internalEdges G.ends {z | -ell-k-r-R-M ≤ f z}
  let K := D \ Percolation.internalEdges G.ends {z | f z ≤ -ell}
  let J := Percolation.internalEdges G.ends {z | -ell-k-r-R-M ≤ f z ∧ f z ≤ -ell}
  let U : Set V := {z | -ell-R ≤ f z ∧ f z ≤ -ell}
  let T : Set V := {z | z ≠ x ∧ 0 ≤ f z}
  let W : Set V := {z | -ell-k-M-2*R ≤ f z ∧ f z ≤ -ell-k}
  let b := ENNReal.ofReal ((min (p : ℝ) (1-p))^(d*(N+1)))*
    G.mixedHeightLayerMoment a p (-k-r) 0 (-k-R) (-k+R) (-k-r-2*M-2*R) ell v₀
  have hj : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e → |f w-f v| ≤ R := by
    intro e v w hv hw
    dsimp [f]
    rw [G.orbitAdjustedHeight_change_base hc hl a x v w,add_sub_cancel_left]
    exact hjump e v w hv hw
  have hD'D : D' ⊆ D := Percolation.internalEdges_mono G.ends (by
    intro z hz
    change -ell-k-r-R-M ≤ f z at hz
    change -ell-k-r-2*M-3*R ≤ f z
    linarith)
  have hJD' : J ⊆ D' := Percolation.internalEdges_mono G.ends (fun _ hz => hz.1)
  have hKD' : K ⊆ D' := upper_mask_lower_bound G.ends f R (-ell) _ hj D (by linarith)
  have hJK : Disjoint J K := Set.disjoint_left.mpr (by
    intro e heJ heK
    exact heK.2 (fun z hz => (heJ z hz).2))
  have hfinD : ∀ v, ∀ᵐ ω ∂G.law p, (Percolation.cluster G.ends (ω ∩ D) v).Finite := by
    intro v
    filter_upwards [hfin v] with ω hω
    exact hω.subset fun z hz => Percolation.conn_mono G.ends Set.inter_subset_left hz
  have hbound : ∀ u ∈ U, b ≤
      ∑' w, if w ∈ W then G.law p (connectionAvoidingHit G.ends D J u w T) else 0 := by
    intro u hu
    exact G.mixedHeight_continuation_at_boundary hc hl a ha d N hd p R M k r ell hR hM
      hk hr hell x u v₀ hu (hpaths u (G.vertexOrbit v₀))
  have hcmp := peak_layer_comparison_averaged_in_domain G.ends p D D' K J
    Set.sdiff_subset (hJD'.trans hD'D) hJK hKD' hJD' x U T W b hfinD (by
      intro u hu
      refine (hbound u hu).trans_eq ?_
      apply tsum_congr
      intro w
      split_ifs <;> rfl)
  have hsub : G.fullPeakDownHit a ell x ⊆
      (restrictedHit G.ends D x T)ᶜ ∩ restrictedHit G.ends K x U :=
    G.fullPeakDownHit_subset_exposed hc hl a R M k r ell hR hM hk hr hell hjump x
  have hdEq : (-ell-k-M-2*R)-(r+R+M)= -ell-k-r-2*M-3*R := by ring
  have hcEq : (-ell-k)-(r+R+M)= -ell-k-r-R-M := by ring
  have heq (ω : Set E) : G.strictPeakSlabBandCount a (r+R+M) (-ell-k-M-2*R) (-ell-k) ω x =
      (restrictedHit G.ends D x T)ᶜ.indicator
        (fun ω => restrictedLayerCount G.ends D' W ω x) ω := by
    simpa only [hdEq,hcEq] using G.strict_peak_slab_band_count_eq a (r+R+M)
      (-ell-k-M-2*R) (-ell-k) (by linarith) ω x
  calc
    _ = G.law p (G.fullPeakDownHit a ell x)*b := by dsimp [b]; rw [mul_assoc]
    _ ≤ G.law p ((restrictedHit G.ends D x T)ᶜ ∩ restrictedHit G.ends K x U)*b :=
      mul_le_mul' (measure_mono hsub) le_rfl
    _ ≤ ∫⁻ ω, (restrictedHit G.ends D x T)ᶜ.indicator
        (fun ω => restrictedLayerCount G.ends D' W ω x) ω ∂G.law p := hcmp
    _ = _ := lintegral_congr fun ω => (heq ω).symm

end CriticalPercolation.BondGraph

end

end OAI
