import OAI.Probability.BenjaminiSchramm.CeilingBandUniform
import OAI.Probability.BenjaminiSchramm.LayerFirstMomentRate

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma adjustedBandCount_aut (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x) (l u : ℝ)
    (φ : G.Aut) (ω : Set E) (x : V) :
    G.adjustedBandCount a l u (φ.edge '' ω) (φ.vertex x) =
      G.adjustedBandCount a l u ω x := by
  unfold adjustedBandCount
  rw [←φ.vertex.tsum_eq]
  simp only [G.adjustedBandTransport_aut a ha l u]

lemma upLayerCount_le_bandCount (a : V → ℝ) (R : ℝ) (hR : 0 < R)
    (n : ℕ) (x : V) (u : ℝ) (ω : Set E) :
    restrictedLayerCount G.ends
      (Percolation.internalEdges G.ends {v | G.adjustedLayerIndex a R u x v ≤ (n : ℤ)})
      {v | G.adjustedLayerIndex a R u x v=(n : ℤ)} ω x ≤
      G.adjustedBandCount a (R*((n : ℝ)-1)) (R*((n : ℝ)+1)) ω x := by
  apply ENNReal.tsum_le_tsum
  intro y
  by_cases hy : G.adjustedLayerIndex a R u x y=(n : ℤ) ∧
      Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
        {v | G.adjustedLayerIndex a R u x v ≤ (n : ℤ)}) x y
  · have hh := G.adjustedLayerIndex_height_bounds a R u hR x y
    rw [hy.1] at hh
    simp only [Int.cast_natCast] at hh
    have hc : y ∈ G.cluster ω x := by
      change y ∈ (criticalModel G.ends).cluster ω x
      rw [criticalModel_cluster]
      exact Percolation.conn_mono G.ends Set.inter_subset_left hy.2
    have ht : y ∈ G.cluster ω x ∧ R*((n : ℝ)-1) ≤ G.orbitAdjustedHeight a x y ∧
        G.orbitAdjustedHeight a x y ≤ R*((n : ℝ)+1) := ⟨hc,hh.1.le,hh.2.le⟩
    simp only [Set.mem_ofPred_eq,ite_eq_left hy,adjustedBandTransport,ite_eq_left ht,le_refl]
  · simp only [Set.mem_ofPred_eq,ite_eq_right hy]
    exact bot_le

lemma spaced_down_bands_sum_le_cluster (a : V → ℝ) (R : ℝ) (hR : 0 < R)
    (s : Finset ℕ) (ω : Set E) (x : V) :
    (∑ n ∈ s, G.adjustedBandCount a (-R*(3*(n : ℝ)+1)) (-R*(3*(n : ℝ)-1)) ω x) ≤
      ∑' y, if y ∈ G.cluster ω x then (1 : ℝ≥0∞) else 0 := by
  unfold adjustedBandCount
  rw [←Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply ENNReal.tsum_le_tsum
  intro y
  by_cases hy : y ∈ G.cluster ω x
  · simp only [adjustedBandTransport,hy,true_and,ite_true]
    rw [Finset.sum_boole]
    have hcard : (s.filter fun (n : ℕ) => -R*(3*(n : ℝ)+1) ≤ G.orbitAdjustedHeight a x y ∧
        G.orbitAdjustedHeight a x y ≤ -R*(3*(n : ℝ)-1)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro n hn m hm
      have hn' := (Finset.mem_filter.mp hn).2
      have hm' := (Finset.mem_filter.mp hm).2
      rcases lt_trichotomy n m with hnm | hnm | hmn
      · have hh : (n : ℝ)+1 ≤ m := by exact_mod_cast (Nat.succ_le_iff.mpr hnm)
        nlinarith
      · exact hnm
      · have hh : (m : ℝ)+1 ≤ n := by exact_mod_cast (Nat.succ_le_iff.mpr hmn)
        nlinarith
    simpa only [Nat.cast_one] using (Nat.cast_le (α := ℝ≥0∞)).mpr hcard
  · simp [adjustedBandTransport,hy]

variable [Countable V] [Countable E]

lemma measurable_adjustedBandCount (a : V → ℝ) (l u : ℝ) (x : V) :
    Measurable (fun ω => G.adjustedBandCount a l u ω x) :=
  Measurable.tsum fun y => G.measurable_adjustedBandTransport a l u x y

lemma expected_adjustedBandCount_aut (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x) (l u : ℝ)
    (φ : G.Aut) (p : unitInterval) (x : V) :
    (∫⁻ ω, G.adjustedBandCount a l u ω (φ.vertex x) ∂G.law p) =
      ∫⁻ ω, G.adjustedBandCount a l u ω x ∂G.law p := by
  conv_lhs => rw [←G.law_map_aut p φ]
  rw [lintegral_map (G.measurable_adjustedBandCount a l u _)
    (BernoulliProduct.measurable_image_equiv φ.edge)]
  simp only [G.adjustedBandCount_aut a ha l u]

lemma expected_band_le_weighted_roots (O : G.OrbitRepresentatives)
    (a : V → ℝ) (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x)
    (m : ℝ) (hm : 0 < m) (ham : ∀ x, m ≤ a x)
    (p : unitInterval) (l u : ℝ) (x : V) :
    (∫⁻ ω, G.adjustedBandCount a l u ω x ∂G.law p) ≤
      (ENNReal.ofReal m)⁻¹ * ∑ r ∈ O.roots, ENNReal.ofReal (a r)*
        (∫⁻ ω, G.adjustedBandCount a l u ω r ∂G.law p) := by
  have hh : ENNReal.ofReal m*(∫⁻ ω, G.adjustedBandCount a l u ω x ∂G.law p) ≤
      ∑ r ∈ O.roots, ENNReal.ofReal (a r)*
        (∫⁻ ω, G.adjustedBandCount a l u ω r ∂G.law p) := by
    obtain ⟨r,hr,φ,rfl⟩ := O.cover x
    rw [G.expected_adjustedBandCount_aut a ha l u φ p r]
    exact (mul_le_mul' (ENNReal.ofReal_le_ofReal (ham r)) le_rfl).trans
      (Finset.single_le_sum (f := fun r => ENNReal.ofReal (a r)*
        (∫⁻ ω, G.adjustedBandCount a l u ω r ∂G.law p)) (fun _ _ => bot_le) hr)
  calc
    _ = (ENNReal.ofReal m)⁻¹*(ENNReal.ofReal m*
        (∫⁻ ω, G.adjustedBandCount a l u ω x ∂G.law p)) := by
      rw [←mul_assoc,ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hm))
        ENNReal.ofReal_ne_top,one_mul]
    _ ≤ _ := mul_le_mul' le_rfl hh

lemma spaced_down_band_moments_sum_le_row (a : V → ℝ) (R : ℝ) (hR : 0 < R)
    (p : unitInterval) (C : ℝ≥0∞)
    (hrow : ∀ z, (∑' y, G.law p {ω | Percolation.Conn G.ends ω z y}) ≤ C)
    (s : Finset ℕ) (x : V) :
    (∑ n ∈ s, ∫⁻ ω, G.adjustedBandCount a (-R*(3*(n : ℝ)+1))
      (-R*(3*(n : ℝ)-1)) ω x ∂G.law p) ≤ C := by
  rw [←lintegral_finsetSum s (fun n _ => G.measurable_adjustedBandCount a _ _ x)]
  have hall (ω : Set E) : (∑' y, if y ∈ G.cluster ω x then (1 : ℝ≥0∞) else 0) =
      restrictedLayerCount G.ends Set.univ Set.univ ω x := by
    apply tsum_congr
    intro y
    have hc : y ∈ G.cluster ω x ↔ Percolation.Conn G.ends ω x y := by
      change y ∈ (criticalModel G.ends).cluster ω x ↔ _
      rw [criticalModel_cluster]
      rfl
    simp [hc]
  exact (lintegral_mono (fun ω => (G.spaced_down_bands_sum_le_cluster a R hR s ω x).trans_eq
    (hall ω))).trans (restrictedLayerCount_expectation_le_row_bound G.ends p C hrow _ _ x)

theorem spaced_up_layer_moments_sum_bound
    (O : G.OrbitRepresentatives) (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (hapos : ∀ x, 0 < a x)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x)
    (m : ℝ) (hm : 0 < m) (ham : ∀ x, m ≤ a x)
    (R : ℝ) (hR : 0 < R) (p : unitInterval) (C : ℝ≥0∞)
    (hrow : ∀ z, (∑' y, G.law p {ω | Percolation.Conn G.ends ω z y}) ≤ C)
    (s : Finset ℕ) :
    (∑ n ∈ s, ENNReal.ofReal (Real.exp (R*(3*(n : ℝ))))*
      G.supAdjustedUpLayerMoment a R p (3*n)) ≤
      (ENNReal.ofReal m)⁻¹*ENNReal.ofReal (Real.exp R)*
        ((∑ r ∈ O.roots, ENNReal.ofReal (a r))*C) := by
  let D (n : ℕ) := ∑ r ∈ O.roots, ENNReal.ofReal (a r)*
    (∫⁻ ω, G.adjustedBandCount a (-R*(3*(n : ℝ)+1)) (-R*(3*(n : ℝ)-1)) ω r ∂G.law p)
  have hu (n : ℕ) : G.supAdjustedUpLayerMoment a R p (3*n) ≤
      (ENNReal.ofReal m)⁻¹*ENNReal.ofReal (Real.exp (-R*(3*(n : ℝ)-1)))*D n := by
    apply iSup_le
    intro x
    apply iSup_le
    intro u
    have hh := ((lintegral_mono (G.upLayerCount_le_bandCount a R hR (3*n) x u)).trans
      (G.expected_band_le_weighted_roots O a ha m hm ham p _ _ x)).trans
        (mul_le_mul' le_rfl (G.expected_adjustedBandCount_reciprocity O hc hl a hapos ha p
          (R*((3*n : ℕ)-1 : ℝ)) (R*((3*n : ℕ)+1 : ℝ))).2)
    simpa only [adjustedUpLayerMoment,D,Nat.cast_mul,Nat.cast_ofNat,mul_assoc,neg_mul] using hh
  have hp (n : ℕ) : ENNReal.ofReal (Real.exp (R*(3*(n : ℝ))))*
      G.supAdjustedUpLayerMoment a R p (3*n) ≤
      ((ENNReal.ofReal m)⁻¹*ENNReal.ofReal (Real.exp R))*D n := by
    apply (mul_le_mul' le_rfl (hu n)).trans_eq
    calc
      _ = (ENNReal.ofReal m)⁻¹*(ENNReal.ofReal (Real.exp (R*(3*(n : ℝ))))*
          ENNReal.ofReal (Real.exp (-R*(3*(n : ℝ)-1))))*D n := by ring
      _ = _ := by rw [←ENNReal.ofReal_mul (Real.exp_nonneg _),←Real.exp_add,
        show R*(3*(n : ℝ)) + -R*(3*(n : ℝ)-1)=R by ring]
  calc
    _ ≤ ∑ n ∈ s, ((ENNReal.ofReal m)⁻¹*ENNReal.ofReal (Real.exp R))*D n :=
      Finset.sum_le_sum fun n _ => hp n
    _ = ((ENNReal.ofReal m)⁻¹*ENNReal.ofReal (Real.exp R))*(∑ n ∈ s, D n) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := by
      apply mul_le_mul' le_rfl
      dsimp only [D]
      rw [Finset.sum_comm,Finset.sum_mul]
      apply Finset.sum_le_sum
      intro r hr
      rw [←Finset.mul_sum]
      exact mul_le_mul' le_rfl (G.spaced_down_band_moments_sum_le_row a R hR p C hrow s r)

end CriticalPercolation.BondGraph
namespace Percolation.BenjaminiSchramm

lemma exponential_rate_strict_of_spaced_sum
    (S : ℕ → ℝ≥0∞) (R β : ℝ)
    (hlower : ∀ n : ℕ, ENNReal.ofReal (Real.exp (-β*n)) ≤ S n)
    (K : ℝ≥0∞) (hK : K < ⊤)
    (hsum : ∀ s : Finset ℕ,
      (∑ n ∈ s, ENNReal.ofReal (Real.exp (R*(3*(n : ℝ))))*S (3*n)) ≤ K) :
    R < β := by
  by_contra hβ
  have hβR : β ≤ R := le_of_not_gt hβ
  have hterm (n : ℕ) : (1 : ℝ≥0∞) ≤
      ENNReal.ofReal (Real.exp (R*(3*(n : ℝ))))*S (3*n) := by
    calc
      _ ≤ ENNReal.ofReal (Real.exp (R*(3*(n : ℝ))))*
          ENNReal.ofReal (Real.exp (-β*(3*n : ℕ))) := by
        rw [←ENNReal.ofReal_mul (Real.exp_nonneg _),←Real.exp_add,←ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        apply Real.one_le_exp_iff.mpr
        simp only [Nat.cast_mul,Nat.cast_ofNat]
        nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      _ ≤ _ := mul_le_mul' le_rfl (hlower (3*n))
  obtain ⟨N,hN⟩ := exists_nat_gt K.toReal
  have hh : (N : ℝ≥0∞) ≤ K := by
    calc
      _ = ∑ n ∈ Finset.range N, (1 : ℝ≥0∞) := by simp
      _ ≤ ∑ n ∈ Finset.range N, ENNReal.ofReal (Real.exp (R*(3*(n : ℝ))))*S (3*n) :=
        Finset.sum_le_sum fun n _ => hterm n
      _ ≤ _ := hsum _
  have hh' := ENNReal.toReal_mono hK.ne hh
  simp only [ENNReal.toReal_natCast] at hh'
  exact (not_lt_of_ge hh') hN

end Percolation.BenjaminiSchramm
namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem normalized_layer_rate_strict_of_lower
    (O : G.OrbitRepresentatives) (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (hapos : ∀ x, 0 < a x)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x)
    (m : ℝ) (hm : 0 < m) (ham : ∀ x, m ≤ a x)
    (R : ℝ) (hR : 0 < R) (p : unitInterval) (C : ℝ≥0∞) (hC : C < ⊤)
    (hrow : ∀ z, (∑' y, G.law p {ω | Percolation.Conn G.ends ω z y}) ≤ C)
    (β : ℝ) (hlower : ∀ n : ℕ, ENNReal.ofReal (Real.exp (-β*n)) ≤
      G.supAdjustedUpLayerMoment a R p n) : R < β := by
  apply exponential_rate_strict_of_spaced_sum _ R β hlower
    ((ENNReal.ofReal m)⁻¹*ENNReal.ofReal (Real.exp R)*
      ((∑ r ∈ O.roots, ENNReal.ofReal (a r))*C))
  · apply ENNReal.mul_lt_top
    · exact ENNReal.mul_lt_top
        (lt_top_iff_ne_top.mpr (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hm).ne'))
        ENNReal.ofReal_lt_top
    · exact ENNReal.mul_lt_top (ENNReal.sum_lt_top.mpr fun r _ => ENNReal.ofReal_lt_top) hC
  · exact G.spaced_up_layer_moments_sum_bound O hc hl a hapos ha m hm ham R hR p C hrow

end CriticalPercolation.BondGraph

end

end OAI
