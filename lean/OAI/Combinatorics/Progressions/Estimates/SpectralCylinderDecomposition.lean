import OAI.Combinatorics.Progressions.Polynomial.FiniteMarginalLowDegree

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_spectral_cylinder_decomposition {Ω ι : Type*} [Fintype Ω] [Fintype ι] [LinearOrder ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (hμ : ∀ i x, 0 < (μ i).weight x)
    (base : ∀ i, X i) (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i)
    (K τ η P : ℝ) (j r q A : ℕ) (hK : 1 ≤ K) (hτ : 0 < τ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hq : 2 ≤ q) (heven : Even q) (hrP : (r : ℝ) ≤ P) (hlog : Real.log (2 + τ⁻¹) ≤ P)
    (hPq : P ≤ (q : ℝ)) (hqP : (q : ℝ) ≤ P + 2)
    (hsmall : η ≤ (1 / 2) * (((2 : ℝ) ^ (r + 1) * (2 + (Fintype.card ι : ℝ)) ^ r * (2 + τ⁻¹)) ^ q)⁻¹)
    (hA : 1 ≤ A) (hX : ∀ i, Fintype.card (X i) ≤ A) (hcut : 2 ≤ τ * K ^ (j + 1))
    (hbase : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η (j + r * (q + 1)))
    (w : Ω → ℝ) (hw0 : ∀ z, 0 ≤ w z) (hw1 : ∀ z, w z ≤ 1) :
    ∃ (v : Ω → ℝ) (cs : List (ProductCylinder X)),
      CylinderRemovalChain μ base p F K τ j r w v cs ∧ cs.Nodup ∧
      cs.length ≤ (∑ k ∈ Finset.range (j + r + 1), (Fintype.card ι).choose k) * A ^ (j + r) ∧
      (removedCylinderWeights F w cs).Pairwise (fun f g => ∀ z, f z = 0 ∨ g z = 0) ∧
      (∀ z, w z = ((removedCylinderWeights F w cs).map (fun f => f z)).sum + v z) ∧
      (∀ f ∈ removedCylinderWeights F w cs, ∀ z, 0 ≤ f z ∧ f z ≤ 1) ∧
      p.mean v ≤ τ ∧ (∀ z, 0 ≤ v z ∧ v z ≤ 1) ∧
      (∀ cf ∈ cs.zip (removedCylinderWeights F w cs), ∀ k : ℕ, k ≤ r →
        Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k)
          (ProductCylinder.normalizedSection μ base (observedProductDensity μ p F cf.2) cf.1)) ≤
            (8 * (1 + K) * (P + 2)) ^ (2 * k)) := by
  have horder : j + r ≤ j + r * (q + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  obtain ⟨v, cs, hchain, hno, hcount, hdis, hdec, hweights, hres, hv⟩ :=
    exists_regular_cylinder_decomposition μ hμ base p F K τ η j r A hK hτ.le hη1 hA hX hcut
      (ProductMarginalsClose.mono μ hbase horder) w hw0 hw1
  exact ⟨v, cs, hchain, hno, hcount, hdis, hdec, hweights, hres, hv,
    hchain.low_degree_bounds hμ hK hτ hη0 hq heven hrP hlog hPq hqP hsmall hbase
      (fun z => ⟨hw0 z, hw1 z⟩)⟩

end Erdos3

end

end OAI
