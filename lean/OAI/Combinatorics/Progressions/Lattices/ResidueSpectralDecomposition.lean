import OAI.Combinatorics.Progressions.Estimates.SpectralCylinderDecomposition
import OAI.Combinatorics.Progressions.Polynomial.StableSiteLowDegree

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_residue_spectral_decomposition {ι σ : Type*} [Fintype ι] [LinearOrder ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a))
    (moduli : ι → ℕ) [∀ i, NeZero (moduli i)] (hM : 0 < M)
    (hcop : ∀ i, M.Coprime (moduli i))
    (hpair : Pairwise (fun i l => (moduli i).Coprime (moduli l)))
    (K τ η P : ℝ) (j r q A : ℕ) (hK : 1 ≤ K) (hτ : 0 < τ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hq : 2 ≤ q) (heven : Even q) (hrP : (r : ℝ) ≤ P) (hlog : Real.log (2 + τ⁻¹) ≤ P)
    (hPq : P ≤ (q : ℝ)) (hqP : (q : ℝ) ≤ P + 2)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P)
    (hηsmall : η ≤ (1 / 2) * Real.exp (-((P + 3) ^ 3)))
    (hA : 1 ≤ A) (halphabet : ∀ i, moduli i ^ Fintype.card σ ≤ A)
    (hcut : 2 ≤ τ * K ^ (j + 1))
    (B C D : ℝ) (hB : 0 ≤ B) (herror : Real.exp (-D) ≤ η)
    (hmoduli : ∀ i, (moduli i : ℝ) ≤ Real.exp B) (hdim : (Fintype.card σ : ℝ) ≤ Real.exp C)
    (hlength : ∀ k, Real.exp (B * (j + r * (q + 1) : ℕ) + D + C + 1) ≤
      (residueIndexLength (lo k) (lo k + N k) M (a k) : ℝ))
    (w : IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a → ℝ)
    (hw0 : ∀ z, 0 ≤ w z) (hw1 : ∀ z, w z ≤ 1) :
    let μ := primeCoordinateReference (σ := σ) moduli
    let p := @FiniteProbabilityWeights.uniform
      (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a) _ hne
    let F := fun z : IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a =>
      primeCoordinateObservation moduli (fun k => (z k).val)
    ∃ (v : IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a → ℝ)
      (cs : List (ProductCylinder (fun i => σ → ZMod (moduli i)))),
      CylinderRemovalChain μ (fun _ _ => 0) p F K τ j r w v cs ∧ cs.Nodup ∧
      cs.length ≤ (∑ k ∈ Finset.range (j + r + 1), (Fintype.card ι).choose k) * A ^ (j + r) ∧
      (removedCylinderWeights F w cs).Pairwise (fun f g => ∀ z, f z = 0 ∨ g z = 0) ∧
      (∀ z, w z = ((removedCylinderWeights F w cs).map (fun f => f z)).sum + v z) ∧
      (∀ f ∈ removedCylinderWeights F w cs, ∀ z, 0 ≤ f z ∧ f z ≤ 1) ∧
      p.mean v ≤ τ ∧ (∀ z, 0 ≤ v z ∧ v z ≤ 1) ∧
      (∀ cf ∈ cs.zip (removedCylinderWeights F w cs), ∀ k : ℕ, k ≤ r →
        Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k)
          (ProductCylinder.normalizedSection μ (fun _ _ => 0) (observedProductDensity μ p F cf.2) cf.1)) ≤
            (8 * (1 + K) * (P + 2)) ^ (2 * k)) := by
  let := hne
  have hP : 0 ≤ P := (Nat.cast_nonneg r).trans hrP
  have hMcap : τ⁻¹ ≤ Real.exp P := by
    have hh := Real.le_exp_of_log_le hlog
    linarith
  have hbudget := approxMoment_small_of_exponential (Fintype.card ι) r q (τ⁻¹) P hP
    (inv_nonneg.mpr hτ.le) hcount hMcap hrP hqP hηsmall
  have hbase := residuePrimeDensity_close_of_lengths lo N M a hne moduli hM hcop hpair
    (j + r * (q + 1)) B C D η hB hη1 herror hmoduli hdim hlength
  exact exists_spectral_cylinder_decomposition (primeCoordinateReference (σ := σ) moduli)
    (primeCoordinateReference_weight_pos moduli) (fun _ _ => 0)
    (FiniteProbabilityWeights.uniform (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a))
    (fun z => primeCoordinateObservation moduli (fun k => (z k).val))
    K τ η P j r q A hK hτ hη0 hη1 hq heven hrP hlog hPq hqP hbudget hA
    (fun i => by simpa only [Fintype.card_fun, ZMod.card] using halphabet i)
    hcut hbase w hw0 hw1

end Erdos3

end

end OAI
