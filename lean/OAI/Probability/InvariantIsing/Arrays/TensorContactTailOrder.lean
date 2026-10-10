import OAI.Probability.InvariantIsing.Spectral.SpectralContactTails

namespace OAI

/-! The actual joint minima enforce upper-tail order at their synchronized
GG limit. All finite field directions are taken at those same minima. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem tensorContact_limit_tail_order
    (N : ℕ → ℕ) (hN : ∀ k, 0 < N k) (m n : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (eig c : (k : ℕ) → Fin (N k) → ℝ)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (hdis : ∀ k, Set.PairwiseDisjoint (Set.univ : Set (Fin m)) (I k))
    (hcover : ∀ k, Finset.univ.biUnion (I k) = Finset.univ)
    (cut : Fin (n + 2) → ℝ) (hc : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (trial : OverlapPath) (values : Fin (n + 1) → ℝ)
    (hvalues : ∀ i s, s ∈ Ioo (cut i.castSucc) (cut i.succ) → trial s = values i)
    (S : ℝ) (V : ℝ → ℝ) (H : ℝ)
    (p : (k : ℕ) → TensorContactParameter (N k) m n)
    (hp : ∀ k, p k ∈ tensorContactRegion (N k) m n H)
    (hmin : ∀ k q, q ∈ tensorContactRegion (N k) m n H →
      tensorContactObjective (μ k) (eig k) (c k) (I k) (chainExponent cut)
        (fun i => (cut i.succ - cut i.castSucc) * values i) S V (p k) ≤
      tensorContactObjective (μ k) (eig k) (c k) (I k) (chainExponent cut)
        (fun i => (cut i.succ - cut i.castSucc) * values i) S V q)
    (hcap : ∀ k, (∑ i, (p k).2.1 i) < H)
    (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (hL : Tendsto (fun k => tensorPerturbedArrayLaw (μ k) (eig k) (c k) (I k)
      (p k).2.2.1 (p k).2.2.2 (p k).1 n (chainExponent cut) (finiteFieldPath (p k).2.1))
      atTop (𝓝 Q))
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m + 1))))
    (q : Fin (m + 1) → ℝ) (hq : ∀ a, 0 ≤ q a)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i a, (x (i,i) a : ℝ) = q a)
    (hP : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ a, 0 ≤ (x (0,1) a : ℝ)) :
    ∀ s ∈ Icc (0 : ℝ) 1, pathTail trial s ≤ pathTail (spectralSpinQuantilePath Q hP hn) s := by
  classical
  have hb := chainExponent_admissible hc hfirst hlast
  have hh k := monotone_finiteFieldPath (tensorContactRegion_bounds (hp k)).2.1
  have h0 k := finiteFieldPath_nonneg (tensorContactRegion_bounds (hp k)).2.1 0
  have hgeom := tensorPerturbedArrayLaw_limit_geometry N m n μ eig c I
    (fun k => (p k).2.2.1) (fun k => (p k).2.2.2) (fun k => (p k).1)
    (chainExponent cut) (fun k => finiteFieldPath (p k).2.1) Q hL
  have hlevels := tensorPerturbedArrayLaw_limit_treeLevels N m n μ eig c I
    (fun k => (p k).2.2.1) (fun k => (p k).2.2.2) (fun k => (p k).1)
    (chainExponent cut) (fun k => finiteFieldPath (p k).2.1) Q hL 0 1
  have htails (d : Fin n) :
      (∫ x, treeTail n d (x (0,1) (Fin.last m) : ℝ)
        ∂(Q : Measure (SpectralArray (m + 1)))) = 1 - cut d.succ.castSucc := by
    have he := tensorPerturbedArrayLaw_limit_treeTail N hN m n μ eig c I
      (fun k => (p k).2.2.1) (fun k => (p k).2.2.2) (fun k => (p k).1)
      (chainExponent cut) hb (fun k => finiteFieldPath (p k).2.1) hh h0 Q hL d
    rw [chainExponent_apply cut d.isLt] at he
    convert he using 1
    apply congrArg (fun a => 1 - cut a)
    exact Fin.ext rfl
  have hcut (j) : cut j ∈ Icc (0 : ℝ) 1 :=
    ⟨by rw [← hfirst]; exact hc.monotone (Fin.zero_le _),
     by rw [← hlast]; exact hc.monotone (Fin.le_last _)⟩
  apply contact_partition_tail_order _ trial cut hc hfirst hlast values hvalues
  intro j
  have hlim := spectralSpinDepthTail_weak_limit hL (n := n) j
  have hineq : (∑ i, ((cut i.succ - cut i.castSucc) * values i) *
      finiteFieldPath (Pi.single j 1) i) ≤
      ∫ x, spectralSpinDepthTail n j x ∂(Q : Measure (SpectralArray (m + 1))) := by
    apply ge_of_tendsto' hlim
    intro k
    have he := tensorNamespacedArrayLaw_field_tail (μ k)
      (diagonalPerturbedEigenvalues (eig k) (I k) (p k).2.2.2 (p k).1) (c k) (I k)
      (hdis k) (hcover k) (fun r => enumeratedSpectralDegree m r)
      (tensorPerturbationAmplitude (N k) (p k).2.2.1) (chainExponent cut)
      (finiteFieldPath (p k).2.1) (fun r => enumeratedTreeDegree m r) j
    have hcdir := tensorContact_minimum_field_cone (hN k) (μ k) (eig k) (c k) (I k)
      (chainExponent cut) (fun i => (cut i.succ - cut i.castSucc) * values i)
      S V H (p k) (hp k) (hmin k) (hcap k) (Pi.single j 1)
      (fun i => by simp only [Pi.single_apply]; split_ifs <;> norm_num)
    exact hcdir.trans_eq he.symm
  rwa [spectralPair_depthTail_integral Q hgg hgeom.1 q hq hd
    (fun e => hgeom.2 e e.injective) hP hn hlevels cut hfirst hcut htails j] at hineq

end InvariantIsing

end

end OAI
