import OAI.Geometry.SurfaceImmersion.Correction.RealPolynomialQuadraticBounds
import OAI.Geometry.SurfaceImmersion.Geometry.TensorPerturbationOperator
import OAI.Geometry.SurfaceImmersion.Correction.PerturbationTaylorBounds

namespace OAI

/-! Common tensor bounds for the actual mixed quadratic term and cubic
Taylor remainder. The exponent does not depend on the correction depth. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates

def tensorQuadraticCross {n : ℕ} (P : Fin 3 → Fin n → Expression) (ε : ℝ)
    (G H K : Base → Space) (t : ℝ) : Base → PhaseMean.Tensor :=
  fun p k => quadraticCross (P k) ε G H K t p

def tensorTaylorRemainder {n : ℕ} (P : Fin 3 → Fin n → Expression) (ε : ℝ)
    (G H : Base → Space) (t : ℝ) : Base → PhaseMean.Tensor :=
  fun p k => taylorRemainder (P k) ε G H t p

lemma tensorQuadraticCross_smooth {n : ℕ} {P : Fin 3 → Fin n → Expression}
    (hP : ∀ k l, (P k l).SmoothCoeffs Set.univ)
    {G H K : Base → Space} (hG : ContDiff ℝ ∞ G)
    (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K) (ε t : ℝ) :
    ContDiff ℝ ∞ (tensorQuadraticCross P ε G H K t) := by
  apply contDiff_pi.mpr
  intro k
  apply contDiffOn_univ.mp
  exact contDiffOn_const.mul
    ((realVariation_smooth isOpen_univ (hP k) (pairFamily_smooth hG hH hK)
      (fun _ _ => Set.mem_univ _) ε 1 t).add
    (realVariation_smooth isOpen_univ (hP k) (pairFamily_smooth hG hK hH)
      (fun _ _ => Set.mem_univ _) ε 1 t))

lemma tensorTaylorRemainder_smooth {n : ℕ} {P : Fin 3 → Fin n → Expression}
    (hP : ∀ k l, (P k l).SmoothCoeffs Set.univ)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (ε t : ℝ) :
    ContDiff ℝ ∞ (tensorTaylorRemainder P ε G H t) := by
  apply contDiff_pi.mpr
  intro k
  change ContDiff ℝ ∞ (fun p => ∑ l, ε ^ (l.val + 1) * (P k l).taylorRemainder G H t p)
  exact ContDiff.sum fun l _ => contDiff_const.mul
    (expression_taylorRemainder_smooth (hP k l) hG hH t)

theorem tensorQuadraticCross_bound {n : ℕ} {U : Set Base} {Q : Set LowJet}
    (hU : IsOpen U) (hQ : IsCompact Q)
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k l, (P k l).SmoothCoeffs Set.univ)
    (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (G H K : Base → Space) (s ε C D : ℝ),
      0 < s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 → 0 < C → 0 < D →
      ContDiff ℝ ∞ G → ContDiff ℝ ∞ H → ContDiff ℝ ∞ K →
      Set.MapsTo (lowJet G) U Q → WeightedBound U s (m + tensorOrder P) B (lowJet G) →
      WeightedBound U s (m + tensorOrder P) C H →
      WeightedBound U s (m + tensorOrder P) D K → ∀ t ∈ Set.Icc (0 : ℝ) 1,
        WeightedBound U s m (E * ε * C * D / s ^ tensorLoss P)
          (tensorQuadraticCross P ε G H K t) := by
  have hex (k : Fin 3) := quadraticCross_bound hU isOpen_univ hQ (Set.subset_univ Q)
    (P k) (hP k) m B hB
  choose E hE he using hex
  refine ⟨∑ k, E k, Finset.sum_nonneg (fun k _ => hE k), ?_⟩
  intro G H K s ε C D hs hs1 hε hε1 hC hD hG hH hK hGQ hGb hHb hKb t ht
  have hsum : 0 ≤ ∑ k, E k := Finset.sum_nonneg (fun k _ => hE k)
  apply WeightedBound.pi hU.uniqueDiffOn hs (by positivity)
  · exact contDiffOn_pi.mp (tensorQuadraticCross_smooth hP hG hH hK ε t).contDiffOn
  · intro k
    have hEk := hE k
    have ho : order (P k) ≤ tensorOrder P :=
      Finset.le_sup (f := fun j => order (P j)) (Finset.mem_univ k)
    have hl : loss (P k) ≤ tensorLoss P :=
      Finset.le_sup (f := fun j => loss (P j)) (Finset.mem_univ k)
    have hb := he k G H K s ε C D hs hs1 hε hε1 hC hD hG hH hK hGQ
      (hGb.mono_order (Nat.add_le_add_left ho m))
      (hHb.mono_order (Nat.add_le_add_left ho m)) (hKb.mono_order (Nat.add_le_add_left ho m)) t ht
    apply hb.mono_const
    calc
      _ ≤ E k * ε * C * D / s ^ tensorLoss P :=
        div_le_div_of_nonneg_left (by positivity) (pow_pos hs _)
          (pow_le_pow_of_le_one hs.le hs1 hl)
      _ ≤ _ := by
        gcongr
        exact Finset.single_le_sum (fun j _ => hE j) (Finset.mem_univ k)

theorem tensorTaylorRemainder_bound {n : ℕ} {U : Set Base} {Q : Set LowJet}
    (hU : IsOpen U) (hQ : IsCompact Q)
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k l, (P k l).SmoothCoeffs Set.univ)
    (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (G H : Base → Space) (s ε C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 → 0 < C →
      ContDiff ℝ ∞ G → ContDiff ℝ ∞ H →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, Set.MapsTo (lowJet (fun p => G p + t • H p)) U Q) →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, WeightedBound U s (m + tensorOrder P) B
        (lowJet (fun p => G p + t • H p))) →
      WeightedBound U s (m + tensorOrder P) C H → ∀ t ∈ Set.Icc (0 : ℝ) 1,
        WeightedBound U s m (E * ε * C ^ 3 / s ^ tensorLoss P)
          (tensorTaylorRemainder P ε G H t) := by
  have hex (k : Fin 3) := compact_taylorRemainder_bound hU hQ (P k) (hP k) m B hB
  choose E hE he using hex
  refine ⟨∑ k, E k, Finset.sum_nonneg (fun k _ => hE k), ?_⟩
  intro G H s ε C hs hs1 hε hε1 hC hG hH hGQ hGb hHb t ht
  have hsum : 0 ≤ ∑ k, E k := Finset.sum_nonneg (fun k _ => hE k)
  apply WeightedBound.pi hU.uniqueDiffOn hs (by positivity)
  · exact contDiffOn_pi.mp (tensorTaylorRemainder_smooth hP hG hH ε t).contDiffOn
  · intro k
    have hEk := hE k
    have ho : order (P k) ≤ tensorOrder P :=
      Finset.le_sup (f := fun j => order (P j)) (Finset.mem_univ k)
    have hl : loss (P k) ≤ tensorLoss P :=
      Finset.le_sup (f := fun j => loss (P j)) (Finset.mem_univ k)
    have hb := he k G H s C ε hs hs1 hC hε hε1 hG hH hGQ
      (fun t ht => (hGb t ht).mono_order (Nat.add_le_add_left ho m))
      (hHb.mono_order (Nat.add_le_add_left ho m)) t ht
    apply hb.mono_const
    calc
      _ ≤ E k * ε * C ^ 3 / s ^ tensorLoss P :=
        div_le_div_of_nonneg_left (by positivity) (pow_pos hs _)
          (pow_le_pow_of_le_one hs.le hs1 hl)
      _ ≤ _ := by
        gcongr
        exact Finset.single_le_sum (fun j _ => hE j) (Finset.mem_univ k)

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
