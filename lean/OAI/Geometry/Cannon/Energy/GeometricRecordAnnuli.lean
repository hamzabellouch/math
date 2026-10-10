import Mathlib
import OAI.Geometry.Cannon.Modulus.GeometricAnnularCompactTails

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
open Set Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set Metric Topology
open Set Topology unitInterval
open scoped BigOperators
open Set unitInterval
open Set MeasureTheory
open Set Filter Metric Topology
open Set Filter Topology
open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
open Set Filter Topology TopologicalSpace Metric

namespace CannonApprox

open CannonGrid CannonChart CannonCharts CannonScales CannonPacking CannonAnnular
open Set Metric Filter Topology MeasureTheory

theorem geometric_record_annuli {X : Type*} [MetricSpace X] [CompactSpace X]
    [LocallyPathConnectedSpace X] [MeasurableSpace X] [BorelSpace X]
    (φ : X ≃ₜ SphereTwo) (d : ℝ) (hd : 0 < d) (hdia : d < diam (univ : Set X))
    (a : ℝ) (ha : 1 < a) (Q : ℕ) (CP C c L : ℝ)
    (hpack : PolynomialPacking (X := X) Q CP) (hCP : 0 ≤ CP)
    (hC : 0 ≤ C) (hc : 0 < c) (hL : 1 ≤ L) (hdc : d ≤ c)
    (hpaths : ∀ (o u v : X) (s : ℝ), 0 < s → dist o u ≤ s → dist o v ≤ s →
      JoinedIn {z | dist o z < L*s} u v)
    (hexp : ∀ (o : X) (l : ℕ), ∃ h : X → X, Continuous h ∧
      ∀ u v, dist u o ≤ 3*(a^l)⁻¹ → dist v o ≤ 3*(a^l)⁻¹ →
        dist (h u) (h v) ≤ C/(a^l)⁻¹*dist u v ∧
        c/(a^l)⁻¹*dist u v ≤ dist (h u) (h v))
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (p : ∀ n, ι n → X)
    (hpsep : ∀ n i j, i ≠ j → (a^n)⁻¹ ≤ dist (p n i) (p n j))
    (hpnet : ∀ n x, ∃ i, dist (p n i) x ≤ (a^n)⁻¹)
    (e : Square → X) (he : IsEmbedding e) (N : ℕ → ℕ)
    (ρ : ∀ n, ι (N n) → ℝ) (hρ : ∀ n i, 0 ≤ ρ n i)
    (hadm : ∀ n, Admissible (fun i => e ⁻¹' ball (p (N n) i) (2*(a^(N n))⁻¹)) (ρ n))
    (m : ℕ → ℕ) (hm : ∀ n, 0 < m n)
    (hmesh : ∀ n z, ∀ i : Index (3*m n), weight (3*m n) z i ≠ 0 →
      dist (e z) (e (vertex (3*m n) (by have := hm n; omega) i)) < (a^(N n))⁻¹)
    (lam : ℝ) (hlam : 1 ≤ lam)
    (hrecord : ∀ n l, l ≤ N n →
      CannonCells.modulus (fun i => ball (p (N n-l) i) (2*(a^(N n-l))⁻¹)) (macroFamily d) ≤
      (lam^l)⁻¹*CannonCells.modulus (fun i => ball (p (N n) i) (2*(a^(N n))⁻¹)) (macroFamily d)) :
    let M := fun n => CannonCells.modulus (fun i => ball (p n i) (2*(a^n)⁻¹)) (macroFamily d)
    let f := fun n => interiorScalar e he (p (N n)) ((a^(N n))⁻¹)
      (ρ n) (hρ n) (hadm n) (m n) (hm n)
    let μ := fun n => CannonAtomic.atomic (p (N n)) (ρ n) (M (N n))
      (by apply Real.sInf_nonneg; rintro t ⟨w,_,rfl⟩; exact sq_nonneg _)
    ∃ E : ℝ, 0 ≤ E ∧ ∀ K : Set X, IsCompact K → K ⊆ interior (range e) →
      ∃ l₀ m₀ : ℕ, ∀ l, l₀ ≤ l → ∀ n, l+m₀ ≤ N n → ∀ o ∈ K,
      ∀ x y : interior (range e),
        dist x.val o ≤ (a^l)⁻¹/(2*L) → dist y.val o ≤ (a^l)⁻¹/(2*L) →
        (f n x-f n y)^2 ≤ (E/(lam^l)) *
          (μ n {z | (a^l)⁻¹/4 ≤ dist z o ∧ dist z o ≤ 4*(a^l)⁻¹} : ℝ) := by
  classical
  let M := fun n => CannonCells.modulus (fun i => ball (p n i) (2*(a^n)⁻¹)) (macroFamily d)
  obtain ⟨E,hE,hann⟩ := geometric_annular_compact_tails φ d hd hdia a ha Q CP C c L
    hpack hCP hC hc hL hdc hpaths hexp ι p hpsep hpnet e he N ρ hρ hadm m hm hmesh
  refine ⟨E,hE,fun K hK hKU => ?_⟩
  obtain ⟨l₀,m₀,hann⟩ := hann K hK hKU
  refine ⟨l₀,m₀,fun l hl n hn o ho x y hx hy => ?_⟩
  have hap : 0 < a := zero_lt_one.trans ha
  have hM : 0 < M (N n) := (sphere_macro_modulus_minimum φ d hd hdia (p (N n))
    ((a^(N n))⁻¹) (fun z => by
      obtain ⟨i,hi⟩ := hpnet (N n) z
      refine ⟨i,?_⟩
      rw [mem_ball,dist_comm]
      exact hi.trans_lt (by have := inv_pos.mpr (pow_pos hap (N n)); linarith))).1
  have hrec : M (N n-l) ≤ M (N n)/(lam^l) := by
    simpa only [inv_mul_eq_div] using hrecord n l (by omega)
  have hS : MeasurableSet {z : X | (a^l)⁻¹/4 ≤ dist z o ∧ dist z o ≤ 4*(a^l)⁻¹} :=
    ((isClosed_le continuous_const (continuous_id.dist continuous_const)).inter
      (isClosed_le (continuous_id.dist continuous_const) continuous_const)).measurableSet
  exact CannonAtomic.record_annular_bound (p (N n)) (ρ n) (M (N n)) (M (N n-l)) E
    _ (lam^l) hM hE (pow_pos (zero_lt_one.trans_le hlam) l) hrec _ hS
    (by
      convert hann l hl n hn o ho x y hx hy using 1
      congr 2
      ext i
      simp only [Finset.mem_filter, Set.mem_ofPred_eq])

end CannonApprox

end
end
end
end
end
end
end
end
end

end OAI
