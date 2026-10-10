import Mathlib
import OAI.Geometry.Cannon.Energy.GeometricRecordAnnuli
import OAI.Geometry.Cannon.ScalarLimits.ReciprocalPowLog

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

theorem geometric_limit_measure_holder {X : Type*} [MetricSpace X] [CompactSpace X]
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
      (lam^l)⁻¹*CannonCells.modulus (fun i => ball (p (N n) i) (2*(a^(N n))⁻¹)) (macroFamily d))
    (hN : StrictMono N) (A : ℝ) (hA : 0 ≤ A)
    (henergy : ∀ n, (∑ i, (ρ n i)^2) ≤ A /
      CannonCells.modulus (fun i => ball (p (N n) i) (2*(a^(N n))⁻¹)) (macroFamily d))
    (u : C(interior (range e),ℝ)) (ν : FiniteMeasure X)
    (hu : ∀ x, u x ∈ Icc (0:ℝ) 1)
    (hf : Tendsto (fun n => interiorScalar e he (p (N n)) ((a^(N n))⁻¹)
      (ρ n) (hρ n) (hadm n) (m n) (hm n)) atTop (𝓝 u))
    (hμ : Tendsto (fun n => CannonAtomic.atomic (p (N n)) (ρ n)
      (CannonCells.modulus (fun i => ball (p (N n) i) (2*(a^(N n))⁻¹)) (macroFamily d))
      (by apply Real.sInf_nonneg; rintro t ⟨w,_,rfl⟩; exact sq_nonneg _)) atTop (𝓝 ν)) :
    ∃ E : ℝ, 0 ≤ E ∧
      (∀ K : Set X, IsCompact K → K ⊆ interior (range e) → ∃ s₀ : ℝ, 0 < s₀ ∧
        ∀ s : ℝ, 0 < s → s ≤ s₀ → ∀ o ∈ K,
          closedBall o s ⊆ interior (range e) ∧
          (CannonScalarLimit.osc (Subtype.val ⁻¹' closedBall o s : Set (interior (range e))) u)^2 ≤
            E*(ν (closedBall o ((8*a*L)*s)) : ℝ)) ∧
      (1 < lam → 0 < Real.log lam/(2*Real.log a) ∧
        ∀ K : Set X, IsCompact K → K ⊆ interior (range e) → ∃ D : ℝ, 0 ≤ D ∧
          ∀ x y : interior (range e), x.val ∈ K → y.val ∈ K →
            |u x-u y| ≤ D*(dist x y)^(Real.log lam/(2*Real.log a))) := by
  classical
  let M := fun n => CannonCells.modulus (fun i => ball (p n i) (2*(a^n)⁻¹)) (macroFamily d)
  have hM (n : ℕ) : 0 < M n := (sphere_macro_modulus_minimum φ d hd hdia (p n)
    ((a^n)⁻¹) (fun z => by
      obtain ⟨i,hi⟩ := hpnet n z
      refine ⟨i,?_⟩
      rw [mem_ball,dist_comm]
      exact hi.trans_lt (by
        have := inv_pos.mpr (pow_pos (zero_lt_one.trans ha) n)
        linarith))).1
  let μ := fun n => CannonAtomic.atomic (p (N n)) (ρ n) (M (N n)) (hM (N n)).le
  have hmass (n : ℕ) : ((μ n).mass : ℝ) ≤ A :=
    CannonAtomic.mass_bound (p (N n)) (ρ n) (M (N n)) (hM (N n)) A (henergy n)
  obtain ⟨E,hE,hann⟩ := geometric_record_annuli φ d hd hdia a ha Q CP C c L
    hpack hCP hC hc hL hdc hpaths hexp ι p hpsep hpnet e he N ρ hρ hadm m hm hmesh
    lam hlam hrecord
  refine ⟨E,hE,?_,?_⟩
  · apply CannonMeasureOscillation.annular_to_measure (interior (range e)) isOpen_interior
      _ u μ ν N hN.tendsto_atTop a L E ha (zero_lt_one.trans_le hL) hE _ hf hμ
    intro K hK hKU
    obtain ⟨l₀,m₀,hann⟩ := hann K hK hKU
    refine ⟨l₀,m₀,fun l hl n hn o ho x y hx hy => (hann l hl n hn o ho x y hx hy).trans ?_⟩
    apply mul_le_mul_of_nonneg_right _ (NNReal.coe_nonneg _)
    exact div_le_self hE (one_le_pow₀ hlam)
  · intro hlamp
    exact CannonMeasureOscillation.annular_to_holder (interior (range e)) isOpen_interior
      _ u μ N hN.tendsto_atTop a L E A lam ha (zero_lt_one.trans_le hL) hE hA
      hlamp hmass hu hann hf

end CannonApprox

open scoped NNReal ENNReal
open Set Metric

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
