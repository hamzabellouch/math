import Mathlib
import OAI.Geometry.Cannon.ScalarLimits.InteriorScalar

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

namespace CannonApprox

open CannonGrid CannonChart CannonCharts CannonScales CannonPacking CannonAnnular
open Set Metric Filter Topology

theorem geometric_annular_compact_tails {X : Type*} [MetricSpace X] [CompactSpace X]
    [LocallyPathConnectedSpace X]
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
      dist (e z) (e (vertex (3*m n) (by have := hm n; omega) i)) < (a^(N n))⁻¹) :
    let M := fun n => CannonCells.modulus (fun i => ball (p n i) (2*(a^n)⁻¹)) (macroFamily d)
    let f := fun n => interiorScalar e he (p (N n)) ((a^(N n))⁻¹)
      (ρ n) (hρ n) (hadm n) (m n) (hm n)
    ∃ E : ℝ, 0 ≤ E ∧ ∀ K : Set X, IsCompact K → K ⊆ interior (range e) →
      ∃ l₀ m₀ : ℕ, ∀ l, l₀ ≤ l → ∀ n, l+m₀ ≤ N n → ∀ o ∈ K,
      ∀ x y : interior (range e),
        dist x.val o ≤ (a^l)⁻¹/(2*L) → dist y.val o ≤ (a^l)⁻¹/(2*L) →
        (f n x-f n y)^2 ≤ E*M (N n-l)*
          (∑ i ∈ Finset.univ.filter (fun i =>
            (a^l)⁻¹/4 ≤ dist (p (N n) i) o ∧ dist (p (N n) i) o ≤ 4*(a^l)⁻¹),
            (ρ n i)^2) := by
  classical
  let M := fun n => CannonCells.modulus (fun i => ball (p n i) (2*(a^n)⁻¹)) (macroFamily d)
  let f := fun n => interiorScalar e he (p (N n)) ((a^(N n))⁻¹)
    (ρ n) (hρ n) (hadm n) (m n) (hm n)
  obtain ⟨E,hE,hbound⟩ := exists_scalar_annular_constant Q CP C c L hpack hCP hC hc hL hpaths
  obtain ⟨d₁,hd₁,hdiam⟩ := exists_chart_lateral_diameter e he
  obtain ⟨m₀,hm₀⟩ := exists_ratio_threshold ha (L*(L*2+1)+3) (max (C+2) (max c 1))
  have hap : 0 < a := zero_lt_one.trans ha
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hcover (k : ℕ) (x : X) : ∃ i, x ∈ ball (p k i) (2*(a^k)⁻¹) := by
    obtain ⟨i,hi⟩ := hpnet k x
    refine ⟨i,?_⟩
    rw [mem_ball,dist_comm]
    exact hi.trans_lt (by have := inv_pos.mpr (pow_pos hap k); linarith)
  refine ⟨E,hE,fun K hK hKU => ?_⟩
  obtain ⟨δ,hδ,hδU⟩ := hK.exists_thickening_subset_open isOpen_interior hKU
  have hscl := inverse_geometric_tendsto_zero ha
  have hsmall : ∀ᶠ l in atTop, 4*(a^l)⁻¹ < min δ d₁ :=
    (tendsto_const_nhds.mul hscl).eventually (gt_mem_nhds (by simpa using lt_min hδ hd₁))
  obtain ⟨l₀,hl₀⟩ := eventually_atTop.mp hsmall
  refine ⟨l₀,m₀,fun l hl n hn o ho x y hx hy => ?_⟩
  let R := (a^l)⁻¹
  let r := (a^(N n))⁻¹
  have hR : 0 < R := inv_pos.mpr (pow_pos hap l)
  have hr : 0 < r := inv_pos.mpr (pow_pos hap (N n))
  have hln : l ≤ N n := by omega
  have hrat : r/R = (a^(N n-l))⁻¹ := inverse_scale_ratio hap hln
  have hconstraints := hm₀ (N n-l) (by omega)
  rw [← hrat] at hconstraints
  have hRone : R ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ ha.le)
  have hRd : 4*R < d₁ := (hl₀ l hl).trans_le (min_le_right _ _)
  have hchart : ball o (4*R) ⊆ range e := by
    intro z hz
    apply interior_subset
    apply hδU
    exact mem_thickening_iff.mpr ⟨o,ho,
      (mem_ball.mp hz).trans ((hl₀ l hl).trans_le (min_le_left _ _))⟩
  have hrR : r ≤ R/2 := by
    have hh := (div_le_iff₀ hR).mp hconstraints.1
    linarith
  have hAr : (L*(L*2+1)+3)*r ≤ R/4 := by
    have hh := (div_le_iff₀ hR).mp (show ((L*(L*2+1)+3)*r)/R ≤ 1/4 by
      simpa only [mul_div_assoc] using hconstraints.2.1)
    linarith
  obtain ⟨h,hh,hlocal⟩ := hexp o l
  obtain ⟨_,ω,hω,hωE⟩ := sphere_macro_modulus_minimum φ d hd hdia (p (N n-l))
    ((a^(N n-l))⁻¹) (hcover (N n-l))
  have hω' : MacroscopicAdmissible (p (N n-l)) (r/R) d ω := by
    simpa only [hrat] using hω
  obtain ⟨zx,hzx⟩ := interior_subset x.property
  obtain ⟨zy,hzy⟩ := interior_subset y.property
  have hzdist : dist o (e zy) ≤ R/(2*L) := by
    rw [hzy,dist_comm]
    exact hy
  have hzero : dist o (e zx) ≤ R/(2*L) := by
    rw [hzx,dist_comm]
    exact hx
  have hlarge (u v : X) (hu : dist u o ≤ 2*R) (hv : dist v o ≤ 2*R)
      (huv : R ≤ dist u v) : d ≤ dist (h u) (h v) := by
    have hu' : dist u o ≤ 3*R := by linarith
    have hv' : dist v o ≤ 3*R := by linarith
    have hlow := (hlocal u v hu' hv').2
    calc
      d ≤ c := hdc
      _ = c/R*R := by field_simp
      _ ≤ c/R*dist u v := mul_le_mul_of_nonneg_left huv (div_nonneg hc.le hR.le)
      _ ≤ dist (h u) (h v) := hlow
  have hs : 0 < R/(2*L) := by positivity
  have hLs : L*(R/(2*L)) ≤ R/2 := by field_simp; linarith
  have hmain := hbound e he d₁ hdiam (p (N n-l)) (p (N n)) h hh o R r d (R/(2*L))
    hR hRone hRd hr hrR hAr hconstraints.2.2 hs hLs hchart
    (fun i j hij => by rw [hrat]; exact hpsep (N n-l) i j hij)
    (hpsep (N n)) (hpnet (N n))
    (fun u v hu hv => (hlocal u v hu hv).1)
    (fun u v hu hv => (hlocal u v hu hv).2) hlarge ω hω' (ρ n) (hρ n)
    (hadm n) (m n) (hm n) (hmesh n) zy zx hzdist hzero
  rw [hωE] at hmain
  have hfx : f n x = scalar (fun i => e ⁻¹' ball (p (N n) i) (2*r)) (ρ n) (m n) (hm n) zx := by
    change extend e _ x.val = _
    rw [← hzx]
    exact extend_apply e he.injective _ zx
  have hfy : f n y = scalar (fun i => e ⁻¹' ball (p (N n) i) (2*r)) (ρ n) (m n) (hm n) zy := by
    change extend e _ y.val = _
    rw [← hzy]
    exact extend_apply e he.injective _ zy
  change (f n x-f n y)^2 ≤ _
  rw [hfx,hfy]
  exact hmain

end CannonApprox

open Set Filter Topology TopologicalSpace Metric

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
