import Mathlib
import OAI.Geometry.Cannon.ScalarLimits.LaterRecord
import OAI.Geometry.Cannon.Modulus.ScalarAnnularConstant
import OAI.Geometry.Cannon.Energy.SquareMapRange
import OAI.Geometry.Cannon.ScalarLimits.Osc
import OAI.Geometry.Cannon.Conformal.SpherePathConnected
import OAI.Geometry.Cannon.Energy.Interior

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

namespace CannonScales

lemma inverse_scale_ratio {a : ℝ} (ha : 0 < a) {N l : ℕ} (hl : l ≤ N) :
    (a^N)⁻¹/(a^l)⁻¹ = (a^(N-l))⁻¹ := by
  have hp : a^N = a^(N-l)*a^l := by rw [← pow_add,Nat.sub_add_cancel hl]
  rw [hp,mul_inv]
  field_simp

lemma exists_ratio_threshold {a : ℝ} (ha : 1 < a) (A B : ℝ) :
    ∃ m₀ : ℕ, ∀ m, m₀ ≤ m →
      (a^m)⁻¹ ≤ 1/2 ∧ A*(a^m)⁻¹ ≤ 1/4 ∧ B*(a^m)⁻¹ ≤ 1 := by
  have hzero := inverse_geometric_tendsto_zero ha
  have h₁ : ∀ᶠ m in Filter.atTop, (a^m)⁻¹ < 1/2 :=
    hzero.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/2))
  have h₂ : ∀ᶠ m in Filter.atTop, A*(a^m)⁻¹ < 1/4 :=
    (tendsto_const_nhds.mul hzero).eventually (gt_mem_nhds (by simp))
  have h₃ : ∀ᶠ m in Filter.atTop, B*(a^m)⁻¹ < 1 :=
    (tendsto_const_nhds.mul hzero).eventually (gt_mem_nhds (by simp))
  obtain ⟨m₀,hm₀⟩ := Filter.eventually_atTop.mp (h₁.and (h₂.and h₃))
  exact ⟨m₀,fun m hm => ⟨(hm₀ m hm).1.le,(hm₀ m hm).2.1.le,(hm₀ m hm).2.2.le⟩⟩

end CannonScales

namespace CannonApprox

open CannonGrid CannonChart CannonCharts CannonScales CannonPacking CannonAnnular
open Set Metric Filter Topology

def interiorScalar {X ι : Type*} [MetricSpace X] [Fintype ι]
    (e : Square → X) (he : IsEmbedding e) (p : ι → X) (r : ℝ)
    (ρ : ι → ℝ) (hρ : ∀ i, 0 ≤ ρ i)
    (hadm : Admissible (fun i => e ⁻¹' ball (p i) (2*r)) ρ) (m : ℕ) (hm : 0 < m) :
    C(interior (range e),ℝ) :=
  onInterior e he ⟨scalar (fun i => e ⁻¹' ball (p i) (2*r)) ρ m hm,
    (scalar_properties _ ρ hρ hadm m hm).1⟩

theorem geometric_annular_tails {X : Type*} [MetricSpace X] [CompactSpace X]
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
    ∃ E : ℝ, 0 ≤ E ∧ ∀ x : interior (range e), ∃ l₀ m₀ : ℕ,
      ∀ l, l₀ ≤ l → ∀ n, l+m₀ ≤ N n → ∀ y : interior (range e),
        dist y x < (a^l)⁻¹/(2*L) →
        (f n x-f n y)^2 ≤ E*M (N n-l)*
          (∑ i ∈ Finset.univ.filter (fun i =>
            (a^l)⁻¹/4 ≤ dist (p (N n) i) x.val ∧ dist (p (N n) i) x.val ≤ 4*(a^l)⁻¹),
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
  refine ⟨E,hE,fun x => ?_⟩
  obtain ⟨δ,hδ,hδball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp x.property)
  have hscl := inverse_geometric_tendsto_zero ha
  have hsmall : ∀ᶠ l in atTop, 4*(a^l)⁻¹ < min δ d₁ :=
    (tendsto_const_nhds.mul hscl).eventually (gt_mem_nhds (by simpa using lt_min hδ hd₁))
  obtain ⟨l₀,hl₀⟩ := eventually_atTop.mp hsmall
  refine ⟨l₀,m₀,fun l hl n hn y hy => ?_⟩
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
  have hchart : ball x.val (4*R) ⊆ range e := by
    intro z hz
    apply hδball
    exact (mem_ball.mp hz).trans ((hl₀ l hl).trans_le (min_le_left _ _))
  have hrR : r ≤ R/2 := by
    have hh := (div_le_iff₀ hR).mp hconstraints.1
    linarith
  have hAr : (L*(L*2+1)+3)*r ≤ R/4 := by
    have hh := (div_le_iff₀ hR).mp (show ((L*(L*2+1)+3)*r)/R ≤ 1/4 by
      simpa only [mul_div_assoc] using hconstraints.2.1)
    linarith
  obtain ⟨h,hh,hlocal⟩ := hexp x.val l
  obtain ⟨_,ω,hω,hωE⟩ := sphere_macro_modulus_minimum φ d hd hdia (p (N n-l))
    ((a^(N n-l))⁻¹) (hcover (N n-l))
  have hω' : MacroscopicAdmissible (p (N n-l)) (r/R) d ω := by
    simpa only [hrat] using hω
  obtain ⟨zx,hzx⟩ := interior_subset x.property
  obtain ⟨zy,hzy⟩ := interior_subset y.property
  have hzdist : dist x.val (e zy) ≤ R/(2*L) := by
    rw [hzy,dist_comm]
    exact hy.le
  have hzero : dist x.val (e zx) ≤ R/(2*L) := by rw [hzx,dist_self]; positivity
  have hlarge (u v : X) (hu : dist u x.val ≤ 2*R) (hv : dist v x.val ≤ 2*R)
      (huv : R ≤ dist u v) : d ≤ dist (h u) (h v) := by
    have hu' : dist u x.val ≤ 3*R := by linarith
    have hv' : dist v x.val ≤ 3*R := by linarith
    have hlow := (hlocal u v hu' hv').2
    calc
      d ≤ c := hdc
      _ = c/R*R := by field_simp
      _ ≤ c/R*dist u v := mul_le_mul_of_nonneg_left huv (div_nonneg hc.le hR.le)
      _ ≤ dist (h u) (h v) := hlow
  have hs : 0 < R/(2*L) := by positivity
  have hLs : L*(R/(2*L)) ≤ R/2 := by field_simp; linarith
  have hmain := hbound e he d₁ hdiam (p (N n-l)) (p (N n)) h hh x.val R r d (R/(2*L))
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

namespace CannonApprox

open CannonGrid CannonCharts CannonCells CannonPacking CannonChart
open Set Metric Filter Topology MeasureTheory

theorem geometric_scalar_limit {X : Type*} [MetricSpace X] [CompactSpace X]
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
    (lam : ℝ) (hlam : 1 ≤ lam)
    (hunbounded : ∀ B : ℝ, ∃ n,
      B < modulus (fun i => ball (p n i) (2*(a^n)⁻¹)) (macroFamily d)/lam^n) :
    let M := fun n => modulus (fun i => ball (p n i) (2*(a^n)⁻¹)) (macroFamily d)
    ∃ e : Plane → X, ∃ he : IsOpenEmbedding e,
      ∃ A : ℝ, 0 < A ∧ ∃ N : ℕ → ℕ, StrictMono N ∧ Tendsto (M ∘ N) atTop atTop ∧
        (∀ j l, l ≤ N j → M (N j-l) ≤ (lam^l)⁻¹*M (N j)) ∧
        ∃ ρ : (j : ℕ) → ι (N j) → ℝ, ∃ m : ℕ → ℕ, ∃ hm : ∀ j, 0 < m j,
        ∃ hρ : ∀ j i, 0 ≤ ρ j i,
        ∃ hadm : ∀ j, Admissible
            (fun i => (e ∘ squareMap) ⁻¹' ball (p (N j) i) (2*(a^(N j))⁻¹)) (ρ j),
          (∀ j, (∑ i, (ρ j i)^2) ≤ A/M (N j)) ∧
          (∀ j z, ∀ i : Index (3*m j), weight (3*m j) z i ≠ 0 →
            dist ((e ∘ squareMap) z)
              ((e ∘ squareMap) (vertex (3*m j) (by have := hm j; omega) i)) < (a^(N j))⁻¹) ∧
          let f := fun j => interiorScalar (e ∘ squareMap)
            (he.isEmbedding.comp squareMap_embedding) (p (N j)) ((a^(N j))⁻¹)
            (ρ j) (hρ j) (hadm j) (m j) (hm j)
          let μ := fun j => CannonAtomic.atomic (p (N j)) (ρ j) (M (N j))
            (by
              apply Real.sInf_nonneg
              rintro t ⟨w,_,rfl⟩
              exact sq_nonneg _)
          ∃ u : C(interior (range (e ∘ squareMap)), ℝ),
            (∀ x, u x ∈ Icc (0 : ℝ) 1) ∧
            (∃ top bot, u top = 0 ∧ u bot = 1) ∧
            ∃ ν : FiniteMeasure X, (ν.mass : ℝ) ≤ A ∧ ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
              Tendsto (f ∘ ψ) atTop (𝓝 u) ∧ Tendsto (μ ∘ ψ) atTop (𝓝 ν) := by
  classical
  let M := fun n => modulus (fun i => ball (p n i) (2*(a^n)⁻¹)) (macroFamily d)
  have hap : 0 < a := zero_lt_one.trans ha
  have hr (n : ℕ) : 0 < (a^n)⁻¹ := inv_pos.mpr (pow_pos hap n)
  have hcover (n : ℕ) (x : X) : ∃ i, x ∈ ball (p n i) (2*(a^n)⁻¹) := by
    obtain ⟨i,hi⟩ := hpnet n x
    exact ⟨i, show dist x (p n i) < 2*(a^n)⁻¹ by
      rw [dist_comm]; linarith [hr n]⟩
  have hM (n : ℕ) : 0 < M n :=
    (sphere_macro_modulus_minimum φ d hd hdia (p n) ((a^n)⁻¹) (hcover n)).1
  obtain ⟨e,he,A,hA,N,hN,hNM,hrec,ρ,m,hm,hdata⟩ :=
    record_scalar_sequence φ d hd ι p (fun n => (a^n)⁻¹) hr hcover hM lam hlam hunbounded
  let E := e ∘ squareMap
  have hE : IsEmbedding E := he.isEmbedding.comp squareMap_embedding
  have hρ (j : ℕ) := (hdata j).1
  have hadm (j : ℕ) := (hdata j).2.1
  have henergy (j : ℕ) := (hdata j).2.2.1
  have hmesh (j : ℕ) := (hdata j).2.2.2
  let f := fun j => interiorScalar E hE (p (N j)) ((a^(N j))⁻¹)
    (ρ j) (hρ j) (hadm j) (m j) (hm j)
  obtain ⟨B,hB,hann⟩ := geometric_annular_tails φ d hd hdia a ha Q CP C c L
    hpack hCP hC hc hL hdc hpaths hexp ι p hpsep hpnet E hE N ρ hρ hadm m hm hmesh
  have hf (j : ℕ) (x : interior (range E)) : f j x ∈ Icc (0:ℝ) 1 := by
    obtain ⟨z,hz⟩ := interior_subset x.property
    change extend E _ x.val ∈ _
    rw [← hz,extend_apply E hE.injective]
    exact (scalar_properties _ (ρ j) (hρ j) (hadm j) (m j) (hm j)).2.1 z
  let zt : Square := (⟨1/2,by norm_num⟩,⟨1/6,by norm_num⟩)
  let zb : Square := (⟨1/2,by norm_num⟩,⟨5/6,by norm_num⟩)
  have hzt : E zt ∈ interior (range E) := chart_square_interior e he
    (by norm_num [zt]) (by norm_num [zt])
  have hzb : E zb ∈ interior (range E) := chart_square_interior e he
    (by norm_num [zb]) (by norm_num [zb])
  let top : interior (range E) := ⟨E zt,hzt⟩
  let bot : interior (range E) := ⟨E zb,hzb⟩
  have htop (j : ℕ) : f j top = 0 := by
    change extend E _ (E zt) = _
    rw [extend_apply E hE.injective]
    apply (scalar_properties _ (ρ j) (hρ j) (hadm j) (m j) (hm j)).2.2.1
    norm_num [zt,CannonLevel.topBand]
  have hbot (j : ℕ) : f j bot = 1 := by
    change extend E _ (E zb) = _
    rw [extend_apply E hE.injective]
    apply (scalar_properties _ (ρ j) (hρ j) (hadm j) (m j) (hm j)).2.2.2
    norm_num [zb,CannonLevel.bottomBand]
  have hrec' (j l : ℕ) (hl : l ≤ N j) : M (N j-l) ≤ M (N j) := by
    have hle : (lam^l)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hlam)
    exact (hrec j l hl).trans (by nlinarith [hM (N j)])
  obtain ⟨u,hu,hut,hub,ν,hν,ψ,hψ,hfconv,hμconv⟩ :=
    CannonScalarLimit.atomic_record_limit (interior (range E)) isOpen_interior
      (fun j => ι (N j)) (fun j => p (N j)) ρ f N hN M hM a L B A ha
      (zero_lt_one.trans_le hL) hB hA.le henergy hrec' hann hf top bot htop hbot
  exact ⟨e,he,A,hA,N,hN,hNM,hrec,ρ,m,hm,hρ,hadm,henergy,hmesh,
    u,hu,⟨top,bot,hut,hub⟩,ν,hν,ψ,hψ,hfconv,hμconv⟩

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
