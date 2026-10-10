import Mathlib
import OAI.Geometry.Cannon.Boundary.PolynomialPacking
import OAI.Geometry.Cannon.Modulus.Clip

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
section
section
section
section
section
section
section
open Set MeasureTheory
open scoped BigOperators
open Set unitInterval

namespace CannonAnnular

open Metric

noncomputable def pathCellIndices {Y β : Type*} [PseudoMetricSpace Y] [Fintype β]
    (ξ : β → Y) (s : ℝ) {u v : Y} (p : Path u v) : Finset β := by
  classical
  exact Finset.univ.filter (fun j => ∃ t, dist (p t) (ξ j) < 2*s)

def MacroscopicAdmissible {Y β : Type*} [PseudoMetricSpace Y] [Fintype β]
    (ξ : β → Y) (s d₀ : ℝ) (ω : β → ℝ) : Prop :=
  (∀ j, 0 ≤ ω j) ∧ ∀ (u v : Y) (p : Path u v),
    d₀ ≤ diam (Set.range p) → 1 ≤ ∑ j ∈ pathCellIndices ξ s p, ω j

lemma exists_outer_point {X : Type*} [PseudoMetricSpace X] (o : X) (R : ℝ)
    (hR : 0 ≤ R) {K : Set X} (hdiam : 4*R < diam K) :
    ∃ y ∈ K, 2*R ≤ dist y o := by
  by_contra hn
  push Not at hn
  have hh : diam K ≤ 4*R := by
    apply diam_le_of_forall_dist_le (by positivity)
    intro x hx y hy
    have hh := dist_triangle x o y
    rw [dist_comm o y] at hh
    linarith [hn x hx, hn y hy]
  exact (not_lt_of_ge hh) hdiam

theorem annular_interval_cover {X Y α β : Type*} [MetricSpace X] [MetricSpace Y]
    [LocallyPathConnectedSpace X] [Fintype α] [Fintype β]
    (q : α → X) (ξ : β → Y) (h : X → Y) (hh : Continuous h)
    (f : X → ℝ) (L U : α → ℝ) (o : X) (R r C d₀ a b : ℝ)
    (hR : 0 < R) (hr : 0 < r) (hrR : r ≤ R/2) (hC : 0 ≤ C)
    (hnet : ∀ y, R ≤ dist y o → dist y o ≤ 2*R → ∃ i, dist (q i) y ≤ r)
    (hzoom : ∀ u v, dist u o ≤ 3*R → dist v o ≤ 3*R →
      dist (h u) (h v) ≤ C/R * dist u v)
    (hlarge : ∀ u v, dist u o ≤ 2*R → dist v o ≤ 2*R →
      R ≤ dist u v → d₀ ≤ dist (h u) (h v))
    (hrange : ∀ i z, dist z (q i) ≤ 2*r → f z ∈ Icc (L i) (U i))
    (ω : β → ℝ) (hω : MacroscopicAdmissible ξ (r/R) d₀ ω)
    (Clevel : ℝ → Set X)
    (hlevel : ∀ t ∈ Ioo a b, IsPreconnected (Clevel t) ∧
      4*R < diam (Clevel t) ∧ (∃ x ∈ Clevel t, dist x o ≤ R/2) ∧
      ∀ z ∈ Clevel t, f z = t) :
    ∀ t ∈ Ioo a b, 1 ≤ ∑ i,
      (Icc (L i) (U i)).indicator
        (fun _ : ℝ => ∑ j ∈ Finset.univ.filter
          (fun j => dist (ξ j) (h (q i)) ≤ (C+2)*(r/R)), ω j) t := by
  classical
  intro t ht
  obtain ⟨hc, hd, ⟨x, hx, hxr⟩, hf⟩ := hlevel t ht
  obtain ⟨y, hy, hyr⟩ := exists_outer_point o R hR.le hd
  let V : Set X := ⋃ z ∈ Clevel t, ball z (r/4)
  have hV : IsOpen V := isOpen_iUnion (fun z => isOpen_iUnion (fun _ => isOpen_ball))
  have hCV : Clevel t ⊆ V := by
    intro z hz
    exact mem_iUnion.mpr ⟨z, mem_iUnion.mpr ⟨hz, by simp [hr]⟩⟩
  obtain ⟨u, v, p, hpV, hu, hv, huv, hp⟩ := annular_path_near_continuum
    o R (2*R) (by linarith) (Clevel t) V hc hV hCV hx hy (by linarith) hyr
  let p' : Path (h u) (h v) := p.map hh
  have hmacro : d₀ ≤ diam (Set.range p') := by
    have hsep := hlarge u v (by linarith) hv.le (by linarith)
    apply hsep.trans
    exact dist_le_diam_of_mem (isCompact_range p'.continuous).isBounded
      ⟨0, p'.source⟩ ⟨1, p'.target⟩
  have hadm := hω.2 (h u) (h v) p' hmacro
  apply interval_cover_of_charging _ ω L U hω.1 t (pathCellIndices ξ (r/R) p') hadm
  intro j hj
  obtain ⟨s, hs⟩ := (Finset.mem_filter.mp hj).2
  change dist (h (p s)) (ξ j) < 2*(r/R) at hs
  have hsV := hpV (Set.mem_range_self s)
  obtain ⟨z, hz⟩ := mem_iUnion.mp hsV
  obtain ⟨hzC, hzs⟩ := mem_iUnion.mp hz
  have hnear : dist z (p s) ≤ r/4 := by
    rw [mem_ball, dist_comm] at hzs
    exact hzs.le
  obtain ⟨i, _, _, hit, hij⟩ := annular_net_charge q h f L U o (p s) z (ξ j)
    R r C t hR hr.le hrR hC (hp s) (hnet (p s) (hp s).1 (hp s).2)
    hzoom (by simpa only [dist_comm] using hs.le) hnear (hf z hzC) hrange
  exact ⟨i, hit, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩⟩

end CannonAnnular

namespace CannonAnnular

open Metric

theorem annular_comparison {X Y α β γ : Type*} [MetricSpace X] [MetricSpace Y]
    [LocallyPathConnectedSpace X] [Fintype α] [Fintype β] [Fintype γ]
    (q : α → X) (ξ : β → Y) (p : γ → X) (h : X → Y) (hh : Continuous h)
    (f : X → ℝ) (L U : α → ℝ) (o : X) (R r C d d₀ a b : ℝ)
    (hR : 0 < R) (hr : 0 < r) (hrR : r ≤ R/2) (hC : 0 ≤ C)
    (hd : d ≤ R/4) (hab : a ≤ b) (hLU : ∀ i, L i ≤ U i)
    (hq : ∀ i, R/2 ≤ dist (q i) o ∧ dist (q i) o ≤ 3*R)
    (hnet : ∀ y, R ≤ dist y o → dist y o ≤ 2*R → ∃ i, dist (q i) y ≤ r)
    (hzoom : ∀ u v, dist u o ≤ 3*R → dist v o ≤ 3*R →
      dist (h u) (h v) ≤ C/R * dist u v)
    (hlarge : ∀ u v, dist u o ≤ 2*R → dist v o ≤ 2*R →
      R ≤ dist u v → d₀ ≤ dist (h u) (h v))
    (hrange : ∀ i z, dist z (q i) ≤ 2*r → f z ∈ Icc (L i) (U i))
    (ω : β → ℝ) (hω : MacroscopicAdmissible ξ (r/R) d₀ ω)
    (ρ : γ → ℝ) (hρ : ∀ j, 0 ≤ ρ j)
    (hlocal : ∀ i, U i - L i ≤ ∑ j ∈ Finset.univ.filter
      (fun j => dist (p j) (q i) ≤ d), ρ j)
    (Clevel : ℝ → Set X)
    (hlevel : ∀ t ∈ Ioo a b, IsPreconnected (Clevel t) ∧
      4*R < diam (Clevel t) ∧ (∃ x ∈ Clevel t, dist x o ≤ R/2) ∧
      ∀ z ∈ Clevel t, f z = t)
    (kr kc lr lc : ℕ)
    (hTrow : ∀ i, (Finset.univ.filter
      (fun j => dist (ξ j) (h (q i)) ≤ (C+2)*(r/R))).card ≤ kr)
    (hTcol : ∀ j, (Finset.univ.filter
      (fun i => dist (ξ j) (h (q i)) ≤ (C+2)*(r/R))).card ≤ kc)
    (hSrow : ∀ i, (Finset.univ.filter
      (fun j => dist (p j) (q i) ≤ d)).card ≤ lr)
    (hScol : ∀ j, (Finset.univ.filter
      (fun i => dist (p j) (q i) ≤ d)).card ≤ lc) :
    (b-a)^2 ≤ ((kr:ℝ)*kc*lr*lc) * (∑ j, (ω j)^2) *
      (∑ j ∈ Finset.univ.filter
        (fun j => R/4 ≤ dist (p j) o ∧ dist (p j) o ≤ 4*R), (ρ j)^2) := by
  classical
  let T (i : α) := Finset.univ.filter
    (fun j => dist (ξ j) (h (q i)) ≤ (C+2)*(r/R))
  let S (i : α) := Finset.univ.filter (fun j => dist (p j) (q i) ≤ d)
  let A := Finset.univ.filter
    (fun j => R/4 ≤ dist (p j) o ∧ dist (p j) o ≤ 4*R)
  let w (j : γ) := if j ∈ A then ρ j else 0
  have hn : ∀ j, 0 ≤ w j := by
    intro j
    dsimp [w]
    split_ifs
    · exact hρ j
    · exact le_rfl
  have hloc : ∀ i, U i - L i ≤ ∑ j ∈ S i, w j := by
    intro i
    apply (hlocal i).trans_eq
    apply Finset.sum_congr rfl
    intro j hj
    have hja : j ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      charged_center_in_annulus o (q i) (p j) R d hR.le (hq i)
        (Finset.mem_filter.mp hj).2 hd⟩
    simp [w, hja]
  have hcover := annular_interval_cover q ξ h hh f L U o R r C d₀ a b
    hR hr hrR hC hnet hzoom hlarge hrange ω hω Clevel hlevel
  have henergy := annular_energy_transfer T S ω w L U a b hab hω.1 hn hLU
    hloc kr kc lr lc hTrow (by simpa [T] using hTcol)
    hSrow (by simpa [S] using hScol) hcover
  have hwE : (∑ j, (w j)^2) = ∑ j ∈ A, (ρ j)^2 := by
    simp [w]
  rw [hwE] at henergy
  exact henergy

end CannonAnnular

open Set Metric

namespace CannonAnnular

open CannonPacking Metric

theorem exists_packed_annular_constant {X : Type*} [MetricSpace X]
    [LocallyPathConnectedSpace X] (Q : ℕ) (CP C c A : ℝ)
    (hpack : PolynomialPacking (X := X) Q CP) (hCP : 0 ≤ CP)
    (hC : 0 ≤ C) (hc : 0 < c) (hA : 0 < A) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
      (q : α → X) (ξ : β → X) (p : γ → X) (h : X → X), Continuous h →
      ∀ (f : X → ℝ) (L U : α → ℝ) (o : X) (R r d₀ a b : ℝ),
      0 < R → 0 < r → r ≤ R/2 → A*r ≤ R/4 →
      max (C+2) (max c 1)*(r/R) ≤ 1 → max A 1*r ≤ 1 →
      a ≤ b → (∀ i, L i ≤ U i) →
      (∀ i, R/2 ≤ dist (q i) o ∧ dist (q i) o ≤ 3*R) →
      (∀ i j, i ≠ j → r ≤ dist (q i) (q j)) →
      (∀ i j, i ≠ j → r/R ≤ dist (ξ i) (ξ j)) →
      (∀ i j, i ≠ j → r ≤ dist (p i) (p j)) →
      (∀ y, R ≤ dist y o → dist y o ≤ 2*R → ∃ i, dist (q i) y ≤ r) →
      (∀ u v, dist u o ≤ 3*R → dist v o ≤ 3*R →
        dist (h u) (h v) ≤ C/R * dist u v) →
      (∀ u v, dist u o ≤ 3*R → dist v o ≤ 3*R →
        c/R * dist u v ≤ dist (h u) (h v)) →
      (∀ u v, dist u o ≤ 2*R → dist v o ≤ 2*R →
        R ≤ dist u v → d₀ ≤ dist (h u) (h v)) →
      (∀ i z, dist z (q i) ≤ 2*r → f z ∈ Icc (L i) (U i)) →
      ∀ (ω : β → ℝ), MacroscopicAdmissible ξ (r/R) d₀ ω →
      ∀ (ρ : γ → ℝ), (∀ j, 0 ≤ ρ j) →
      (∀ i, U i-L i ≤ ∑ j ∈ Finset.univ.filter
        (fun j => dist (p j) (q i) ≤ A*r), ρ j) →
      ∀ (Clevel : ℝ → Set X),
      (∀ t ∈ Ioo a b, IsPreconnected (Clevel t) ∧
        4*R < diam (Clevel t) ∧ (∃ x ∈ Clevel t, dist x o ≤ R/2) ∧
        ∀ z ∈ Clevel t, f z = t) →
      (b-a)^2 ≤ E*(∑ j, (ω j)^2)*
        (∑ j ∈ Finset.univ.filter
          (fun j => R/4 ≤ dist (p j) o ∧ dist (p j) o ≤ 4*R), (ρ j)^2) := by
  classical
  have hC2 : 0 < C+2 := by linarith
  obtain ⟨kr, hkr⟩ := exists_overlap_bound Q CP (C+2) 1 hpack hCP hC2 zero_lt_one
  obtain ⟨kc, hkc⟩ := exists_overlap_bound Q CP (C+2) c hpack hCP hC2 hc
  obtain ⟨lr, hlr⟩ := exists_overlap_bound Q CP A 1 hpack hCP hA zero_lt_one
  obtain ⟨lc, hlc⟩ := exists_overlap_bound Q CP A 1 hpack hCP hA zero_lt_one
  refine ⟨(kr:ℝ)*kc*lr*lc, by positivity, ?_⟩
  intro α β γ _ _ _ q ξ p h hh f L U o R r d₀ a b hR hr hrR hAr
    hscaleT hscaleS hab hLU hq hqsep hξsep hpsep hnet hzoom hlow hlarge
    hrange ω hω ρ hρ hlocal Clevel hlevel
  have hrdiv : 0 < r/R := div_pos hr hR
  have hscale1 : max (C+2) 1*(r/R) ≤ 1 :=
    (mul_le_mul_of_nonneg_right (max_le_max le_rfl (le_max_right ..)) hrdiv.le).trans hscaleT
  have hscalec : max (C+2) c*(r/R) ≤ 1 :=
    (mul_le_mul_of_nonneg_right (max_le_max le_rfl (le_max_left ..)) hrdiv.le).trans hscaleT
  have hrow (i : α) := hkr (ι := β) ξ Finset.univ (h (q i)) (r/R) hrdiv hscale1
    (by simpa using hξsep)
  have himsep (i j : α) (hne : i ≠ j) : c*(r/R) ≤ dist (h (q i)) (h (q j)) := by
    calc
      c*(r/R) = c/R*r := by ring
      _ ≤ c/R*dist (q i) (q j) :=
        mul_le_mul_of_nonneg_left (hqsep i j hne) (div_nonneg hc.le hR.le)
      _ ≤ dist (h (q i)) (h (q j)) := hlow _ _ (hq i).2 (hq j).2
  have hcol (j : β) := hkc (ι := α) (fun i => h (q i)) Finset.univ (ξ j) (r/R)
    hrdiv hscalec (by simpa using himsep)
  have hsrow (i : α) := hlr (ι := γ) p Finset.univ (q i) r hr hscaleS
    (by simpa using hpsep)
  have hscol (j : γ) := hlc (ι := α) q Finset.univ (p j) r hr hscaleS
    (by simpa using hqsep)
  exact annular_comparison q ξ p h hh f L U o R r C (A*r) d₀ a b
    hR hr hrR hC hAr hab hLU hq hnet hzoom hlarge hrange ω hω ρ hρ hlocal
    Clevel hlevel kr kc lr lc
    (by simpa only [dist_comm] using hrow) hcol
    (by simpa only [one_mul, dist_comm] using hsrow) hscol

end CannonAnnular

end

namespace CannonCapacity

open Set Metric Finset CannonAnnular

attribute [local instance] Classical.propDecidable

lemma level_radial_hit {X : Type*} [MetricSpace X] (x : X) (K : Set X)
    (hK : IsPreconnected K) {b : ℝ} (hb : 0 ≤ b)
    (hinner : ∃ y ∈ K, dist y x ≤ b) (hdiam : 2*b < diam K) :
    ∃ w ∈ K, dist w x = b := by
  obtain ⟨y,hy,hyb⟩ := hinner
  obtain ⟨z,hz,hzb⟩ := exists_outer_point x (b/2) (by linarith) (by linarith : 4*(b/2) < diam K)
  exact hK.intermediate_value hy hz (continuous_id.dist continuous_const).continuousOn
    ⟨hyb,by dsimp; linarith⟩

theorem unmarked_level_detection {X : Type*} [MetricSpace X]
    [LocallyPathConnectedSpace X] {ι β : Type*} [Fintype ι] [Fintype β]
    (q : ι → X) (ξ : β → X) (h : X → X) (hh : Continuous h)
    (x w z : X) (A Ω K : Set X) (f : X → ℝ) (lo hi σ : ι → ℝ)
    (large : ι → Prop) (r s C d₀ b t : ℝ)
    (hr : 0 < r) (hs : 0 < s) (hrs : r ≤ s) (hC : 0 ≤ C)
    (hK : IsPreconnected K) (hwK : w ∈ K) (hdiam : 4*s < diam K)
    (hwb : dist w x = b) (hwz : dist w z ≤ s)
    (hregion : ∀ v, dist v w ≤ s → v ∈ A)
    (hdomain : ∀ v, dist v w ≤ s+r/4 → v ∈ Ω)
    (hlevel : ∀ v ∈ K, v ∈ Ω → f v = t)
    (hnet : ∀ v ∈ A, ∃ i, dist (q i) v ≤ r)
    (hupper : ∀ v v', dist v z ≤ 3*s → dist v' z ≤ 3*s →
      dist (h v) (h v') ≤ C/s*dist v v')
    (hlower : ∀ v v', dist v z ≤ 2*s → dist v' z ≤ 2*s →
      s ≤ dist v v' → d₀ ≤ dist (h v) (h v'))
    (hrange : ∀ i v, v ∈ Ω → dist v (q i) ≤ 2*r → f v ∈ Icc (lo i) (hi i))
    (ω : β → ℝ) (hω : MacroscopicAdmissible ξ (r/s) d₀ ω)
    (hσ : ∀ i, 0 ≤ σ i)
    (hpay : ∀ i, dist (q i) z ≤ 3*s →
      (∑ j ∈ univ.filter (fun j => dist (ξ j) (h (q i)) ≤ (C+2)*(r/s)), ω j) ≤ σ i)
    (hunmarked : ∀ i, large i → |dist (q i) x-b| ≤ 5*s → t ∈ Icc (lo i) (hi i) → False) :
    1 ≤ ∑ i, (Icc (lo i) (hi i)).indicator
      (fun _ : ℝ => if |dist (q i) x-b| ≤ 5*s ∧ ¬ large i then σ i else 0) t := by
  classical
  let V : Set X := ⋃ v ∈ K, ball v (r/4)
  have hV : IsOpen V := isOpen_iUnion (fun v => isOpen_iUnion (fun _ => isOpen_ball))
  have hKV : K ⊆ V := by
    intro v hv
    exact mem_iUnion.mpr ⟨v,mem_iUnion.mpr ⟨hv,by simp [hr]⟩⟩
  obtain ⟨v,hv,hvs⟩ := exists_outer_point w s hs.le hdiam
  obtain ⟨u,v',π,hπV,hu,hv',huv,hπ⟩ := annular_path_near_continuum w 0 s hs K V
    hK hV hKV hwK hv (by simp) (by linarith)
  have hzπ : ∀ a, dist (π a) z ≤ 2*s := by
    intro a
    exact (dist_triangle (π a) w z).trans (by linarith [(hπ a).2])
  let π' := π.map hh
  have hmacro : d₀ ≤ diam (range π') := by
    have h₁ : dist u z ≤ 2*s := by simpa only [π.source] using hzπ 0
    have h₂ : dist v' z ≤ 2*s := by simpa only [π.target] using hzπ 1
    exact (hlower u v' h₁ h₂ (by linarith)).trans
      (dist_le_diam_of_mem (isCompact_range π'.continuous).isBounded
        ⟨0,π'.source⟩ ⟨1,π'.target⟩)
  have hadm := hω.2 (h u) (h v') π' hmacro
  let eligible := univ.filter (fun i => |dist (q i) x-b| ≤ 5*s ∧
    ¬ large i ∧ t ∈ Icc (lo i) (hi i) ∧ dist (q i) z ≤ 3*s)
  let rel i := univ.filter (fun j => dist (ξ j) (h (q i)) ≤ (C+2)*(r/s))
  have hcharge : ∀ j ∈ pathCellIndices ξ (r/s) π', ∃ i ∈ eligible, j ∈ rel i := by
    intro j hj
    obtain ⟨a,ha⟩ := (mem_filter.mp hj).2
    obtain ⟨i,hqi⟩ := hnet (π a) (hregion _ (hπ a).2)
    have hiw : dist (q i) w ≤ r+s := (dist_triangle (q i) (π a) w).trans (by linarith [(hπ a).2])
    have hiz : dist (q i) z ≤ 3*s := (dist_triangle (q i) w z).trans (by linarith)
    obtain ⟨v',hv'⟩ := mem_iUnion.mp (hπV (mem_range_self a))
    obtain ⟨hv'K,hv'π⟩ := mem_iUnion.mp hv'
    have hv'π : dist v' (π a) < r/4 := by simpa only [mem_ball,dist_comm] using hv'π
    have hv'Ω : v' ∈ Ω := hdomain _ ((dist_triangle v' (π a) w).trans (by linarith [(hπ a).2]))
    have htv : t ∈ Icc (lo i) (hi i) := by
      rw [← hlevel v' hv'K hv'Ω]
      apply hrange i v' hv'Ω
      have hd := dist_triangle v' (π a) (q i)
      rw [dist_comm (π a) (q i)] at hd
      linarith
    have hib : |dist (q i) x-b| ≤ 5*s := by
      rw [← hwb]
      exact (abs_dist_sub_le (q i) w x).trans (by linarith)
    refine ⟨i,mem_filter.mpr ⟨mem_univ _,hib,fun hl => hunmarked i hl hib htv,htv,hiz⟩,?_⟩
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    have ht : dist (h (π a)) (h (q i)) ≤ C/s*r := by
      apply (hupper _ _ (by linarith [hzπ a]) hiz).trans
      exact mul_le_mul_of_nonneg_left (by simpa only [dist_comm] using hqi) (div_nonneg hC hs.le)
    have ha' : dist (ξ j) (h (π a)) ≤ 2*(r/s) := by
      simpa only [Path.map_coe,π',dist_comm,Function.comp_apply] using ha.le
    calc
      _ ≤ dist (ξ j) (h (π a)) + dist (h (π a)) (h (q i)) := dist_triangle _ _ _
      _ ≤ 2*(r/s)+C/s*r := add_le_add ha' ht
      _ = _ := by ring
  have hchargeSum := finite_charge_cover eligible (pathCellIndices ξ (r/s) π') rel ω hω.1 hcharge
  have hbound : (∑ i ∈ eligible, ∑ j ∈ rel i, ω j) ≤ ∑ i ∈ eligible, σ i := by
    apply sum_le_sum
    intro i hi
    exact hpay i (mem_filter.mp hi).2.2.2.2
  apply hadm.trans (hchargeSum.trans (hbound.trans _))
  rw [sum_filter]
  apply sum_le_sum
  intro i _
  by_cases he : |dist (q i) x-b| ≤ 5*s ∧ ¬ large i ∧ t ∈ Icc (lo i) (hi i) ∧ dist (q i) z ≤ 3*s
  · have hnear : |dist (q i) x-b| ≤ 5*s ∧ ¬ large i := ⟨he.1,he.2.1⟩
    simp only [ite_eq_left he,indicator_of_mem he.2.2.1,ite_eq_left hnear]
    exact le_rfl
  · rw [ite_eq_right he]
    exact Set.indicator_nonneg (fun _ _ => by split_ifs; exact hσ i; exact le_rfl) _

end CannonCapacity

end

section

namespace CannonCapacity

open Set Metric Finset CannonAnnular CannonPacking

attribute [local instance] Classical.propDecidable

lemma sparse_transfer_energy {ι β : Type*} [Fintype ι] [Fintype β]
    (f : β → ι → ℝ) (near : β → ι → Prop) (N : ℕ) (E : ℝ)
    (hsupport : ∀ z i, ¬ near z i → f z i = 0)
    (hmult : ∀ i, (univ.filter (fun z => near z i)).card ≤ N)
    (he : ∀ z, ∑ i, (f z i)^2 ≤ E) :
    (∑ i, (∑ z, f z i)^2) ≤ (N : ℝ) * Fintype.card β * E := by
  classical
  have hrow (i : ι) : (∑ z, f z i)^2 ≤ (N : ℝ)*∑ z, (f z i)^2 := by
    let S := univ.filter (fun z => near z i)
    have heq : ∑ z, f z i = ∑ z ∈ S, f z i := by
      symm
      apply sum_filter_of_ne
      intro z _ hz
      by_contra hn
      exact hz (hsupport z i hn)
    rw [heq]
    have hCS := sum_mul_sq_le_sq_mul_sq S (fun _ => (1:ℝ)) (fun z => f z i)
    simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one] at hCS
    calc
      _ ≤ (S.card : ℝ)*(∑ z ∈ S, (f z i)^2) := hCS
      _ ≤ (N : ℝ)*(∑ z, (f z i)^2) := by
        apply mul_le_mul (by exact_mod_cast hmult i)
          (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun z _ _ => sq_nonneg _))
          (sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity)
  calc
    _ ≤ ∑ i, (N : ℝ)*∑ z, (f z i)^2 := sum_le_sum (fun i _ => hrow i)
    _ = (N : ℝ)*∑ z, ∑ i, (f z i)^2 := by rw [← mul_sum,sum_comm]
    _ ≤ (N : ℝ)*∑ _z : β, E := mul_le_mul_of_nonneg_left (sum_le_sum (fun z _ => he z)) (by positivity)
    _ = _ := by simp; ring

theorem exists_local_transfer_constant {X : Type*} [MetricSpace X]
    (Q : ℕ) (CP A c : ℝ) (hpack : PolynomialPacking (X := X) Q CP)
    (hCP : 0 ≤ CP) (hA : 0 < A) (hc : 0 < c) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ {ι β : Type*} [Fintype ι] [Fintype β]
      (q : ι → X) (ξ : β → X) (h : X → X) (z : X) (r s : ℝ),
      0 < r → 0 < s → max A (max c 1)*(r/s) ≤ 1 →
      (∀ i j, i ≠ j → r ≤ dist (q i) (q j)) →
      (∀ i j, i ≠ j → r/s ≤ dist (ξ i) (ξ j)) →
      (∀ v v', dist v z ≤ 3*s → dist v' z ≤ 3*s →
        c/s*dist v v' ≤ dist (h v) (h v')) →
      ∀ ω : β → ℝ,
      (∑ i, (if dist (q i) z ≤ 3*s then
        ∑ j ∈ univ.filter (fun j => dist (ξ j) (h (q i)) ≤ A*(r/s)), ω j else 0)^2) ≤
        E*∑ j, (ω j)^2 := by
  classical
  obtain ⟨kr,hkr⟩ := exists_overlap_bound Q CP A 1 hpack hCP hA zero_lt_one
  obtain ⟨kc,hkc⟩ := exists_overlap_bound Q CP A c hpack hCP hA hc
  refine ⟨(kr:ℝ)*kc,by positivity,?_⟩
  intro ι β _ _ q ξ h z r s hr hs hscale hq hξ hlow ω
  let rel i := if dist (q i) z ≤ 3*s then
    univ.filter (fun j => dist (ξ j) (h (q i)) ≤ A*(r/s)) else ∅
  let S := univ.filter (fun i => dist (q i) z ≤ 3*s)
  have hratio : 0 < r/s := div_pos hr hs
  have hscale₁ : max A 1*(r/s) ≤ 1 :=
    (mul_le_mul_of_nonneg_right (max_le_max le_rfl (le_max_right ..)) hratio.le).trans hscale
  have hscalec : max A c*(r/s) ≤ 1 :=
    (mul_le_mul_of_nonneg_right (max_le_max le_rfl (le_max_left ..)) hratio.le).trans hscale
  have hrow (i : ι) : (rel i).card ≤ kr := by
    dsimp only [rel]
    split_ifs
    · have hh := hkr ξ univ (h (q i)) (r/s) hratio hscale₁ (by simpa using hξ)
      simpa only [dist_comm] using hh
    · simp
  have hcol (j : β) : (univ.filter (fun i => j ∈ rel i)).card ≤ kc := by
    have him : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → c*(r/s) ≤ dist (h (q i)) (h (q j)) := by
      intro i hi j hj hij
      calc
        _ = c/s*r := by ring
        _ ≤ c/s*dist (q i) (q j) := mul_le_mul_of_nonneg_left (hq i j hij) (div_nonneg hc.le hs.le)
        _ ≤ _ := hlow _ _ (mem_filter.mp hi).2 (mem_filter.mp hj).2
    have hh := hkc (fun i => h (q i)) S (ξ j) (r/s) hratio hscalec him
    convert hh using 1
    congr 1
    ext i
    by_cases hi : dist (q i) z ≤ 3*s <;> simp [S,rel,hi]
  have he := overlap_energy rel ω kr kc hrow hcol
  convert he using 1
  congr 1
  funext i
  simp only [rel]
  split_ifs <;> simp

end CannonCapacity

end

namespace CannonCapacity

open Set Metric Finset CannonAnnular

attribute [local instance] Classical.propDecidable

theorem node_separated_capacity {X : Type*} [MetricSpace X]
    [LocallyPathConnectedSpace X]
    {ι β ζ δ : Type*} [Fintype ι] [Fintype β] [Fintype ζ] [Fintype δ]
    (q : ι → X) (bin : β → ℝ) (aux : ζ → X) (ξ : δ → X)
    (h : ζ → X ≃ₜ X) (x : X) (Ω : Set X) (f : X → ℝ)
    (K : ℝ → Set X) (lo hi t : ι → ℝ)
    (a b A B₀ R r s C c d₀ H L Q E M BinMul : ℝ) (N Naux : ℕ)
    (hab : a < b) (hA : 1 ≤ A) (hAB : A+2 ≤ B₀)
    (hR : 0 < R) (hr : 0 < r) (hs : 0 < s) (hrs : r ≤ s) (hsR : s ≤ R/4)
    (hC : 0 ≤ C) (hc : 0 < c) (hdc : d₀ ≤ c)
    (hbin : ∀ j, (A+1)*R ≤ bin j ∧ bin j ≤ (B₀-1)*R)
    (hnet : ∀ v, (A-1)*R ≤ dist v x → dist v x ≤ (B₀+1)*R →
      ∃ i, dist (q i) v ≤ r)
    (haux : ∀ v, (A-1)*R ≤ dist v x → dist v x ≤ (B₀+1)*R →
      ∃ z, dist v (aux z) ≤ s)
    (hΩ : ∀ v, dist v x ≤ (B₀+2)*R → v ∈ Ω)
    (hK : ∀ v ∈ Ioo a b, IsPreconnected (K v))
    (hinner : ∀ v ∈ Ioo a b, ∃ y ∈ K v, dist y x ≤ A*R)
    (hdiam : ∀ v ∈ Ioo a b, 2*B₀*R < diam (K v))
    (hlevel : ∀ v ∈ Ioo a b, ∀ y ∈ K v, y ∈ Ω → f y = v)
    (hlohi : ∀ i, lo i ≤ hi i) (ht : ∀ i, 0 ≤ t i)
    (hlen : ∀ i, clip a b (hi i)-clip a b (lo i) = (b-a)*t i)
    (hrange : ∀ i v, v ∈ Ω → dist v (q i) ≤ 2*r → f v ∈ Icc (lo i) (hi i))
    (hupper : ∀ z v v', dist v (aux z) ≤ 3*s → dist v' (aux z) ≤ 3*s →
      dist (h z v) (h z v') ≤ C/s*dist v v')
    (hlower : ∀ z v v', dist v (aux z) ≤ 3*s → dist v' (aux z) ≤ 3*s →
      c/s*dist v v' ≤ dist (h z v) (h z v'))
    (ω : δ → ℝ) (hω : MacroscopicAdmissible ξ (r/s) d₀ ω)
    (hωmass : ∑ j, (ω j)^2 ≤ M)
    (hlocal : ∀ z, (∑ i, (if dist (q i) (aux z) ≤ 3*s then
      ∑ j ∈ univ.filter (fun j => dist (ξ j) (h z (q i)) ≤ (C+2)*(r/s)), ω j else 0)^2)
      ≤ E*∑ j, (ω j)^2)
    (hmultaux : ∀ i, (univ.filter (fun z => dist (q i) (aux z) ≤ 3*s)).card ≤ Naux)
    (hL : 0 < L) (hQ : 0 < Q) (hE : 0 ≤ E) (hM : 0 ≤ M)
    (hBinMul : 0 < BinMul) (hHr : 0 ≤ H*r) (hN : 0 < N)
    (hdegree : ∀ i, (univ.filter (fun j => dist (q i) (q j) ≤ H*r)).card ≤ N)
    (hmult : ∀ i, ((univ.filter (fun j => |dist (q i) x-bin j| ≤ 5*s)).card : ℝ) ≤ BinMul)
    (hlarge : 2*BinMul*N ≤ L*Fintype.card β)
    (hsmall : 4*BinMul^2*((Naux:ℝ)*Fintype.card ζ*(E*M))*N < Q*(Fintype.card β : ℝ)^2) :
    ∃ S : Finset ι, (∀ i ∈ S, ∀ j ∈ S, i ≠ j → H*r < dist (q i) (q j)) ∧
      1 ≤ ∑ i ∈ S, min (L*t i) (Q*(t i)^2) := by
  classical
  let σz : ζ → ι → ℝ := fun z i => if dist (q i) (aux z) ≤ 3*s then
    ∑ j ∈ univ.filter (fun j => dist (ξ j) (h z (q i)) ≤ (C+2)*(r/s)), ω j else 0
  let σ : ι → ℝ := fun i => ∑ z, σz z i
  have hσz : ∀ z i, 0 ≤ σz z i := by
    intro z i
    dsimp only [σz]
    split_ifs
    · exact sum_nonneg (fun j _ => hω.1 j)
    · exact le_rfl
  have hσ : ∀ i, 0 ≤ σ i := fun i => sum_nonneg (fun z _ => hσz z i)
  have he := sparse_transfer_energy σz (fun z i => dist (q i) (aux z) ≤ 3*s) Naux (E*M)
    (by intro z i hn; simp only [σz,ite_eq_right hn]) hmultaux
    (fun z => (hlocal z).trans (mul_le_mul_of_nonneg_left hωmass hE))
  apply separated_capacity_of_detection q lo hi t σ
    (fun j i => |dist (q i) x-bin j| ≤ 5*s) a b BinMul L Q
    ((Naux:ℝ)*Fintype.card ζ*(E*M)) H r N hab hlohi ht hlen hσ hL hQ hBinMul
    (by positivity) hHr hN hdegree hmult he hlarge hsmall
  intro j v hv hunmarked
  have hbnon : 0 ≤ bin j := by nlinarith only [(hbin j).1,hA,hR]
  obtain ⟨w,hwK,hwb⟩ := level_radial_hit x (K v) (hK v hv) hbnon (by
    obtain ⟨y,hy,hyA⟩ := hinner v hv
    exact ⟨y,hy,by nlinarith only [(hbin j).1,hyA,hR]⟩) (by nlinarith only [hdiam v hv,(hbin j).2,hR])
  have hwann : (A-1)*R ≤ dist w x ∧ dist w x ≤ (B₀+1)*R := by
    rw [hwb]
    constructor <;> nlinarith only [(hbin j).1,(hbin j).2,hR]
  obtain ⟨z,hwz⟩ := haux w hwann.1 hwann.2
  apply unmarked_level_detection q ξ (h z) (h z).continuous x w (aux z)
    {v | (A-1)*R ≤ dist v x ∧ dist v x ≤ (B₀+1)*R} Ω (K v) f lo hi σ
    (fun i => L ≤ Q*t i) r s C d₀ (bin j) v hr hs hrs hC (hK v hv) hwK
    (by nlinarith only [hdiam v hv,hAB,hA,hR,hsR]) hwb hwz
    (by
      intro y hy
      have hyw := dist_triangle y w x
      have hwy := dist_triangle w y x
      rw [dist_comm w y] at hwy
      constructor <;> nlinarith only [(hbin j).1,(hbin j).2,hy,hyw,hwy,hwb,hsR,hR])
    (by
      intro y hy
      apply hΩ
      have hh := dist_triangle y w x
      nlinarith only [(hbin j).2,hh,hy,hwb,hsR,hrs,hR])
    (hlevel v hv) (by intro y hy; exact hnet y hy.1 hy.2)
    (hupper z)
    (by
      intro y y' hy hy' hyy'
      have hh := hlower z y y' (by linarith only [hy,hs]) (by linarith only [hy',hs])
      have hsne : s ≠ 0 := ne_of_gt hs
      have hcs : c/s*s = c := by field_simp
      have hm := mul_le_mul_of_nonneg_left hyy' (div_nonneg hc.le hs.le)
      rw [hcs] at hm
      exact hdc.trans (hm.trans hh))
    hrange ω hω hσ (by
      intro i hi
      have hh : σz z i ≤ σ i := single_le_sum (fun z _ => hσz z i) (mem_univ z)
      simpa only [σz,ite_eq_left hi] using hh)
    hunmarked

end CannonCapacity

end

section

namespace CannonCapacity

open Set Metric Finset CannonAnnular CannonPacking

attribute [local instance] Classical.propDecidable

end CannonCapacity

end

end
end
end
end
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
