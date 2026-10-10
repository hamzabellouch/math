import Mathlib
import OAI.Geometry.Cannon.Energy.PathCosts
import OAI.Geometry.Cannon.ScalarLimits.LocalOscillation

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
open Set Metric Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set unitInterval

namespace CannonApprox

open CannonGrid CannonRegularization CannonLevel CannonCells CannonBands

variable {ι : Type*} [Fintype ι]

local instance : PathConnectedSpace (Strip height (1 / 3) (2 / 3)) :=
  strip_pathConnected _ _ (by norm_num) (by norm_num) (by norm_num)

def rawFunction (C : ι → Set CannonGrid.Square) (ρ : ι → ℝ) : CannonGrid.Square → ℝ :=
  rawExtended height (1/3) (2/3) C ρ

def Admissible (C : ι → Set CannonGrid.Square) (ρ : ι → ℝ) : Prop :=
  ∀ u : Strip height (1/3) (2/3), height u.val = 1/3 →
    ∀ v : Strip height (1/3) (2/3), height v.val = 2/3 →
      ∀ p : Path u v, 1 ≤ cost (fun i => Subtype.val ⁻¹' C i) ρ (range p)

theorem rawFunction_properties (C : ι → Set CannonGrid.Square) (ρ : ι → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hcross : Admissible C ρ) :
    (∀ z, rawFunction C ρ z ∈ Icc 0 1) ∧
    (∀ z ∈ topBand, rawFunction C ρ z = 0) ∧
    (∀ z ∈ bottomBand, rawFunction C ρ z = 1) ∧
    (∀ u v, ∀ p : Path u v, |rawFunction C ρ u-rawFunction C ρ v| ≤ cost C ρ (range p)) := by
  exact rawExtended_properties height (by unfold height; fun_prop) (1/3) (2/3) (by norm_num) C ρ hρ
    (strip_top_nonempty _ _ (by norm_num) (by norm_num) (by norm_num)) hcross

def initial (C : ι → Set CannonGrid.Square) (ρ : ι → ℝ) (n : ℕ) (hn : 0 < n) :
    CannonGrid.Square → ℝ := interpolate (3*n) (by omega) (rawFunction C ρ)

def scalar (C : ι → Set CannonGrid.Square) (ρ : ι → ℝ) (n : ℕ) (hn : 0 < n) :
    CannonGrid.Square → ℝ := drain (flood (initial C ρ n hn) topBand) bottomBand

lemma initial_properties (C : ι → Set CannonGrid.Square) (ρ : ι → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hcross : Admissible C ρ) (n : ℕ) (hn : 0 < n) :
    Continuous (initial C ρ n hn) ∧ (∀ z, initial C ρ n hn z ∈ Icc 0 1) ∧
    (∀ z ∈ topBand, initial C ρ n hn z = 0) ∧
    (∀ z ∈ bottomBand, initial C ρ n hn z = 1) := by
  obtain ⟨hrange,htop,hbottom,_⟩ := rawFunction_properties C ρ hρ hcross
  have hbands := interpolate_preserves_bands n hn (rawFunction C ρ) htop hbottom
  exact ⟨continuous_interpolate _ _ _, interpolate_bounds _ _ _ hrange,hbands⟩

theorem scalar_properties (C : ι → Set CannonGrid.Square) (ρ : ι → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hcross : Admissible C ρ) (n : ℕ) (hn : 0 < n) :
    Continuous (scalar C ρ n hn) ∧ (∀ z, scalar C ρ n hn z ∈ Icc 0 1) ∧
    (∀ z ∈ topBand, scalar C ρ n hn z = 0) ∧
    (∀ z ∈ bottomBand, scalar C ρ n hn z = 1) := by
  obtain ⟨hf,hfI,hT,hB⟩ := initial_properties C ρ hρ hcross n hn
  have hF := continuous_flood topBand_pathConnected.nonempty hf (fun z => (hfI z).2)
  have hFk : ∀ z, 0 ≤ flood (initial C ρ n hn) topBand z := fun z =>
    (hfI z).1.trans (le_flood topBand_pathConnected.nonempty (fun w => (hfI w).2) z)
  exact ⟨continuous_drain bottomBand_pathConnected.nonempty hF hFk,
    regularized_values topBand_pathConnected.nonempty bottomBand_pathConnected.nonempty
      (fun z => (hfI z).1) (fun z => (hfI z).2) hT hB⟩

theorem scalar_level (C : ι → Set CannonGrid.Square) (ρ : ι → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hcross : Admissible C ρ) (n : ℕ) (hn : 0 < n)
    {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    ∃ A : Set CannonGrid.Square, IsCompact A ∧ IsConnected A ∧ A ⊆ centralRectangle ∧
      (∀ z ∈ A, scalar C ρ n hn z = t) ∧ (∃ z ∈ A, z.1 = 0) ∧ (∃ z ∈ A, z.1 = 1) ∧
      (∀ {x y : CannonGrid.Square} (p : Path x y), scalar C ρ n hn x < t →
        t < scalar C ρ n hn y → ∃ s, p s ∈ A) := by
  obtain ⟨hf,hfI,hT,hB⟩ := initial_properties C ρ hρ hcross n hn
  exact rectangle_separating_level hf (fun z => (hfI z).1) (fun z => (hfI z).2) hT hB ht.1 ht.2

theorem exists_mesh {X : Type*} [MetricSpace X] (e : CannonGrid.Square → X)
    (he : Continuous e) {r : ℝ} (hr : 0 < r) :
    ∃ n : ℕ, ∃ hn : 0 < n, ∀ z : CannonGrid.Square, ∀ i : Index (3*n),
      weight (3*n) z i ≠ 0 → dist (e z) (e (vertex (3*n) (by omega) i)) < r :=
  exists_metric_mesh e he hr

theorem scalar_local_oscillation {X : Type*} [MetricSpace X]
    (e : CannonGrid.Square → X) (he : Topology.IsEmbedding e)
    (L J r : ℝ) (hL : 1 ≤ L) (hJ : 0 < J) (hr : 0 < r)
    (hpaths : ∀ (o u v : X) (s : ℝ), 0 < s → dist o u ≤ s → dist o v ≤ s →
      JoinedIn {z | dist o z < L*s} u v)
    (x : X) (hchart : Metric.ball x (L*(L*J+1)*r) ⊆ range e)
    (q : ι → X) (ρ : ι → ℝ) (hρ : ∀ i, 0 ≤ ρ i)
    (hcross : Admissible (fun i => e ⁻¹' Metric.ball (q i) (2*r)) ρ)
    (n : ℕ) (hn : 0 < n)
    (hmesh : ∀ z : CannonGrid.Square, ∀ i : Index (3*n), weight (3*n) z i ≠ 0 →
      dist (e z) (e (vertex (3*n) (by omega) i)) < r)
    (a b : CannonGrid.Square) (ha : dist x (e a) ≤ J*r) (hb : dist x (e b) ≤ J*r) :
    let C := fun i => e ⁻¹' Metric.ball (q i) (2*r)
    |scalar C ρ n hn a-scalar C ρ n hn b| ≤
      ∑ i ∈ Finset.univ.filter (fun i => dist (q i) x ≤ (L*(L*J+1)+3)*r), ρ i := by
  let C := fun i => e ⁻¹' Metric.ball (q i) (2*r)
  obtain ⟨hrawI,_,_,hraw⟩ := rawFunction_properties C ρ hρ hcross
  exact CannonScalarLocal.local_oscillation e he L J r hL hJ hr hpaths x hchart q ρ hρ
    (rawFunction C ρ) hrawI hraw (3*n) (by omega) hmesh topBand bottomBand
    topBand_pathConnected.nonempty bottomBand_pathConnected.nonempty a b ha hb

end CannonApprox

namespace CannonRectangle

open CannonGrid CannonCells CannonBands

abbrev Middle := Strip height (1/3) (2/3)

def normalize (z : Middle) : CannonGrid.Square :=
  (z.val.1, ⟨3*(z.val.2:ℝ)-1, by
    have hz := z.property
    change (z.val.2:ℝ) ∈ Icc (1/3:ℝ) (2/3) at hz
    constructor <;> linarith [hz.1,hz.2]⟩)

lemma continuous_normalize : Continuous normalize := by
  unfold normalize
  fun_prop

lemma normalize_injective : Function.Injective normalize := by
  intro x y h
  apply Subtype.ext
  apply Prod.ext
  · simpa only [normalize] using congrArg Prod.fst h
  · apply Subtype.ext
    have hh := congrArg (fun z : CannonGrid.Square => (z.2:ℝ)) h
    change 3*(x.val.2:ℝ)-1 = 3*(y.val.2:ℝ)-1 at hh
    linarith

def leftRight : Set (Set CannonGrid.Square) :=
  {A | ∃ u v : Middle, u.val.1 = 0 ∧ v.val.1 = 1 ∧
    ∃ p : Path u v, A = Subtype.val '' range p}

def topBottom : Set (Set CannonGrid.Square) :=
  {A | ∃ u v : Middle, height u.val = 1/3 ∧ height v.val = 2/3 ∧
    ∃ p : Path u v, A = Subtype.val '' range p}

lemma leftRight_nonempty : leftRight.Nonempty := by
  let u : Middle := ⟨(0,⟨1/2,by norm_num⟩),by norm_num [height]⟩
  let v : Middle := ⟨(1,⟨1/2,by norm_num⟩),by norm_num [height]⟩
  let : PathConnectedSpace Middle := strip_pathConnected _ _ (by norm_num) (by norm_num) (by norm_num)
  exact ⟨Subtype.val '' range (PathConnectedSpace.somePath u v),
    u,v,rfl,rfl,PathConnectedSpace.somePath u v,rfl⟩

lemma leftRight_members_nonempty (A : Set CannonGrid.Square) (hA : A ∈ leftRight) :
    A.Nonempty := by
  obtain ⟨u,v,_,_,p,rfl⟩ := hA
  exact ⟨(p 0).val,⟨p 0,⟨0,rfl⟩,rfl⟩⟩

lemma crossings_intersect (A : Set CannonGrid.Square) (hA : A ∈ leftRight)
    (B : Set CannonGrid.Square) (hB : B ∈ topBottom) : (A ∩ B).Nonempty := by
  obtain ⟨u,v,hu,hv,p,rfl⟩ := hA
  obtain ⟨w,z,hw,hz,q,rfl⟩ := hB
  have hp0 : (normalize (p 0)).1 = 0 := by simpa [normalize] using hu
  have hp1 : (normalize (p 1)).1 = 1 := by simpa [normalize] using hv
  have hq0 : (normalize (q.symm 0)).2 = 1 := by
    apply Subtype.ext
    change 3*((q.symm 0).val.2:ℝ)-1 = 1
    simpa only [Path.source] using show 3*(z.val.2:ℝ)-1 = 1 by
      change (z.val.2:ℝ) = 2/3 at hz
      linarith
  have hq1 : (normalize (q.symm 1)).2 = 0 := by
    apply Subtype.ext
    change 3*((q.symm 1).val.2:ℝ)-1 = 0
    simpa only [Path.target] using show 3*(w.val.2:ℝ)-1 = 0 by
      change (w.val.2:ℝ) = 1/3 at hw
      linarith
  obtain ⟨s,t,hst⟩ := CannonPlanar.paths_cross
    (continuous_normalize.comp p.continuous) (continuous_normalize.comp q.symm.continuous)
    hp0 hp1 hq0 hq1
  have he := normalize_injective hst
  refine ⟨(p s).val,⟨p s,⟨s,rfl⟩,rfl⟩,?_⟩
  refine ⟨q.symm t,?_,congrArg Subtype.val he.symm⟩
  exact (q.symm_range ▸ mem_range_self t)

theorem exists_dual_weights {ι : Type*} [Fintype ι]
    (C : ι → Set CannonGrid.Square) (hcover : ∀ x, ∃ i, x ∈ C i) :
    0 < modulus C leftRight ∧ ∃ ρ : ι → ℝ, (∀ i, 0 ≤ ρ i) ∧
      CannonApprox.Admissible C ρ ∧ (∑ i, (ρ i)^2) = (modulus C leftRight)⁻¹ := by
  obtain ⟨hpos,_⟩ := modulus_minimum C hcover leftRight_nonempty leftRight_members_nonempty
  obtain ⟨ρ,hρ,he⟩ := transverse_weights C hcover leftRight_nonempty
    leftRight_members_nonempty crossings_intersect
  obtain ⟨hn,hadm⟩ := (admissible_iff C topBottom ρ).mp hρ
  refine ⟨hpos,ρ,hn,?_,?_⟩
  · intro u hu v hv p
    rw [cost_preimage_image]
    exact hadm _ ⟨u,v,hu,hv,p,rfl⟩
  · simpa only [EuclideanSpace.real_norm_sq_eq] using he

end CannonRectangle

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
