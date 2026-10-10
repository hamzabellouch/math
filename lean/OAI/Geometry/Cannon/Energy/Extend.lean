import Mathlib
import OAI.Geometry.Cannon.Energy.RawFunction

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
open Set unitInterval
open Set Metric Topology
open Set Topology unitInterval
open Set Filter Topology

namespace CannonChart

open Set Topology Metric

variable {X Y : Type*}

def extend (e : X → Y) (f : X → ℝ) : Y → ℝ := Function.extend e f (fun _ => 0)

lemma extend_apply (e : X → Y) (he : Function.Injective e) (f : X → ℝ) (x : X) :
    extend e f (e x) = f x := he.extend_apply f (fun _ => 0) x

lemma extend_image (e : X → Y) (he : Function.Injective e) (f : X → ℝ)
    (A : Set Y) (hA : A ⊆ range e) :
    extend e f '' A = f '' (e ⁻¹' A) := by
  ext t
  constructor
  · rintro ⟨y,hy,rfl⟩
    obtain ⟨x,rfl⟩ := hA hy
    exact ⟨x,hy,(extend_apply e he f x).symm⟩
  · rintro ⟨x,hx,rfl⟩
    exact ⟨e x,hx,extend_apply e he f x⟩

lemma continuousOn_extend [TopologicalSpace X] [TopologicalSpace Y] (e : X → Y) (he : IsEmbedding e) (f : X → ℝ)
    (hf : Continuous f) : ContinuousOn (extend e f) (range e) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hc := hf.comp he.toHomeomorph.symm.continuous
  convert hc using 1
  funext y
  obtain ⟨x,hx⟩ := y.property
  have hy : y = he.toHomeomorph x := Subtype.ext hx.symm
  subst y
  simp only [Set.domRestrict, Function.comp_apply, Homeomorph.symm_apply_apply]
  exact extend_apply e he.injective f x

end CannonChart

namespace CannonApprox

open CannonGrid CannonLevel CannonChart Metric

theorem exists_chart_lateral_diameter {X : Type*} [MetricSpace X]
    (e : CannonGrid.Square → X) (he : Topology.IsEmbedding e) :
    ∃ d₁ : ℝ, 0 < d₁ ∧ ∀ A : Set CannonGrid.Square, IsCompact A →
      (∃ x ∈ A, x.1 = 0) → (∃ x ∈ A, x.1 = 1) → d₁ ≤ diam (e '' A) := by
  let l : Set CannonGrid.Square := {z | z.1 = 0}
  let r : Set CannonGrid.Square := {z | z.1 = 1}
  have hl : IsCompact l := (isClosed_eq continuous_fst continuous_const).isCompact
  have hr : IsCompact r := (isClosed_eq continuous_fst continuous_const).isCompact
  have hdis : Disjoint (e '' l) (e '' r) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨x,hx,hxz⟩ ⟨y,hy,hyz⟩
    have hxy := he.injective (hxz.trans hyz.symm)
    have h01 : (0 : unitInterval) = 1 := hx.symm.trans ((congrArg Prod.fst hxy).trans hy)
    exact zero_ne_one h01
  obtain ⟨d,hd,hsep⟩ := Metric.exists_pos_forall_lt_edist
    (hl.image he.continuous) (hr.image he.continuous).isClosed hdis
  refine ⟨d,by exact_mod_cast hd,?_⟩
  intro A hA hAl hAr
  obtain ⟨x,hx,hxl⟩ := hAl
  obtain ⟨y,hy,hyr⟩ := hAr
  have hh := hsep (e x) ⟨x,hxl,rfl⟩ (e y) ⟨y,hyr,rfl⟩
  rw [edist_nndist] at hh
  have hdist : (d : ℝ) ≤ dist (e x) (e y) := by exact_mod_cast hh.le
  exact hdist.trans (dist_le_diam_of_mem (hA.image he.continuous).isBounded
    (mem_image_of_mem e hx) (mem_image_of_mem e hy))

theorem scalar_ambient_level {X : Type*} [MetricSpace X]
    (e : CannonGrid.Square → X) (he : Topology.IsEmbedding e)
    {ι : Type*} [Fintype ι] (C : ι → Set CannonGrid.Square) (ρ : ι → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hadm : Admissible C ρ) (n : ℕ) (hn : 0 < n)
    (d₁ : ℝ) (hd₁ : ∀ A : Set CannonGrid.Square, IsCompact A →
      (∃ x ∈ A, x.1 = 0) → (∃ x ∈ A, x.1 = 1) → d₁ ≤ diam (e '' A))
    (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
    ∃ A : Set X, IsCompact A ∧ IsConnected A ∧ A ⊆ e '' centralRectangle ∧
      d₁ ≤ diam A ∧ (∀ z ∈ A, extend e (scalar C ρ n hn) z = t) ∧
      (∀ {a b : CannonGrid.Square} (p : Path (e a) (e b)),
        (∀ s, p s ∈ range e) → scalar C ρ n hn a < t → t < scalar C ρ n hn b →
        ∃ s, p s ∈ A) := by
  obtain ⟨A,hA,hcon,hcentral,hf,hl,hr,hhit⟩ := scalar_level C ρ hρ hadm n hn ht
  refine ⟨e '' A,hA.image he.continuous,hcon.image e he.continuous.continuousOn,
    image_mono hcentral,hd₁ A hA hl hr,?_,?_⟩
  · rintro z ⟨x,hx,rfl⟩
    rw [extend_apply e he.injective]
    exact hf x hx
  · intro a b p hp ha hb
    obtain ⟨s,hs⟩ := hhit (liftPath e he p hp) ha hb
    refine ⟨s,?_⟩
    rw [← liftPath_apply e he p hp s]
    exact mem_image_of_mem e hs

end CannonApprox

open Set MeasureTheory
open scoped BigOperators
open Set unitInterval

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
