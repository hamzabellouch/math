import OAI.Geometry.NodalSets.Elliptic.SignScalePacking
import OAI.Geometry.NodalSets.Persistence.FiniteSignPersistence

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set MeasureTheory
open scoped ENNReal
noncomputable section

def LiteralNodalCertificate
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (S : Coord → ℝ)
    (Q U : Set Coord) (n : ℕ) (f : Coord → ℝ) (M : ℝ) : Prop :=
  ∃ tau rf : ℝ, 0 < tau ∧ tau < 1/4 ∧ 0 < rf ∧ rf < tau/4 ∧ rf < (1-tau)/2 ∧
    ∃ t : Finset Coord, ∃ j : t → Fin 4, ∃ u : Finset t,
      let R := fun x ↦ ((n:ℝ)*sourceSignScale g S x)⁻¹
      (↑t : Set Coord) ⊆ Q ∧
      (↑t : Set Coord).PairwiseDisjoint (fun x ↦ sourceClosedBall x (R x)) ∧
      (∀ x ∈ t, 0 < R x ∧ sourceClosedBall x (5*R x) ⊆ U) ∧
      M ≤ 2*rf^3*∑ x ∈ u, (R x)^3 ∧
      ∃ mu > 0,
        (∀ x ∈ u,
          (∀ y ∈ sourceClosedBall x (rf*R x), mu ≤ f y) ∧
          (∀ y ∈ sourceClosedBall ((x:Coord)+R x • (tau • Pi.single (j x) 1))
            (rf*R x), f y ≤ -mu)) ∧
        ∀ v : Coord → ℝ, Continuous v →
          (∀ x ∈ u, ∀ y ∈ sourceClosedBall x (rf*R x) ∪
            sourceClosedBall ((x:Coord)+R x • (tau • Pi.single (j x) 1)) (rf*R x),
            |v y-f y| < mu) →
          ENNReal.ofReal M ≤ Measure.hausdorffMeasure (4:ℝ)
            ((U ×ˢ Icc (-1:ℝ) 1) ∩ {y : Coord × ℝ | v y.1 = 0})

theorem literal_nodal_certificate_of_packing
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (S : Coord → ℝ)
    (Q U : Set Coord) (n : ℕ) (f : Coord → ℝ) (hf : Continuous f)
    (tau rf : ℝ) (ht : 0 < tau) (ht4 : tau < 1/4) (hr : 0 < rf)
    (hrt : rf < tau/4) (hr1 : rf < (1-tau)/2)
    (t : Finset Coord) (j : t → Fin 4) (u : Finset t) (M : ℝ)
    (htQ : (↑t : Set Coord) ⊆ Q)
    (hdis : (↑t : Set Coord).PairwiseDisjoint
      (fun x ↦ sourceClosedBall x (((n:ℝ)*sourceSignScale g S x)⁻¹)))
    (hU : ∀ x ∈ t, 0 < ((n:ℝ)*sourceSignScale g S x)⁻¹ ∧
      sourceClosedBall x (5*((n:ℝ)*sourceSignScale g S x)⁻¹) ⊆ U)
    (hsign : ∀ x ∈ u,
      (∀ y ∈ sourceClosedBall x (rf*((n:ℝ)*sourceSignScale g S x)⁻¹), 0 < f y) ∧
      (∀ y ∈ sourceClosedBall ((x:Coord)+((n:ℝ)*sourceSignScale g S x)⁻¹ •
        (tau • Pi.single (j x) 1)) (rf*((n:ℝ)*sourceSignScale g S x)⁻¹), f y < 0))
    (hweight : M ≤ 2*rf^3*∑ x ∈ u, (((n:ℝ)*sourceSignScale g S x)⁻¹)^3) :
    LiteralNodalCertificate g S Q U n f M := by
  let R := fun x ↦ ((n:ℝ)*sourceSignScale g S x)⁻¹
  let P := fun x : t ↦ sourceClosedBall (x:Coord) (rf*R x)
  let N := fun x : t ↦ sourceClosedBall ((x:Coord)+R x • (tau • Pi.single (j x) 1)) (rf*R x)
  have hp : ∀ y ∈ ⋃ x ∈ u, P x, 0 < f y := by
    intro y hy
    obtain ⟨x,hx,hy⟩ := mem_iUnion₂.mp hy
    exact (hsign x hx).1 y hy
  have hn : ∀ y ∈ ⋃ x ∈ u, N x, 0 < -f y := by
    intro y hy
    obtain ⟨x,hx,hy⟩ := mem_iUnion₂.mp hy
    exact neg_pos.mpr ((hsign x hx).2 y hy)
  obtain ⟨ep,hep,hpm⟩ := compact_positive_margin
    (u.isCompact_biUnion (fun x _ ↦ sourceClosedBall_isCompact _ _)) f hf.continuousOn hp
  obtain ⟨en,hen,hnm⟩ := compact_positive_margin
    (u.isCompact_biUnion (fun x _ ↦ sourceClosedBall_isCompact _ _))
    (fun y ↦ -f y) hf.neg.continuousOn hn
  obtain ⟨es,hes,hpersist⟩ := finite_sign_uniform_persistence u P N
    (fun x _ ↦ sourceClosedBall_isCompact _ _) (fun x _ ↦ sourceClosedBall_isCompact _ _) f hf hsign
  let mu := min ep (min en es)
  have hmu : 0 < mu := lt_min hep (lt_min hen hes)
  refine ⟨tau,rf,ht,ht4,hr,hrt,hr1,t,j,u,htQ,hdis,hU,hweight,mu,hmu,?_,?_⟩
  · intro x hx
    constructor
    · intro y hy
      exact (min_le_left _ _).trans (hpm y (mem_iUnion₂.mpr ⟨x,hx,hy⟩))
    · intro y hy
      have hm := hnm y (mem_iUnion₂.mpr ⟨x,hx,hy⟩)
      have hh : mu ≤ en := (min_le_right _ _).trans (min_le_left _ _)
      linarith
  · intro v hv hclose
    have hsign' := hpersist v (fun x hx y hy ↦
      (hclose x hx y hy).trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    have hdis' : (↑u : Set t).PairwiseDisjoint (fun x ↦ sourceClosedBall (x:Coord) (R x)) := by
      intro x _ y _ hxy
      exact hdis x.property y.property (fun h ↦ hxy (Subtype.ext h))
    have hU' : ∀ x ∈ u, sourceClosedBall (x:Coord) (R x) ⊆ U := by
      intro x hx y hy
      apply (hU x x.property).2
      change sourceEuclideanNorm (y-(x:Coord)) ≤ 5*R x
      exact hy.trans (by linarith [(hU x x.property).1])
    exact (ENNReal.ofReal_le_ofReal hweight).trans
      (finite_nodal_cylinder_measure u v hv (fun x : t ↦ (x:Coord)) (fun x : t ↦ R x) j
        ht.le hr.le (by linarith) (fun x _ ↦ (hU x x.property).1) hdis' hU' hsign')

theorem LiteralNodalCertificate.measure
    {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {S : Coord → ℝ}
    {Q U : Set Coord} {n : ℕ} {f : Coord → ℝ} {M : ℝ}
    (h : LiteralNodalCertificate g S Q U n f M) (hf : Continuous f) :
    ENNReal.ofReal M ≤ Measure.hausdorffMeasure (4:ℝ)
      ((U ×ˢ Icc (-1:ℝ) 1) ∩ {y : Coord × ℝ | f y.1 = 0}) := by
  obtain ⟨tau,rf,ht,ht4,hr,hrt,hr1,t,j,u,htQ,hdis,hU,hw,mu,hmu,hs,hp⟩ := h
  exact hp f hf (by intro x hx y hy; simpa using hmu)

end
end Yau.Geometry

end OAI
