import OAI.Dynamics.EntropyCounterexample.CylinderAttraction

namespace OAI

noncomputable section

namespace Problem340

section Models

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def clockMainCylinderHomeomorph (q : ℕ) (x₀ : X) (y₀ : Y) :
    ↥(clockMainCylinder x₀ y₀ (0 : Fin (q + 1))) ≃ₜ (Fin q → Y) where
  toFun p k := p.1.2 k.succ
  invFun v := ⟨(x₀, Fin.cases y₀ v), rfl, rfl⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact p.2.1.symm
    · funext k
      refine Fin.cases ?_ (fun _ => rfl) k
      exact p.2.2.symm
  right_inv v := rfl
  continuous_toFun := by
    apply continuous_pi
    intro k
    exact (continuous_apply k.succ).comp (continuous_snd.comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk continuous_const
    apply continuous_pi
    intro k
    refine Fin.cases ?_ (fun j => ?_) k
    · exact continuous_const
    · exact continuous_apply j

def sphereVectorCylinderHomeomorph {ι : Type*} (v₀ : ι → Y) :
    ↥(sphereVectorCylinder (X := X) v₀) ≃ₜ X where
  toFun p := p.1.1
  invFun x := ⟨(x, v₀), rfl⟩
  left_inv p := by
    apply Subtype.ext
    exact Prod.ext rfl p.2.symm
  right_inv x := rfl
  continuous_toFun := continuous_fst.comp continuous_subtype_val
  continuous_invFun := by
    exact (continuous_id.prodMk continuous_const).subtype_mk _

theorem clockMainCylinder_semiconj (q : ℕ) (x₀ : X) (y₀ : Y)
    (F : X × (Fin (q + 1) → Y) → X × (Fin (q + 1) → Y)) (R : Y → Y)
    (hF : Set.MapsTo F (clockMainCylinder x₀ y₀ 0) (clockMainCylinder x₀ y₀ 0))
    (hR : ∀ p ∈ clockMainCylinder x₀ y₀ (0 : Fin (q + 1)),
      ∀ k : Fin q, (F p).2 k.succ = R (p.2 k.succ)) :
    Function.Semiconj (clockMainCylinderHomeomorph q x₀ y₀)
      (hF.restrict F _ _) (fun v k => R (v k)) := by
  intro p
  funext k
  exact hR p.1 p.2 k

theorem sphereVectorCylinder_semiconj {ι : Type*} (v₀ : ι → Y)
    (F : X × (ι → Y) → X × (ι → Y)) (g : X → X)
    (hF : Set.MapsTo F (sphereVectorCylinder v₀) (sphereVectorCylinder v₀))
    (hg : ∀ p ∈ sphereVectorCylinder v₀, (F p).1 = g p.1) :
    Function.Semiconj (sphereVectorCylinderHomeomorph (X := X) v₀)
      (hF.restrict F _ _) g := by
  intro p
  exact hg p.1 p.2

end Models

end Problem340

namespace Problem340

theorem coverEntropy_univ_eq_of_compact_homeomorph
    {X Y : Type*} [UniformSpace X] [UniformSpace Y]
    [CompactSpace X] [CompactSpace Y]
    (e : X ≃ₜ Y) (F : X → X) (G : Y → Y)
    (h : Function.Semiconj e F G) :
    Dynamics.coverEntropy F Set.univ = Dynamics.coverEntropy G Set.univ := by
  have he : e '' Set.univ = Set.univ := Set.image_univ_of_surjective e.surjective
  have hei : e.symm '' Set.univ = Set.univ := Set.image_univ_of_surjective e.symm.surjective
  have hi : Function.Semiconj e.symm G F := by
    intro y
    apply e.injective
    simpa using (h (e.symm y)).symm
  apply le_antisymm
  · simpa only [hei] using
      Dynamics.coverEntropy_image_le_of_uniformContinuous hi
        (CompactSpace.uniformContinuous_of_continuous e.symm.continuous) Set.univ
  · simpa only [he] using
      Dynamics.coverEntropy_image_le_of_uniformContinuous h
        (CompactSpace.uniformContinuous_of_continuous e.continuous) Set.univ

theorem coverEntropy_clockMainCylinder
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [T2Space X] [T2Space Y] [CompactSpace X] [CompactSpace Y]
    (q : ℕ) (x₀ : X) (y₀ : Y)
    (F : X × (Fin (q + 1) → Y) → X × (Fin (q + 1) → Y)) (R : Y → Y)
    (hF : Set.MapsTo F (clockMainCylinder x₀ y₀ 0) (clockMainCylinder x₀ y₀ 0))
    (hR : ∀ p ∈ clockMainCylinder x₀ y₀ (0 : Fin (q + 1)),
      ∀ k : Fin q, (F p).2 k.succ = R (p.2 k.succ)) :
    Dynamics.coverEntropy F (clockMainCylinder x₀ y₀ 0) =
      Dynamics.coverEntropy (fun v : Fin q → Y => fun k => R (v k)) Set.univ := by
  let : CompactSpace ↥(clockMainCylinder x₀ y₀ (0 : Fin (q + 1))) :=
    isCompact_iff_compactSpace.mp (isClosed_clockMainCylinder x₀ y₀ 0).isCompact
  rw [← Dynamics.coverEntropy_restrict hF]
  exact coverEntropy_univ_eq_of_compact_homeomorph
    (clockMainCylinderHomeomorph q x₀ y₀) _ _
    (clockMainCylinder_semiconj q x₀ y₀ F R hF hR)

theorem coverEntropy_sphereVectorCylinder
    {X Y ι : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [T2Space X] [T2Space Y] [CompactSpace X] [CompactSpace Y] [Fintype ι]
    (v₀ : ι → Y) (F : X × (ι → Y) → X × (ι → Y)) (g : X → X)
    (hF : Set.MapsTo F (sphereVectorCylinder v₀) (sphereVectorCylinder v₀))
    (hg : ∀ p ∈ sphereVectorCylinder v₀, (F p).1 = g p.1) :
    Dynamics.coverEntropy F (sphereVectorCylinder v₀) =
      Dynamics.coverEntropy g Set.univ := by
  let : CompactSpace ↥(sphereVectorCylinder (X := X) v₀) :=
    isCompact_iff_compactSpace.mp (isClosed_sphereVectorCylinder v₀).isCompact
  rw [← Dynamics.coverEntropy_restrict hF]
  exact coverEntropy_univ_eq_of_compact_homeomorph
    (sphereVectorCylinderHomeomorph (X := X) v₀) _ _
    (sphereVectorCylinder_semiconj v₀ F g hF hg)

theorem coverEntropy_attractor_union_eq_zero
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [T2Space X] [T2Space Y] [CompactSpace X] [CompactSpace Y]
    (q : ℕ) (x₀ : X) (y₀ : Y) (v₀ : Fin (q + 1) → Y)
    (F : X × (Fin (q + 1) → Y) → X × (Fin (q + 1) → Y))
    (R : Y → Y) (g : X → X)
    (hzero : Set.MapsTo F (clockMainCylinder x₀ y₀ 0) (clockMainCylinder x₀ y₀ 0))
    (hinf : Set.MapsTo F (sphereVectorCylinder v₀) (sphereVectorCylinder v₀))
    (hR : ∀ p ∈ clockMainCylinder x₀ y₀ (0 : Fin (q + 1)),
      ∀ k : Fin q, (F p).2 k.succ = R (p.2 k.succ))
    (hg : ∀ p ∈ sphereVectorCylinder v₀, (F p).1 = g p.1)
    (hREntropy : Dynamics.coverEntropy
      (fun v : Fin q → Y => fun k => R (v k)) Set.univ = 0)
    (hgEntropy : Dynamics.coverEntropy g Set.univ = 0) :
    Dynamics.coverEntropy F
      (clockMainCylinder x₀ y₀ 0 ∪ sphereVectorCylinder v₀) = 0 := by
  rw [Dynamics.coverEntropy_union,
    coverEntropy_clockMainCylinder q x₀ y₀ F R hzero hR,
    coverEntropy_sphereVectorCylinder v₀ F g hinf hg,
    hREntropy, hgEntropy, max_self]

end Problem340

end

end OAI
