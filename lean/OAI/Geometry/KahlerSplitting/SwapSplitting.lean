import OAI.Geometry.KahlerSplitting.FixedManifolds

namespace OAI

section

noncomputable section
open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n}

lemma HolomorphicSplitting.complement_range (S : HolomorphicSplitting X r s) (x : X.Carrier) :
    LinearMap.range (complementaryProjection S x).toLinearMap = LinearMap.ker (S.projection x).toLinearMap := by
  ext v
  constructor
  · rintro ⟨w,rfl⟩
    change S.projection x (w-S.projection x w)=0
    rw [map_sub,S.idempotent,sub_self]
  · intro hv
    refine ⟨v,?_⟩
    change v-S.projection x v=v
    change S.projection x v=0 at hv
    rw [hv,sub_zero]

lemma HolomorphicSplitting.complement_ker (S : HolomorphicSplitting X r s) (x : X.Carrier) :
    LinearMap.ker (complementaryProjection S x).toLinearMap = LinearMap.range (S.projection x).toLinearMap := by
  ext v
  constructor
  · intro hv
    change v-S.projection x v=0 at hv
    exact ⟨v,(sub_eq_zero.mp hv).symm⟩
  · rintro ⟨w,rfl⟩
    change S.projection x w-S.projection x (S.projection x w)=0
    rw [S.idempotent,sub_self]

def HolomorphicSplitting.swap (S : HolomorphicSplitting X r s) : HolomorphicSplitting X s r where
  projection := complementaryProjection S
  idempotent := by
    intro x v
    change v-S.projection x v-S.projection x (v-S.projection x v)=v-S.projection x v
    rw [map_sub,S.idempotent,sub_self,sub_zero]
  holomorphic := S.complement_holomorphic
  first_rank := fun x ↦ by
    rw [S.complement_range x]
    exact S.second_rank x
  second_rank := fun x ↦ by
    rw [S.complement_ker x]
    exact S.first_rank x

lemma complementaryProjection_swap (S : HolomorphicSplitting X r s) :
    complementaryProjection S.swap=S.projection := by
  funext x
  change ContinuousLinearMap.id ℂ (Tangent X x)-(ContinuousLinearMap.id ℂ (Tangent X x)-S.projection x)=_
  exact sub_sub_cancel _ _

variable {S : HolomorphicSplitting X r s}

def SplittingChart.swapChart (e : SplittingChart S) :
    OpenPartialHomeomorph X.Carrier (Model s × Model r) where
  toFun := fun x ↦ (e.chart x).swap
  invFun := fun z ↦ e.chart.symm z.swap
  source := e.chart.source
  target := ball 0 e.radius ×ˢ ball 0 e.radius
  map_source' := by intro x hx; have h := e.chart.map_source hx; rw [e.product_range] at h; exact ⟨h.2,h.1⟩
  map_target' := by intro z hz; apply e.chart.map_target; rw [e.product_range]; exact ⟨hz.2,hz.1⟩
  left_inv' := by intro x hx; exact e.chart.left_inv hx
  right_inv' := by
    intro z hz
    have ht : z.swap ∈ e.chart.target := by rw [e.product_range]; exact ⟨hz.2,hz.1⟩
    exact congrArg Prod.swap (e.chart.right_inv ht)
  open_source := e.chart.open_source
  open_target := isOpen_ball.prod isOpen_ball
  continuousOn_toFun := continuous_swap.comp_continuousOn e.chart.continuousOn
  continuousOn_invFun := e.chart.continuousOn_symm.comp continuous_swap.continuousOn (by
    intro z hz; rw [e.product_range]; exact ⟨hz.2,hz.1⟩)

lemma SplittingChart.swapChart_holomorphic (e : SplittingChart S) :
    MDifferentiableOn (model n) 𝓘(ℂ,Model s × Model r) e.swapChart e.chart.source := by
  intro x hx
  exact (mdifferentiableAt_iff_differentiableAt.mpr
    (ContinuousLinearEquiv.prodComm ℂ (Model r) (Model s)).differentiableAt).comp_mdifferentiableWithinAt x
    (e.holomorphic x hx)

lemma SplittingChart.swapChart_derivative (e : SplittingChart S) {x : X.Carrier}
    (hx : x ∈ e.chart.source) (v : Tangent X x) :
    mfderiv (model n) 𝓘(ℂ,Model s × Model r) e.swapChart x v=
      (mfderiv (model n) 𝓘(ℂ,Model r × Model s) e.chart x v).swap := by
  let c := ContinuousLinearEquiv.prodComm ℂ (Model r) (Model s)
  have h := mfderiv_comp (I := model n) (I' := 𝓘(ℂ,Model r × Model s))
    (I'' := 𝓘(ℂ,Model s × Model r)) x
    (mdifferentiableAt_iff_differentiableAt.mpr c.differentiableAt)
    (e.holomorphic.mdifferentiableAt (e.chart.open_source.mem_nhds hx))
  change mfderiv (model n) 𝓘(ℂ,Model s × Model r) e.swapChart x = _ at h
  rw [mfderiv_eq_fderiv,c.hasFDerivAt.fderiv] at h
  exact congrArg (fun L : Model n →L[ℂ] (Model s × Model r) ↦ L v) h

def SplittingChart.swap (e : SplittingChart S) : SplittingChart S.swap where
  chart := e.swapChart
  radius := e.radius
  radius_pos := e.radius_pos
  product_range := rfl
  holomorphic := e.swapChart_holomorphic
  inverse_holomorphic := by
    intro z hz
    have ht : z.swap ∈ e.chart.target := by rw [e.product_range]; exact ⟨hz.2,hz.1⟩
    exact (e.inverse_holomorphic.mdifferentiableAt (e.chart.open_target.mem_nhds ht)).comp_mdifferentiableWithinAt z
      (mdifferentiableAt_iff_differentiableAt.mpr
        (ContinuousLinearEquiv.prodComm ℂ (Model s) (Model r)).differentiableAt).mdifferentiableWithinAt
  horizontal := by
    intro x hx v
    rw [e.swapChart_derivative hx]
    change v-S.projection x v=v ↔ _
    exact sub_eq_self.trans (e.vertical x hx v)
  vertical := by
    intro x hx v
    rw [e.swapChart_derivative hx]
    change v-S.projection x v=0 ↔ _
    exact sub_eq_zero.trans (eq_comm.trans (e.horizontal x hx v))

end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Filter Topology Metric
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X Z : ComplexManifold n} {S : HolomorphicSplitting X r s}
    {π : OrdinaryUniversalCover X Z}

lemma HolomorphicSplitting.swap_swap (S : HolomorphicSplitting X r s) : S.swap.swap=S := by
  cases S
  simp only [HolomorphicSplitting.swap]
  congr 1
  funext x
  exact sub_sub_cancel _ _

def CoverProductChart.swapChart (e : CoverProductChart π S) :
    OpenPartialHomeomorph Z.Carrier (Model s × Model r) where
  toFun := fun x ↦ (e.chart x).swap
  invFun := fun z ↦ e.chart.symm z.swap
  source := e.chart.source
  target := ball 0 e.radius ×ˢ ball 0 e.radius
  map_source' := by intro x hx; have h := e.chart.map_source hx; rw [e.product_range] at h; exact ⟨h.2,h.1⟩
  map_target' := by intro z hz; apply e.chart.map_target; rw [e.product_range]; exact ⟨hz.2,hz.1⟩
  left_inv' := by intro x hx; exact e.chart.left_inv hx
  right_inv' := by
    intro z hz
    have ht : z.swap ∈ e.chart.target := by rw [e.product_range]; exact ⟨hz.2,hz.1⟩
    exact congrArg Prod.swap (e.chart.right_inv ht)
  open_source := e.chart.open_source
  open_target := isOpen_ball.prod isOpen_ball
  continuousOn_toFun := continuous_swap.comp_continuousOn e.chart.continuousOn
  continuousOn_invFun := e.chart.continuousOn_symm.comp continuous_swap.continuousOn (by
    intro z hz; rw [e.product_range]; exact ⟨hz.2,hz.1⟩)

def CoverProductChart.swap (e : CoverProductChart π S) : CoverProductChart π S.swap where
  chart := e.swapChart
  radius := e.radius
  radius_pos := e.radius_pos
  product_range := rfl
  holomorphic := by
    intro x hx
    exact (mdifferentiableAt_iff_differentiableAt.mpr
      (ContinuousLinearEquiv.prodComm ℂ (Model r) (Model s)).differentiableAt).comp_mdifferentiableWithinAt x
      (e.holomorphic x hx)
  inverse_holomorphic := by
    intro z hz
    have ht : z.swap ∈ e.chart.target := by rw [e.product_range]; exact ⟨hz.2,hz.1⟩
    exact (e.inverse_holomorphic.mdifferentiableAt (e.chart.open_target.mem_nhds ht)).comp_mdifferentiableWithinAt z
      (mdifferentiableAt_iff_differentiableAt.mpr
        (ContinuousLinearEquiv.prodComm ℂ (Model s) (Model r)).differentiableAt).mdifferentiableWithinAt
  downstairs := e.downstairs.swap
  maps := e.maps
  coordinates := fun z hz ↦ congrArg Prod.swap (e.coordinates z hz)

lemma CoverProductChart.swap_derivative (e : CoverProductChart π S) {z : Z.Carrier}
    (hz : z ∈ e.chart.source) (v : Tangent Z z) :
    mfderiv (model n) 𝓘(ℂ,Model s × Model r) e.swap.chart z v=
      (mfderiv (model n) 𝓘(ℂ,Model r × Model s) e.chart z v).swap := by
  let c := ContinuousLinearEquiv.prodComm ℂ (Model r) (Model s)
  have h := mfderiv_comp (I := model n) (I' := 𝓘(ℂ,Model r × Model s))
    (I'' := 𝓘(ℂ,Model s × Model r)) z
    (mdifferentiableAt_iff_differentiableAt.mpr c.differentiableAt)
    (e.holomorphic.mdifferentiableAt (e.chart.open_source.mem_nhds hz))
  change mfderiv (model n) 𝓘(ℂ,Model s × Model r) e.swap.chart z = _ at h
  rw [mfderiv_eq_fderiv,c.hasFDerivAt.fderiv] at h
  exact congrArg (fun L : Model n →L[ℂ] (Model s × Model r) ↦ L v) h

lemma SplittingChart.cast_chart {T : HolomorphicSplitting X r s}
    (h : S=T) (e : SplittingChart S) : (h ▸ e).chart=e.chart := by
  subst T
  rfl

variable {A : Type*} [TopologicalSpace A] {f : A → X.Carrier}

lemma horizontal_swap_of_vertical
    (hv : ProductBoxTopology.IsVertical (splittingAtlas S) f) :
    ProductBoxTopology.IsHorizontal (splittingAtlas S.swap) f := by
  refine ⟨hv.1,?_⟩
  rintro _ ⟨e,rfl⟩
  let d : SplittingChart S := S.swap_swap ▸ e.swap
  have H := hv.2 d.chart ⟨d,rfl⟩
  dsimp only [d] at H
  rw [SplittingChart.cast_chart] at H
  exact H

lemma vertical_swap_of_horizontal
    (hh : ProductBoxTopology.IsHorizontal (splittingAtlas S) f) :
    ProductBoxTopology.IsVertical (splittingAtlas S.swap) f := by
  refine ⟨hh.1,?_⟩
  rintro _ ⟨e,rfl⟩
  let d : SplittingChart S := S.swap_swap ▸ e.swap
  have H := hh.2 d.chart ⟨d,rfl⟩
  dsimp only [d] at H
  rw [SplittingChart.cast_chart] at H
  exact H

lemma horizontal_of_vertical_swap
    (hv : ProductBoxTopology.IsVertical (splittingAtlas S.swap) f) :
    ProductBoxTopology.IsHorizontal (splittingAtlas S) f := by
  have H := horizontal_swap_of_vertical hv
  rwa [S.swap_swap] at H

lemma vertical_of_horizontal_swap
    (hh : ProductBoxTopology.IsHorizontal (splittingAtlas S.swap) f) :
    ProductBoxTopology.IsVertical (splittingAtlas S) f := by
  have H := vertical_swap_of_horizontal hh
  rwa [S.swap_swap] at H

end UniversalCoverSplitting
end
end

end OAI
