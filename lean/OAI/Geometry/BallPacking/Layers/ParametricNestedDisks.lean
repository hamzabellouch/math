import Mathlib
import OAI.Geometry.BallPacking.DiskMaps.ParameterRelativeDiskMoser

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function
open MeasureTheory
open Metric
section

variable (P : Type*) [NormedAddCommGroup P] [NormedSpace ℝ P]

structure ParametricDiskEmbedding (O : Set P) where
  radius : ℝ
  radius_pos : 0 < radius
  map : P × ℂ → ℂ
  smooth : ContDiff ℝ ∞ map
  domain : Set ℂ
  open_domain : IsOpen domain
  convex_domain : Convex ℝ domain
  subset_domain : Metric.closedBall 0 radius ⊆ domain
  injective : ∀ y ∈ O, InjOn (fun x => map (y,x)) domain
  nonsingular : ∀ y ∈ O, ∀ x ∈ domain,
    (fderiv ℝ (fun x => map (y,x)) x).IsInvertible
  orientation : ∀ y ∈ O, 0 < (fderiv ℝ (fun x => map (y,x)) 0).det

variable {P}
namespace ParametricDiskEmbedding
variable {O : Set P}

def carrier (D : ParametricDiskEmbedding P O) (y : P) : Set ℂ :=
  (fun x => D.map (y,x)) '' Metric.closedBall 0 D.radius

def NestedOn (Y : Set P) (D E : ParametricDiskEmbedding P O) : Prop :=
  ∀ y ∈ Y, E.carrier y ⊆ interior (D.carrier y)

def eval (D : ParametricDiskEmbedding P O) (y : P) (hy : y ∈ O) : PlanarDiskEmbedding where
  radius := D.radius
  radius_pos := D.radius_pos
  map := fun x => D.map (y,x)
  smooth := D.smooth.comp (contDiff_const.prodMk contDiff_id)
  domain := D.domain
  open_domain := D.open_domain
  convex_domain := D.convex_domain
  subset_domain := D.subset_domain
  injective := D.injective y hy
  nonsingular := D.nonsingular y hy
  orientation := D.orientation y hy

@[simp] theorem eval_carrier (D : ParametricDiskEmbedding P O) (y : P) (hy : y ∈ O) :
    (D.eval y hy).carrier = D.carrier y := rfl

def pull {W : Set ℂ} (D : ParametricDiskEmbedding P O)
    (Φ : SupportedSmoothIsotopyFamily P ℂ W) : ParametricDiskEmbedding P O where
  radius := D.radius
  radius_pos := D.radius_pos
  map := fun p => (Φ.map p.1 1).symm (D.map p)
  smooth := Φ.endpoint_inverse_smooth.comp (contDiff_fst.prodMk D.smooth)
  domain := D.domain
  open_domain := D.open_domain
  convex_domain := D.convex_domain
  subset_domain := D.subset_domain
  injective := fun y hy => (Φ.map y 1).symm.injective.injOn.comp (D.injective y hy) (mapsTo_univ _ _)
  nonsingular := by
    intro y hy x hx
    have hd : ContDiff ℝ ∞ (fun x : ℂ => D.map (y,x)) :=
      D.smooth.comp (contDiff_const.prodMk contDiff_id)
    have hdi : ContDiff ℝ ∞ (Φ.map y 1).symm := (Φ.eval y).symm_smooth 1
    change (fderiv ℝ ((Φ.map y 1).symm ∘ (fun x => D.map (y,x))) x).IsInvertible
    rw [fderiv_comp x (hdi.differentiable (by simp) _) (hd.differentiable (by simp) x)]
    exact ((Φ.eval y).symm.fderiv_isInvertible 1 (D.map (y,x))).comp (D.nonsingular y hy x hx)
  orientation := by
    intro y hy
    have hd : ContDiff ℝ ∞ (fun x : ℂ => D.map (y,x)) :=
      D.smooth.comp (contDiff_const.prodMk contDiff_id)
    have hdi : ContDiff ℝ ∞ (Φ.map y 1).symm := (Φ.eval y).symm_smooth 1
    change 0 < (fderiv ℝ ((Φ.map y 1).symm ∘ (fun x => D.map (y,x))) 0).det
    rw [fderiv_comp 0 (hdi.differentiable (by simp) _) (hd.differentiable (by simp) 0),
      ContinuousLinearMap.det,ContinuousLinearMap.toLinearMap_comp,LinearMap.det_comp]
    exact mul_pos ((Φ.eval y).symm.det_fderiv_pos 1 (D.map (y,0))) (D.orientation y hy)

@[simp] theorem pull_radius {W : Set ℂ} (D : ParametricDiskEmbedding P O)
    (Φ : SupportedSmoothIsotopyFamily P ℂ W) : (D.pull Φ).radius = D.radius := rfl

@[simp] theorem pull_carrier {W : Set ℂ} (D : ParametricDiskEmbedding P O)
    (Φ : SupportedSmoothIsotopyFamily P ℂ W) (y : P) :
    (D.pull Φ).carrier y = (Φ.map y 1).symm '' D.carrier y := by
  exact image_comp (Φ.map y 1).symm (fun x => D.map (y,x)) _

theorem nested_pull {W : Set ℂ} {Y : Set P} {D E : ParametricDiskEmbedding P O}
    (h : NestedOn Y D E) (Φ : SupportedSmoothIsotopyFamily P ℂ W) :
    NestedOn Y (D.pull Φ) (E.pull Φ) := by
  intro y hy
  simp only [pull_carrier]
  rw [← (Φ.map y 1).symm.image_interior]
  exact image_mono (h y hy)

end ParametricDiskEmbedding

theorem supported_homeomorph_image {E : Type*} [TopologicalSpace E]
    (φ : E ≃ₜ E) (S : Set E) (h : ∀ x ∉ S, φ x = x) : φ '' S = S := by
  apply Subset.antisymm
  · rintro x ⟨y,hy,rfl⟩
    by_contra hn
    have hh : φ (φ y) = φ y := h (φ y) hn
    apply hn
    rw [φ.injective hh]
    exact hy
  · intro x hx
    refine ⟨φ.symm x,?_,φ.apply_symm_apply x⟩
    by_contra hn
    have hh := h (φ.symm x) hn
    rw [φ.apply_symm_apply] at hh
    exact hn (hh ▸ hx)

variable [CompleteSpace P] [FiniteDimensional ℝ P]

theorem exists_nested_disk_family_transport
    (O : Set P) (hO : IsOpen O) (hcO : Convex ℝ O)
    (Y : Set P) (hY : IsCompact Y) (hcY : Convex ℝ Y) (hYO : Y ⊆ O)
    (y₀ : P) (hy₀ : y₀ ∈ Y)
    (L : List (ParametricDiskEmbedding P O))
    (hL : L.Pairwise (ParametricDiskEmbedding.NestedOn Y))
    (W : Set ℂ) (hW : IsOpen W) (hLW : ∀ D ∈ L, ∀ y ∈ Y, D.carrier y ⊆ W) :
    ∃ Φ : SupportedSmoothIsotopyFamily P ℂ W,
      ∀ D ∈ L, ∀ y ∈ Y, Φ.map y 1 '' D.carrier y₀ = D.carrier y := by
  induction hn : L.length using Nat.strong_induction_on generalizing L W with
  | h n ih =>
    cases L with
    | nil => exact ⟨SupportedSmoothIsotopyFamily.refl _,by simp⟩
    | cons D L =>
      obtain ⟨Φ,hΦ⟩ := exists_embedding_family_transport D.map D.smooth O hO hcO
        D.domain W D.open_domain hW D.injective D.nonsingular Y hY hcY hYO y₀ hy₀
        (Metric.closedBall 0 D.radius) (isCompact_closedBall _ _) D.subset_domain
        (fun y hy x hx => hLW D (by simp) y hy ⟨x,hx,rfl⟩)
      have hΦim (y : P) (hy : y ∈ Y) : Φ.map y 1 '' D.carrier y₀ = D.carrier y := by
        rw [ParametricDiskEmbedding.carrier,ParametricDiskEmbedding.carrier,Set.image_image]
        exact image_congr (hΦ y hy)
      have hΦfix (x : ℂ) (hx : x ∈ D.carrier y₀) : Φ.map y₀ 1 x = x := by
        obtain ⟨z,hz,rfl⟩ := hx
        exact hΦ y₀ hy₀ z hz
      let L' := L.map (fun E => E.pull Φ)
      have hLL : L.Pairwise (ParametricDiskEmbedding.NestedOn Y) := hL.of_cons
      have hDL : ∀ E ∈ L, ParametricDiskEmbedding.NestedOn Y D E :=
        fun _ h => List.rel_of_pairwise_cons hL h
      have hL' : L'.Pairwise (ParametricDiskEmbedding.NestedOn Y) := by
        exact List.Pairwise.map (fun E => E.pull Φ)
          (fun _ _ h => ParametricDiskEmbedding.nested_pull h Φ) hLL
      have hW' : ∀ E ∈ L', ∀ y ∈ Y, E.carrier y ⊆ interior (D.carrier y₀) := by
        intro E hE y hy
        change E ∈ L.map (fun E => E.pull Φ) at hE
        obtain ⟨E0,hE0,he⟩ := List.mem_map.mp hE
        subst E
        rw [ParametricDiskEmbedding.pull_carrier]
        have hsub := image_mono (f := (Φ.map y 1).symm) (hDL E0 hE0 y hy)
        rw [(Φ.map y 1).symm.image_interior,← hΦim y hy] at hsub
        simpa only [Set.image_image,(Φ.map y 1).symm_apply_apply,Set.image_id'] using hsub
      have hlen : L'.length < n := by
        simp only [L',List.length_map]
        simp only [List.length_cons] at hn
        omega
      obtain ⟨Ψ,hΨ⟩ := ih L'.length hlen L' hL' (interior (D.carrier y₀)) isOpen_interior hW' rfl
      let Ψ' := Ψ.mono (interior_subset.trans (hLW D (by simp) y₀ hy₀))
      refine ⟨Ψ'.trans Φ,?_⟩
      intro E hE y hy
      rcases List.mem_cons.mp hE with hE | hE
      · subst E
        change (fun x => Φ.map y 1 (Ψ.map y 1 x)) '' D.carrier y₀ = D.carrier y
        have hΨim : Ψ.map y 1 '' D.carrier y₀ = D.carrier y₀ :=
          supported_homeomorph_image _ _ (fun x hx => Ψ.fixed y 1 x
            (fun h => hx (interior_subset (Ψ.support_subset h))))
        rw [← Set.image_image,hΨim,hΦim y hy]
      · have he := hΨ (E.pull Φ) (List.mem_map.mpr ⟨E,hE,rfl⟩) y hy
        have hE0 : (E.pull Φ).carrier y₀ = E.carrier y₀ := by
          rw [ParametricDiskEmbedding.pull_carrier]
          calc
            (Φ.map y₀ 1).symm '' E.carrier y₀ = id '' E.carrier y₀ := by
              apply image_congr
              intro x hx
              apply (Φ.map y₀ 1).injective
              rw [(Φ.map y₀ 1).apply_symm_apply]
              exact (hΦfix x (interior_subset (hDL E hE y₀ hy₀ hx))).symm
            _ = E.carrier y₀ := image_id _
        rw [hE0] at he
        change (fun x => Φ.map y 1 (Ψ.map y 1 x)) '' E.carrier y₀ = E.carrier y
        rw [← Set.image_image,he,ParametricDiskEmbedding.pull_carrier]
        simp only [Set.image_image,(Φ.map y 1).apply_symm_apply,Set.image_id']

theorem exists_ordinary_nested_disk_family
    (O : Set P) (hO : IsOpen O) (hcO : Convex ℝ O)
    (Y : Set P) (hY : IsCompact Y) (hcY : Convex ℝ Y) (hYO : Y ⊆ O)
    (y₀ : P) (hy₀ : y₀ ∈ Y)
    (L : List (ParametricDiskEmbedding P O))
    (hL : L.Pairwise (ParametricDiskEmbedding.NestedOn Y))
    (hr : L.Pairwise (fun D E => E.radius < D.radius))
    (R : ℝ) (hR : ∀ D ∈ L, D.radius < R)
    (hLW : ∀ D ∈ L, ∀ y ∈ Y, D.carrier y ⊆ Metric.ball 0 R) :
    ∃ Φ : SupportedSmoothIsotopyFamily P ℂ (Metric.ball 0 R),
      ∀ D ∈ L, ∀ y ∈ Y,
        Φ.map y 1 '' Metric.closedBall 0 D.radius = D.carrier y := by
  let L₀ := L.map (fun D => D.eval y₀ (hYO hy₀))
  have hL₀ : L₀.Pairwise PlanarDiskEmbedding.Nested := by
    apply List.Pairwise.map _ _ (hr.and hL)
    intro D E h
    exact ⟨h.1,h.2 y₀ hy₀⟩
  have hR₀ : ∀ D ∈ L₀, D.radius < R := by
    intro D hD
    change D ∈ L.map _ at hD
    obtain ⟨E,hE,he⟩ := List.mem_map.mp hD
    subst D
    exact hR E hE
  have hW₀ : ∀ D ∈ L₀, D.carrier ⊆ Metric.ball 0 R := by
    intro D hD
    change D ∈ L.map _ at hD
    obtain ⟨E,hE,he⟩ := List.mem_map.mp hD
    subst D
    exact hLW E hE y₀ hy₀
  obtain ⟨Φ₀,hΦ₀⟩ := exists_nested_disk_isotopy L₀ hL₀ R hR₀ hW₀
  obtain ⟨Ψ,hΨ⟩ := exists_nested_disk_family_transport O hO hcO Y hY hcY hYO y₀ hy₀
    L hL (Metric.ball 0 R) Metric.isOpen_ball hLW
  refine ⟨(SupportedSmoothIsotopyFamily.constant Φ₀).trans Ψ,?_⟩
  intro D hD y hy
  have hh := hΦ₀ (D.eval y₀ (hYO hy₀)) (List.mem_map.mpr ⟨D,hD,rfl⟩)
  change Φ₀.map 1 '' Metric.closedBall 0 D.radius = D.carrier y₀ at hh
  change (fun x => Ψ.map y 1 (Φ₀.map 1 x)) '' Metric.closedBall 0 D.radius = D.carrier y
  rw [← Set.image_image,hh,hΨ D hD y hy]

end
section

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem exists_hamiltonian_nested_disk_family
    (O : Set P) (hO : IsOpen O) (hcO : Convex ℝ O)
    (Y : Set P) (hY : IsCompact Y) (hcY : Convex ℝ Y) (hYO : Y ⊆ O)
    (y₀ : P) (hy₀ : y₀ ∈ Y)
    {m : ℕ} (D : Fin m → ParametricDiskEmbedding P O)
    (hfamily : ∀ ⦃i j⦄, i < j → ParametricDiskEmbedding.NestedOn Y (D i) (D j))
    (hr : StrictAnti (fun i => (D i).radius))
    (R : ℝ) (hR : 0 < R) (hrR : ∀ i, (D i).radius < R)
    (hDW : ∀ i y, y ∈ Y → (D i).carrier y ⊆ Metric.ball 0 R)
    (harea : ∀ i y, y ∈ Y → volume ((D i).carrier y) =
      volume (Metric.closedBall (0:ℂ) (D i).radius)) :
    ∃ Ψ : HamiltonianDiskIsotopyFamily P R, ∀ i y, y ∈ Y →
      Ψ.isotopy.map y 1 '' closedRoundDisk (D i).radius =
        Complex.equivRealProdCLM '' (D i).carrier y := by
  have hL : (List.ofFn D).Pairwise (ParametricDiskEmbedding.NestedOn Y) :=
    List.pairwise_ofFn.mpr hfamily
  have hLr : (List.ofFn D).Pairwise (fun D E => E.radius < D.radius) :=
    List.pairwise_ofFn.mpr hr
  obtain ⟨Φ,hΦ⟩ := exists_ordinary_nested_disk_family O hO hcO Y hY hcY hYO y₀ hy₀
    (List.ofFn D) hL hLr R
    (by intro E hE; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hE; exact hrR i)
    (by intro E hE; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hE; exact hDW i)
  let e := Complex.equivRealProdCLM
  let Φreal : SupportedSmoothIsotopyFamily P Plane (roundDisk R) :=
    (Φ.conjugate e).mono (by rw [complex_plane_image_ball hR.le])
  have himage (i : Fin m) (y : P) (hy : y ∈ Y) :
      Φreal.map y 1 '' closedRoundDisk (D i).radius = e '' (D i).carrier y := by
    rw [← complex_plane_image_closedBall (D i).radius_pos.le]
    change (Φ.conjugate e).map y 1 '' (e '' Metric.closedBall 0 (D i).radius) = _
    rw [Φ.conjugate_image e y 1,hΦ (D i) (List.mem_ofFn.mpr ⟨i,rfl⟩) y hy]
  obtain ⟨Ψ,hΨ⟩ := exists_hamiltonian_disk_isotopy hR Φreal Y hY
    (fun i => (D i).radius) (fun i => (D i).radius_pos) hrR hr.injective (by
      intro i y hy
      rw [himage i y hy]
      change volume (Complex.equivRealProdCLM '' (D i).carrier y) = _
      rw [complex_plane_volume_image,harea i y hy,
        ← complex_plane_image_closedBall (D i).radius_pos.le,complex_plane_volume_image])
  refine ⟨Ψ,?_⟩
  intro i y hy
  rw [hΨ i y hy,himage i y hy]

end
section

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem exists_parametric_disk_representative
    {Y A : Set P} (hY : IsCompact Y) (hcY : Convex ℝ Y)
    (hA : IsOpen A) (hYA : Y ⊆ A) {r : ℝ} (hr : 0 < r)
    (f : P × ℂ → ℂ) (hf : ContDiffOn ℝ ∞ f (A ×ˢ univ))
    (hi : ∀ y ∈ A, Injective (fun x => f (y,x)))
    (hd : ∀ y ∈ A, ∀ x, (fderiv ℝ (fun x => f (y,x)) x).IsInvertible)
    (ho : ∀ y ∈ A, 0 < (fderiv ℝ (fun x => f (y,x)) 0).det) :
    ∃ O : Set P, IsOpen O ∧ Convex ℝ O ∧ Y ⊆ O ∧ O ⊆ A ∧
      ∃ D : ParametricDiskEmbedding P O, D.radius = r ∧
        ∀ y ∈ O, ∀ x ∈ Metric.closedBall (0:ℂ) r, D.map (y,x) = f (y,x) := by
  let K := Y ×ˢ Metric.closedBall (0:ℂ) r
  have hK : IsCompact K := hY.prod (isCompact_closedBall _ _)
  obtain ⟨χ,_,_,_,_,_,hg,_,he⟩ := exists_smooth_compact_extension hK
    (hA.prod isOpen_univ) (by
      rintro ⟨y,x⟩ ⟨hy,_⟩
      exact ⟨hYA hy,mem_univ _⟩) hf
  let g : P × ℂ → ℂ := fun p => χ p • f p
  obtain ⟨W,hW,hKW,hWe⟩ := mem_nhdsSet_iff_exists.mp he
  obtain ⟨U,V,hU,hV,hYU,hBV,hUV⟩ :=
    generalized_tube_lemma hY (isCompact_closedBall (0:ℂ) r) hW hKW
  obtain ⟨δ,hδ,hδO⟩ := hY.exists_thickening_subset_open (hU.inter hA)
    (subset_inter hYU hYA)
  let O := thickening δ Y
  obtain ⟨ε,hε,hεV⟩ := (isCompact_closedBall (0:ℂ) r).exists_thickening_subset_open hV hBV
  have hball : ball (0:ℂ) (r+ε) ⊆ V := by
    rw [add_comm r ε,← thickening_closedBall hε hr.le (0:ℂ)]
    exact hεV
  have hEq (y : P) (hy : y ∈ O) (x : ℂ) (hx : x ∈ ball (0:ℂ) (r+ε)) :
      g (y,x) = f (y,x) := hWe (hUV ⟨(hδO hy).1,hball hx⟩)
  have hfder (y : P) (hy : y ∈ O) (x : ℂ) (hx : x ∈ ball (0:ℂ) (r+ε)) :
      fderiv ℝ (fun x => g (y,x)) x = fderiv ℝ (fun x => f (y,x)) x := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [isOpen_ball.mem_nhds hx] with z hz
    exact hEq y hy z hz
  let D : ParametricDiskEmbedding P O := {
      radius := r
      radius_pos := hr
      map := g
      smooth := hg
      domain := ball 0 (r+ε)
      open_domain := isOpen_ball
      convex_domain := convex_ball _ _
      subset_domain := closedBall_subset_ball (by linarith)
      injective := by
        intro y hy x hx z hz heq
        apply hi y (hδO hy).2
        change f (y,x) = f (y,z)
        rw [← hEq y hy x hx,← hEq y hy z hz]
        exact heq
      nonsingular := by
        intro y hy x hx
        rw [hfder y hy x hx]
        exact hd y (hδO hy).2 x
      orientation := by
        intro y hy
        rw [hfder y hy 0 (mem_ball_self (by linarith))]
        exact ho y (hδO hy).2 }
  refine ⟨O,isOpen_thickening,hcY.thickening δ,self_subset_thickening hδ Y,
    fun _ hy => (hδO hy).2,D,rfl,?_⟩
  intro y hy x hx
  exact hEq y hy x (closedBall_subset_ball (by linarith) hx)

end

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

namespace ParametricDiskEmbedding

def restrictParam {O U : Set P} (D : ParametricDiskEmbedding P O) (hU : U ⊆ O) :
    ParametricDiskEmbedding P U where
  radius := D.radius
  radius_pos := D.radius_pos
  map := D.map
  smooth := D.smooth
  domain := D.domain
  open_domain := D.open_domain
  convex_domain := D.convex_domain
  subset_domain := D.subset_domain
  injective := fun y hy => D.injective y (hU hy)
  nonsingular := fun y hy => D.nonsingular y (hU hy)
  orientation := fun y hy => D.orientation y (hU hy)

end ParametricDiskEmbedding

theorem exists_hamiltonian_disk_germs {m : ℕ} {Y A : Set P}
    (hY : IsCompact Y) (hcY : Convex ℝ Y) (hA : IsOpen A) (hYA : Y ⊆ A)
    (y₀ : P) (hy₀ : y₀ ∈ Y) (r : Fin m → ℝ) (hr : ∀ i, 0 < r i)
    (hrmono : StrictMono r) (f : Fin m → P × ℂ → ℂ)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (A ×ˢ univ))
    (hi : ∀ i y, y ∈ A → Injective (fun x => f i (y,x)))
    (hd : ∀ i y, y ∈ A → ∀ x, (fderiv ℝ (fun x => f i (y,x)) x).IsInvertible)
    (ho : ∀ i y, y ∈ A → 0 < (fderiv ℝ (fun x => f i (y,x)) 0).det)
    (hnest : ∀ ⦃i j⦄, i < j → ∀ y ∈ Y,
      (fun x => f i (y,x)) '' Metric.closedBall 0 (r i) ⊆
        interior ((fun x => f j (y,x)) '' Metric.closedBall 0 (r j)))
    (R : ℝ) (hR : 0 < R) (hrR : ∀ i, r i < R)
    (hfit : ∀ i y, y ∈ Y →
      (fun x => f i (y,x)) '' Metric.closedBall 0 (r i) ⊆ Metric.ball 0 R)
    (harea : ∀ i y, y ∈ Y → volume ((fun x => f i (y,x)) '' Metric.closedBall 0 (r i)) =
      volume (Metric.closedBall (0:ℂ) (r i))) :
    ∃ Ψ : HamiltonianDiskIsotopyFamily P R, ∀ i y, y ∈ Y →
      Ψ.isotopy.map y 1 '' closedRoundDisk (r i) =
        Complex.equivRealProdCLM '' ((fun x => f i (y,x)) '' Metric.closedBall 0 (r i)) := by
  classical
  have hex (i : Fin m) := exists_parametric_disk_representative hY hcY hA hYA (hr i)
    (f i) (hf i) (hi i) (hd i) (ho i)
  choose O hO hcO hYO hOA D hDr hDf using hex
  let U : Set P := ⋂ i, O i
  have hU : IsOpen U := isOpen_iInter_of_finite hO
  have hcU : Convex ℝ U := convex_iInter hcO
  have hYU : Y ⊆ U := by intro y hy; exact mem_iInter.mpr (fun i => hYO i hy)
  have hUO (i : Fin m) : U ⊆ O i := iInter_subset _ i
  let E (i : Fin m) : ParametricDiskEmbedding P U := (D i).restrictParam (hUO i)
  have hEr (i : Fin m) : (E i).radius = r i := hDr i
  have hEc (i : Fin m) (y : P) (hy : y ∈ Y) :
      (E i).carrier y = (fun x => f i (y,x)) '' Metric.closedBall 0 (r i) := by
    change (fun x => (D i).map (y,x)) '' Metric.closedBall 0 (D i).radius = _
    rw [hDr i]
    apply image_congr
    intro x hx
    exact hDf i y (hYO i hy) x hx
  let Erev (i : Fin m) := E i.rev
  obtain ⟨Ψ,hΨ⟩ := exists_hamiltonian_nested_disk_family U hU hcU Y hY hcY hYU y₀ hy₀
    Erev (by
      intro i j hij y hy
      change (E j.rev).carrier y ⊆ interior ((E i.rev).carrier y)
      rw [hEc _ y hy,hEc _ y hy]
      exact hnest (Fin.rev_lt_rev.mpr hij) y hy)
    (by
      intro i j hij
      change (E j.rev).radius < (E i.rev).radius
      rw [hEr,hEr]
      exact hrmono (Fin.rev_lt_rev.mpr hij))
    R hR (by intro i; change (E i.rev).radius < R; rw [hEr]; exact hrR _)
    (by intro i y hy; change (E i.rev).carrier y ⊆ _; rw [hEc _ y hy]; exact hfit _ y hy)
    (by
      intro i y hy
      change volume ((E i.rev).carrier y) = volume (Metric.closedBall (0:ℂ) (E i.rev).radius)
      rw [hEc _ y hy,hEr]
      exact harea _ y hy)
  refine ⟨Ψ,?_⟩
  intro i y hy
  have hh := hΨ i.rev y hy
  change Ψ.isotopy.map y 1 '' closedRoundDisk (E i.rev.rev).radius =
    Complex.equivRealProdCLM '' (E i.rev.rev).carrier y at hh
  simpa only [Fin.rev_rev,hEr,hEc _ y hy] using hh

theorem exists_hamiltonian_plane_disk_germs {m : ℕ} {Y A : Set P}
    (hY : IsCompact Y) (hcY : Convex ℝ Y) (hA : IsOpen A) (hYA : Y ⊆ A)
    (y₀ : P) (hy₀ : y₀ ∈ Y) (r : Fin m → ℝ) (hr : ∀ i, 0 < r i)
    (hrmono : StrictMono r) (f : Fin m → P × Plane → Plane)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (A ×ˢ univ))
    (hi : ∀ i y, y ∈ A → Injective (fun x => f i (y,x)))
    (hd : ∀ i y, y ∈ A → ∀ x, 0 < (fderiv ℝ (fun x => f i (y,x)) x).det)
    (hnest : ∀ ⦃i j⦄, i < j → ∀ y ∈ Y,
      (fun x => f i (y,x)) '' closedRoundDisk (r i) ⊆
        interior ((fun x => f j (y,x)) '' closedRoundDisk (r j)))
    (R : ℝ) (hR : 0 < R) (hrR : ∀ i, r i < R)
    (hfit : ∀ i y, y ∈ Y →
      (fun x => f i (y,x)) '' closedRoundDisk (r i) ⊆ roundDisk R)
    (harea : ∀ i y, y ∈ Y → volume ((fun x => f i (y,x)) '' closedRoundDisk (r i)) =
      volume (closedRoundDisk (r i))) :
    ∃ Ψ : HamiltonianDiskIsotopyFamily P R, ∀ i y, y ∈ Y →
      Ψ.isotopy.map y 1 '' closedRoundDisk (r i) =
        (fun x => f i (y,x)) '' closedRoundDisk (r i) := by
  let e := Complex.equivRealProdCLM
  let g (i : Fin m) (p : P × ℂ) := e.symm (f i (p.1,e p.2))
  have hs (i : Fin m) : ContDiffOn ℝ ∞ (g i) (A ×ˢ univ) :=
    e.symm.contDiff.comp_contDiffOn ((hf i).comp
      (contDiff_fst.prodMk (e.contDiff.comp contDiff_snd)).contDiffOn (by
        intro p hp; exact ⟨hp.1,mem_univ _⟩))
  have hder (i : Fin m) (y : P) (hy : y ∈ A) (x : ℂ) :
      (fderiv ℝ (fun x => g i (y,x)) x).det =
        (fderiv ℝ (fun x => f i (y,x)) (e x)).det := by
    change (fderiv ℝ (fun x => e.symm (f i (y,e x))) x).det = _
    apply det_fderiv_conjugate e (f := fun x => f i (y,x)) (x := x)
    have hh : ContDiffAt ℝ ∞ (f i) (y,e x) :=
      (hf i).contDiffAt ((hA.prod isOpen_univ).mem_nhds ⟨hy,mem_univ _⟩)
    exact (hh.comp _ (contDiff_const.prodMk contDiff_id).contDiffAt).differentiableAt (by simp)
  have himage (i : Fin m) (y : P) :
      e '' ((fun x => g i (y,x)) '' Metric.closedBall 0 (r i)) =
        (fun x => f i (y,x)) '' closedRoundDisk (r i) := by
    rw [←complex_plane_image_closedBall (hr i).le]
    simp only [image_image,g,e.apply_symm_apply]
    rfl
  obtain ⟨Ψ,hΨ⟩ := exists_hamiltonian_disk_germs hY hcY hA hYA y₀ hy₀ r hr hrmono g hs
    (fun i y hy => e.symm.injective.comp ((hi i y hy).comp e.injective))
    (fun i y hy x => isInvertible_of_det_ne_zero (by rw [hder i y hy x]; exact (hd i y hy _).ne'))
    (fun i y hy => by rw [hder i y hy 0]; exact hd i y hy _)
    (by
      intro i j hij y hy x hx
      have hh := hnest hij y hy
      rw [←himage i y,←himage j y] at hh
      have he : interior (e '' ((fun x => g j (y,x)) '' Metric.closedBall 0 (r j))) =
          e '' interior ((fun x => g j (y,x)) '' Metric.closedBall 0 (r j)) :=
        (e.toHomeomorph.image_interior _).symm
      rw [he] at hh
      have hh' := hh (mem_image_of_mem e hx)
      exact e.injective.mem_set_image.mp hh') R hR hrR
    (by
      intro i y hy x hx
      have hh := hfit i y hy
      rw [←himage i y,←complex_plane_image_ball hR.le] at hh
      exact e.injective.mem_set_image.mp (hh (mem_image_of_mem e hx)))
    (by
      intro i y hy
      rw [←complex_plane_volume_image, himage i y,harea i y hy,
        ←complex_plane_image_closedBall (hr i).le,complex_plane_volume_image])
  refine ⟨Ψ,?_⟩
  intro i y hy
  exact (hΨ i y hy).trans (himage i y)

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Comparison
open Set

theorem exists_positive_area_grid {A δ : ℝ} (_hA : 0 ≤ A) (hδ : 0 < δ) :
    ∃ (m : ℕ) (h : Fin m → ℝ), StrictMono h ∧ (∀ i, 0 < h i) ∧
      ∀ w ∈ Icc (0:ℝ) A, ∃ i, w ≤ h i ∧ h i-w < δ := by
  obtain ⟨N,hN⟩ := exists_nat_gt (A/(δ/2))
  have hhalf : 0 < δ/2 := by positivity
  let h (i : Fin (N+1)) : ℝ := ((i:ℕ)+1 : ℝ)*(δ/2)
  refine ⟨N+1,h,?_,?_,?_⟩
  · intro i j hij
    apply mul_lt_mul_of_pos_right _ hhalf
    have he : (i:ℝ) < (j:ℝ) := by exact_mod_cast hij
    linarith
  · intro i
    apply mul_pos _ hhalf
    positivity
  · intro w hw
    let k := ⌊w/(δ/2)⌋₊
    have hk : (k:ℝ) ≤ w/(δ/2) := Nat.floor_le (div_nonneg hw.1 hhalf.le)
    have hk' : w/(δ/2) < (k:ℝ)+1 := Nat.lt_floor_add_one _
    have hkn : (k:ℝ) < N := hk.trans_lt ((div_le_div_of_nonneg_right hw.2 hhalf.le).trans_lt hN)
    have hkN : k < N+1 := by
      have : k < N := by exact_mod_cast hkn
      omega
    refine ⟨⟨k,hkN⟩,?_,?_⟩
    · change w ≤ ((k:ℝ)+1)*(δ/2)
      exact ((div_lt_iff₀ hhalf).mp hk').le
    · change ((k:ℝ)+1)*(δ/2)-w < δ
      have hkw := (le_div_iff₀ hhalf).mp hk
      nlinarith

end PackingSufficiencySupport.Comparison
end

end OAI
