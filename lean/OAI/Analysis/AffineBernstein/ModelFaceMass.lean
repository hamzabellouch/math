import Mathlib
import OAI.Analysis.AffineBernstein.NormalizedCaps
import OAI.Analysis.AffineBernstein.PositiveFaceLimit
import OAI.Analysis.AffineBernstein.ProductAmbientCoordinates

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section ModelFaceMass
open Filter Metric

theorem normalized_model_positive_face_mass {n k m d : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hm : 1 ≤ m) (e : Fin n ≃ Fin k ⊕ Fin d) (eE : Fin m ≃ Fin d ⊕ Unit)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hcv : Convex ℝ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hmP : AffineMaximalOn Ω u)
    (hcomplete : EuclideanGraphComplete Ω u)
    (a : ℕ → Space n × ℝ) (L : ℕ → (Space k × Space m) ≃L[ℝ] (Space n × ℝ))
    {C : Set (Space k × Space m)} (hC : IsModelShape C)
    (hlim : LocalDistanceConverges (fun j => affineEpigraphPullback Ω u (a j) (L j)) C)
    {r R₀ : ℝ} (hr : 0 < r)
    (hin : closedBall (0:Space m) r ⊆ modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))))
    (hout : modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))) ⊆ closedBall 0 R₀) :
    ∃ R > 0, ∃ ε > 0, ∃ c > 0, ∀ᶠ j in atTop,
      ∃ K : Set (Space n), K ⊆ Ω ∧
        (∀ x ∈ K, ∀ i, ε ≤ ((L j).symm ((x,u x)-a j)).1 i ∧
          ((L j).symm ((x,u x)-a j)).1 i ≤ R) ∧
        c ≤ Real.rpow |(productAmbientBasis ((EuclideanSpace.basisFun (Fin m) ℝ).reindex eE) e).det
          ((graphAmbientBasis n).map (L j).symm.toLinearEquiv)| ((n:ℝ)/((n:ℝ)+2)) *
            ∫ x in K, affineAreaDensity u x := by
  let : NeZero m := ⟨by omega⟩
  let bE := (EuclideanSpace.basisFun (Fin m) ℝ).reindex eE
  let b := productAmbientBasis bE e
  let T := targetBasisCoordinates b
  let A := fun j => (L j).symm.trans T
  let v := fun j => -(A j) (a j)
  let ell := (positiveBaseForm (m := m) (fun _ : Fin k => (1:ℝ))).comp T.symm.toContinuousLinearMap
  let o : Space k × Space m := (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ)),0)
  have hellT (p : Space k × Space m) : ell (T p) = ∑ i, p.1 i := by
    simp [ell]
  have hoC : o ∈ interior C := by
    exact hC.normalized_center_ball hr hin (mem_closedBall_self (by positivity : 0 ≤ min (1/4:ℝ) (r/4)))
  have hclosed := sourceEpigraph_closed hΩ hne hcv hu hp hcomplete
  have hclj j : IsClosed (affineEpigraphPullback Ω u (a j) (L j)) :=
    affineEpigraphPullback_isClosed hclosed _ _
  have hnej j : (affineEpigraphPullback Ω u (a j) (L j)).Nonempty := by
    obtain ⟨x,hx⟩ := hne
    refine ⟨(L j).symm ((x,u x)-a j),?_⟩
    change (a j + (L j) ((L j).symm ((x,u x)-a j))).1 ∈ Ω ∧ _
    simp [hx]
  have hjT (j : ℕ) : (fun p => A j p + v j) '' sourceEpigraph Ω u =
      T '' affineEpigraphPullback Ω u (a j) (L j) := by
    rw [affineEpigraphPullback_eq_image,Set.image_image]
    congr 1
    funext p
    simp [A,v,sub_eq_add_neg]
  have hlimT : LocalDistanceConverges
      (fun j => (fun p => A j p+v j) '' sourceEpigraph Ω u) (T '' C) := by
    have hh := hlim.homeomorph hC.closed ⟨0,hC.zero_mem⟩ hclj hnej T.toHomeomorph
    change LocalDistanceConverges (fun j => T '' affineEpigraphPullback Ω u (a j) (L j)) (T '' C) at hh
    simpa only [hjT] using hh
  have hell : ell ≠ 0 := by
    intro hz
    have hh := hellT o
    rw [hz] at hh
    have : (0:ℝ) = k := by simpa [o] using hh
    have : (0:ℝ) < k := Nat.cast_pos.mpr (by omega)
    linarith
  have hcap : Bornology.IsBounded ((T '' C) ∩ {z | ell z ≤ (k:ℝ)+1}) := by
    have hb := (isCompact_closedBall (0:Space k × Space m)
      (max (Real.sqrt k * max 1 (((k:ℝ)+1)/1)) (max 1 (((k:ℝ)+1)/1)*R₀))).isBounded.subset
      (hC.normalized_cap_radius (B := (k:ℝ)+1) (by norm_num : (0:ℝ)<1)
        (fun _ => le_rfl) hout)
    apply (hb.image T.toContinuousLinearMap).subset
    rintro z ⟨⟨p,hp,rfl⟩,hz⟩
    refine ⟨p,⟨hp,?_⟩,rfl⟩
    simpa [ell] using hz
  have hoT : T o ∈ interior (T '' C) := by
    change T.toHomeomorph o ∈ interior (T.toHomeomorph '' C)
    rw [← T.toHomeomorph.image_interior]
    exact mem_image_of_mem _ hoC
  have hob : ell (T o) < (k:ℝ)+1 := by simp [hellT,o]
  have hs : ∀ z ∈ T '' C, ∀ i, 0 ≤ ambientCoordinates n z (productBaseIndex e i) := by
    rintro _ ⟨p,hp,rfl⟩ i
    rw [show ambientCoordinates n (T p) (productBaseIndex e i) = p.1 i from
      productAmbientCoordinates_base bE e p i]
    exact hC.support p hp i
  obtain ⟨R,hR,ε,hε,c,hc,hh⟩ := complete_affineMaximal_positive_face_mass
    (by omega : 0 < n) hΩ hne hcv hu hp hmP hcomplete A v
    (T.toHomeomorph.isClosedMap C hC.closed) hlimT ell hell hcap hoT hob (productBaseIndex e) hs
  refine ⟨R,hR,ε,hε,c,hc,?_⟩
  filter_upwards [hh] with j hj
  let K : Set (Space n) := {x | x ∈ Ω ∧ ell (A j (x,u x)+v j) < (k:ℝ)+1} ∩
    {x | ∀ i, ε < ambientCoordinates n (A j (x,u x)+v j) (productBaseIndex e i)}
  have hpull (x : Space n) : A j (x,u x)+v j = T ((L j).symm ((x,u x)-a j)) := by
    simp [A,v,sub_eq_add_neg]
  refine ⟨K,fun x hx => hx.1.1,?_,?_⟩
  · intro x hx i
    have he : ambientCoordinates n (A j (x,u x)+v j) (productBaseIndex e i) =
        ((L j).symm ((x,u x)-a j)).1 i := by rw [hpull]; exact productAmbientCoordinates_base bE e _ i
    refine ⟨by rw [← he]; exact (hx.2 i).le,?_⟩
    rw [← he]
    exact (le_abs_self _).trans ((ambientCoordinate_abs_le_norm _ _).trans
      (hj.1 x hx.1.1 hx.1.2))
  · have hh := hj.2
    change c ≤ Real.rpow |((L j).symm.trans (targetBasisCoordinates b)).toContinuousLinearMap.det|
      ((n:ℝ)/((n:ℝ)+2)) * ∫ x in K, affineAreaDensity u x at hh
    rw [targetBasisCoordinates_det] at hh
    exact hh
end ModelFaceMass


end
end AffineBernstein
end

end OAI
