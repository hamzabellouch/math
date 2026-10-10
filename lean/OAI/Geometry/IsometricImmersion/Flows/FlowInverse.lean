import OAI.Geometry.IsometricImmersion.Flows.FlowBounds
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

namespace OAI

noncomputable section
open Set Filter MeasureTheory Function
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

def triangularLinearEquiv (a b : ℝ) (hb : b ≠ 0) : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) where
  toFun v := (v.1, a * v.1 + b * v.2)
  invFun w := (w.1, (w.2 - a * w.1) / b)
  left_inv v := by
    apply Prod.ext
    · rfl
    · dsimp
      field_simp [hb]
      ring
  right_inv w := by
    apply Prod.ext
    · rfl
    · dsimp
      field_simp [hb]
      ring
  map_add' v w := by
    apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add]
    ring
  map_smul' c v := by
    apply Prod.ext <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]
    ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}

theorem triangularFlow_hasFDerivAt_equiv
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      Y s t ∈ Icc (-3 : ℝ) 3)
    (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    {p : ℝ × ℝ} (hp : p ∈ pairRectangle 2 (-2) 2) :
    ∃ A : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ), HasFDerivAt (triangularFlow Y) (A : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) p := by
  let F (v : ℝ × ℝ) := Y v.2 v.1
  let a := -q (coordinatePoint p.1 (Y p.2 p.1))
  let b := Real.exp (-(∫ r in 0..p.1, coordPartial 1 q (coordinatePoint r (Y p.2 r))))
  have hF : ContDiffOn ℝ ∞ F (pairRectangle 2 (-2) 2) :=
    cap_flow_joint_contDiffOn hq hU hSU hY hrange hstart hode
  have hd := ((hF.contDiffAt ((pairRectangle_isOpen 2 (-2) 2).mem_nhds hp)).differentiableAt
    (by simp)).hasFDerivAt
  have hdx : HasDerivAt (fun t => F (t, p.2)) a p.1 :=
    (hode p.2 ⟨hp.2.1.le, hp.2.2.le⟩ p.1 ⟨hp.1.1.le, hp.1.2.le⟩).hasDerivAt
      (Icc_mem_nhds hp.1.1 hp.1.2)
  have hdy : HasDerivAt (fun s => F (p.1, s)) b p.2 :=
    cap_flow_hasDerivAt_initial hq hU hSU hY hrange hstart hode hp.2 hp.1
  have hdx' : HasDerivAt (fun t => F (t, p.2)) (fderiv ℝ F p (1, 0)) p.1 := by
    convert hd.comp_hasDerivAt p.1 ((hasDerivAt_id p.1).prodMk
      (hasDerivAt_const p.1 p.2)) using 1
    rfl
  have hdy' : HasDerivAt (fun s => F (p.1, s)) (fderiv ℝ F p (0, 1)) p.2 := by
    convert hd.comp_hasDerivAt p.2 ((hasDerivAt_const p.2 p.1).prodMk
      (hasDerivAt_id p.2)) using 1
    rfl
  have hx : fderiv ℝ F p (1, 0) = a := hdx'.unique hdx
  have hy : fderiv ℝ F p (0, 1) = b := hdy'.unique hdy
  have hdeq : fderiv ℝ F p = jointDifferential a b := by
    apply ContinuousLinearMap.ext
    intro v
    have hv : v = v.1 • ((1, 0) : ℝ × ℝ) + v.2 • ((0, 1) : ℝ × ℝ) := by
      ext <;> simp
    calc
      fderiv ℝ F p v = v.1 * a + v.2 * b := by
        conv_lhs => rw [hv]
        simp only [map_add, map_smul, smul_eq_mul, hx, hy]
      _ = jointDifferential a b v := by simp [jointDifferential]
  have hFD : HasFDerivAt F (jointDifferential a b) p := hd.congr_fderiv hdeq
  have hb : b ≠ 0 := (Real.exp_pos _).ne'
  refine ⟨triangularLinearEquiv a b hb, ?_⟩
  have hTF := (hasFDerivAt_fst (𝕜 := ℝ) (p := p)).prodMk hFD
  convert hTF using 1 <;> first
    | rfl
    | (ext <;> simp [triangularLinearEquiv, jointDifferential])

theorem exists_triangularFlow_smooth_chart
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      Y s t ∈ Icc (-3 : ℝ) 3)
    (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    {p : ℝ × ℝ} (hp : p ∈ pairRectangle 2 (-2) 2) :
    ∃ e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ),
      p ∈ e.source ∧ e.source ⊆ pairRectangle 2 (-2) 2 ∧
      (e : (ℝ × ℝ) → (ℝ × ℝ)) = triangularFlow Y ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  let D := pairRectangle 2 (-2) 2
  have hD : IsOpen D := pairRectangle_isOpen 2 (-2) 2
  have hTF : ContDiffOn ℝ ∞ (triangularFlow Y) D :=
    contDiffOn_fst.prodMk (cap_flow_joint_contDiffOn hq hU hSU hY hrange hstart hode)
  have hTFp := hTF.contDiffAt (hD.mem_nhds hp)
  obtain ⟨A, hA⟩ := triangularFlow_hasFDerivAt_equiv hq hU hSU hY hrange hstart hode hp
  let e0 := hTFp.toOpenPartialHomeomorph (triangularFlow Y) hA (by simp)
  let e := e0.restrOpen D hD
  have heq : (e : (ℝ × ℝ) → (ℝ × ℝ)) = triangularFlow Y := rfl
  have hsub : e.source ⊆ D := fun _ hx => hx.2
  refine ⟨e, ⟨hTFp.mem_toOpenPartialHomeomorph_source hA (by simp), hp⟩,
    hsub, heq, ?_, ?_⟩
  · rw [heq]
    exact hTF.mono hsub
  · intro y hy
    have hx : e.symm y ∈ D := hsub (e.map_target hy)
    obtain ⟨L, hL⟩ := triangularFlow_hasFDerivAt_equiv hq hU hSU hY hrange hstart hode hx
    have hLe : HasFDerivAt e (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (e.symm y) := by
      rw [heq]
      exact hL
    have hfe : ContDiffAt ℝ ∞ e (e.symm y) := by
      rw [heq]
      exact hTF.contDiffAt (hD.mem_nhds hx)
    exact (e.contDiffAt_symm hy hLe hfe).contDiffWithinAt

end SmoothLocal.Flow

end

end OAI
