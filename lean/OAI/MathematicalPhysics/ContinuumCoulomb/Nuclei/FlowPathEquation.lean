import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.FlowPathJets

namespace OAI

/-! The integral equation for the spatial jets of a local C⁴ flow model. -/

noncomputable section
open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
namespace ContinuumCoulomb
open WeakMTWTransport

theorem flow_model_path_equation (H K : ℝ × Position → Position)
    (hH : ContDiff ℝ 4 H) (hK : ContDiff ℝ 4 K)
    (O : Set Position)
    (hODE : ∀ y ∈ O, ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivAt (fun s => H (s,y)) (K (t,y)) t)
    (y : Position) (hy : y ∈ O) :
    modelPath H hH.continuous y =
      ContinuousMap.const UnitTime (H (0,y)) +
        unitPathIntegral (modelPath K hK.continuous y) := by
  apply ContinuousMap.ext
  intro t
  change H (t,y) = H (0,y) + ∫ s in (0:ℝ)..t.val,
    extendUnitPath (modelPath K hK.continuous y) s
  have hd (s : ℝ) (hs : s ∈ uIcc (0:ℝ) t.val) :
      HasDerivAt (fun s => H (s,y))
        (extendUnitPath (modelPath K hK.continuous y) s) s := by
    rw [uIcc_of_le t.property.1] at hs
    have hs' : s ∈ Icc (0:ℝ) 1 := ⟨hs.1,hs.2.trans t.property.2⟩
    have he : extendUnitPath (modelPath K hK.continuous y) s = K (s,y) :=
      extendUnitPath_coe (modelPath K hK.continuous y) ⟨s,hs'⟩
    rw [he]
    exact hODE y hy s hs'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((extendUnitPath (modelPath K hK.continuous y)).continuous.intervalIntegrable _ _)]
  abel

theorem flow_model_jet_integral (H K : ℝ × Position → Position)
    (hH : ContDiff ℝ 4 H) (hK : ContDiff ℝ 4 K)
    (O : Set Position) (hO : IsOpen O) (x : Position) (hx : x ∈ O)
    (hODE : ∀ y ∈ O, ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivAt (fun s => H (s,y)) (K (t,y)) t)
    (n : ℕ) (hn : n ≤ 4) (e : Fin n → Position) :
    iteratedFDeriv ℝ n (modelPath H hH.continuous) x e =
      ContinuousMap.const UnitTime (iteratedFDeriv ℝ n (fun y => H (0,y)) x e) +
        unitPathIntegral (iteratedFDeriv ℝ n (modelPath K hK.continuous) x e) := by
  let C : Position →L[ℝ] SpatialPath := ContinuousLinearMap.const ℝ UnitTime
  let A : SpatialPath →L[ℝ] SpatialPath := unitPathIntegral
  have hinit : ContDiff ℝ 4 (fun y => H (0,y)) :=
    hH.comp (contDiff_const.prodMk contDiff_id)
  have hP := modelPath_C4 K hK
  have heq : modelPath H hH.continuous =ᶠ[𝓝 x]
      (fun y => C (H (0,y)) + A (modelPath K hK.continuous y)) := by
    filter_upwards [hO.mem_nhds hx] with y hy
    exact flow_model_path_equation H K hH hK O hODE y hy
  have hd := (heq.iteratedFDeriv (𝕜 := ℝ) n).eq_of_nhds
  have hsum : (fun y => C (H (0,y)) + A (modelPath K hK.continuous y)) =
      (C ∘ (fun y => H (0,y))) + (A ∘ modelPath K hK.continuous) := rfl
  rw [hd, hsum, iteratedFDeriv_add_apply
    ((C.contDiff.comp hinit).contDiffAt.of_le (show (n:WithTop ℕ∞) ≤ 4 by exact_mod_cast hn))
    ((A.contDiff.comp hP).contDiffAt.of_le (show (n:WithTop ℕ∞) ≤ 4 by exact_mod_cast hn))]
  have hC := C.iteratedFDeriv_comp_left (x := x) hinit.contDiffAt
    (show (n:WithTop ℕ∞) ≤ 4 by exact_mod_cast hn)
  have hA := A.iteratedFDeriv_comp_left (x := x) hP.contDiffAt
    (show (n:WithTop ℕ∞) ≤ 4 by exact_mod_cast hn)
  change (iteratedFDeriv ℝ n (C ∘ (fun y => H (0,y))) x +
    iteratedFDeriv ℝ n (A ∘ modelPath K hK.continuous) x) e = _
  rw [hC,hA]
  rfl

end ContinuumCoulomb

end

end OAI
