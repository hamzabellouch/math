import OAI.Dynamics.EntropyCounterexample.SkewProduct
import OAI.Geometry.SingularHomology.HomologyTransfer

namespace OAI

noncomputable section

namespace Problem340

def rawSphereSection (q : ℕ) (z : OnePoint ℂ) : RawState q :=
  (0, z, fun _ => ((0 : ℂ) : OnePoint ℂ))

def rawSphereProjection {q : ℕ} (x : RawState q) : OnePoint ℂ := x.2.1

def rawSphereSquare : OnePoint ℂ → OnePoint ℂ :=
  OnePoint.map (fun z : ℂ => z ^ 2)

theorem continuous_rawSphereSection (q : ℕ) : Continuous (rawSphereSection q) := by
  exact continuous_const.prodMk (continuous_id.prodMk continuous_const)

theorem continuous_rawSphereProjection (q : ℕ) :
    Continuous (@rawSphereProjection q) := continuous_fst.comp continuous_snd

theorem continuous_rawSphereSquare : Continuous rawSphereSquare := by
  simpa [rawQuadratic, rawSphereSquare, Function.comp_def] using
    continuous_rawQuadratic.comp (continuous_const.prodMk continuous_id :
      Continuous (fun z : OnePoint ℂ => ((0 : ℂ), z)))

@[simp] theorem rawSphereProjection_section (q : ℕ) (z : OnePoint ℂ) :
    rawSphereProjection (rawSphereSection q z) = z := rfl

@[simp] theorem rawNormalForm_section (q : ℕ) (z : OnePoint ℂ) :
    rawNormalForm (rawSphereSection q z) = rawSphereSection q (rawSphereSquare z) := rfl

theorem realHomologyMap_rawUpdate_eq_normalForm (n q : ℕ)
    {h : RawState q → ℝ} {C : RawState q → ℂ} {R : RawState q → Fin q → ℂ}
    (hh : Continuous h) (hC : Continuous C) (hR : Continuous R) :
    realHomologyMap n (rawUpdate h C R) (continuous_rawUpdate hh hC hR) =
      realHomologyMap n rawNormalForm continuous_rawNormalForm :=
  (realHomologyMap_eq_of_homotopy n continuous_rawNormalForm
    (continuous_rawUpdate hh hC hR) (rawUpdateHomotopy hh hC hR)).symm

theorem rawUpdate_eigenvector_of_sphere (n q : ℕ)
    {h : RawState q → ℝ} {C : RawState q → ℂ} {R : RawState q → Fin q → ℂ}
    (hh : Continuous h) (hC : Continuous C) (hR : Continuous R)
    (c : ℝ) (v : RealSingularHomology n (OnePoint ℂ)) (hv : v ≠ 0)
    (heig : realHomologyMap n rawSphereSquare continuous_rawSphereSquare v = c • v) :
    ∃ w : RealSingularHomology n (RawState q), w ≠ 0 ∧
      realHomologyMap n (rawUpdate h C R) (continuous_rawUpdate hh hC hR) w = c • w := by
  let s := rawSphereSection q
  have hs : Continuous s := continuous_rawSphereSection q
  have hinj := realHomologyMap_injective_of_retraction n s rawSphereProjection hs
    (continuous_rawSphereProjection q) (rawSphereProjection_section q)
  refine ⟨realHomologyMap n s hs v, ?_, ?_⟩
  · intro hz
    apply hv
    apply hinj
    simpa using hz
  · rw [realHomologyMap_rawUpdate_eq_normalForm n q hh hC hR]
    have H := realHomologyMap_comp n s rawNormalForm hs continuous_rawNormalForm
    change realHomologyMap n (s ∘ rawSphereSquare) (hs.comp continuous_rawSphereSquare) =
      (realHomologyMap n rawNormalForm continuous_rawNormalForm).comp
        (realHomologyMap n s hs) at H
    rw [realHomologyMap_comp n rawSphereSquare s continuous_rawSphereSquare hs] at H
    have Hv := congrArg (fun k => k v) H.symm
    simpa [heig] using Hv

end Problem340

end

end OAI
