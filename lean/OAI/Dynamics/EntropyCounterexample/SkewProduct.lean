import OAI.Dynamics.EntropyCounterexample.SpherePerturbation

namespace OAI

noncomputable section

namespace Problem340

open scoped OnePoint

abbrev RawState (q : ℕ) := AddCircle (100 : ℝ) × OnePoint ℂ × (Fin q → OnePoint ℂ)

def rawQuadratic (p : ℂ × OnePoint ℂ) : OnePoint ℂ :=
  OnePoint.map (fun z : ℂ => z ^ 2 + p.1) p.2

theorem continuous_rawQuadratic : Continuous rawQuadratic :=
  continuous_perturbedSquare

def rawUpdate {q : ℕ} (h : RawState q → ℝ) (C : RawState q → ℂ)
    (R : RawState q → Fin q → ℂ) (x : RawState q) : RawState q :=
  (x.1 + (h x : AddCircle (100 : ℝ)), rawQuadratic (C x, x.2.1),
    fun i => (R x i : OnePoint ℂ))

def rawUpdateAtTime {q : ℕ} (h : RawState q → ℝ) (C : RawState q → ℂ)
    (R : RawState q → Fin q → ℂ) (s : ℝ) (x : RawState q) : RawState q :=
  rawUpdate (fun y => s * h y) (fun y => (s : ℂ) * C y)
    (fun y i => (s : ℂ) * R y i) x

def rawNormalForm {q : ℕ} (x : RawState q) : RawState q :=
  (x.1, OnePoint.map (fun z : ℂ => z ^ 2) x.2.1,
    fun _ => ((0 : ℂ) : OnePoint ℂ))

@[simp] theorem rawUpdateAtTime_zero {q : ℕ} (h : RawState q → ℝ)
    (C : RawState q → ℂ) (R : RawState q → Fin q → ℂ) (x : RawState q) :
    rawUpdateAtTime h C R 0 x = rawNormalForm x := by
  simp [rawUpdateAtTime, rawUpdate, rawQuadratic, rawNormalForm]

@[simp] theorem rawUpdateAtTime_one {q : ℕ} (h : RawState q → ℝ)
    (C : RawState q → ℂ) (R : RawState q → Fin q → ℂ) (x : RawState q) :
    rawUpdateAtTime h C R 1 x = rawUpdate h C R x := by
  simp [rawUpdateAtTime]

theorem continuous_rawUpdate {q : ℕ}
    {h : RawState q → ℝ} {C : RawState q → ℂ} {R : RawState q → Fin q → ℂ}
    (hh : Continuous h) (hC : Continuous C) (hR : Continuous R) :
    Continuous (rawUpdate h C R) := by
  apply Continuous.prodMk
  · exact continuous_fst.add ((AddCircle.continuous_mk' (100 : ℝ)).comp hh)
  · apply Continuous.prodMk
    · exact continuous_rawQuadratic.comp (hC.prodMk (continuous_fst.comp continuous_snd))
    · exact continuous_pi fun i => OnePoint.continuous_coe.comp
        ((continuous_apply i).comp hR)

theorem continuous_rawUpdateAtTime {q : ℕ}
    {h : RawState q → ℝ} {C : RawState q → ℂ} {R : RawState q → Fin q → ℂ}
    (hh : Continuous h) (hC : Continuous C) (hR : Continuous R) :
    Continuous (fun p : ℝ × RawState q => rawUpdateAtTime h C R p.1 p.2) := by
  unfold rawUpdateAtTime rawUpdate
  apply Continuous.prodMk
  · exact (continuous_fst.comp continuous_snd).add
      ((AddCircle.continuous_mk' (100 : ℝ)).comp
        (continuous_fst.mul (hh.comp continuous_snd)))
  · apply Continuous.prodMk
    · exact continuous_rawQuadratic.comp (((Complex.continuous_ofReal.comp continuous_fst).mul
        (hC.comp continuous_snd)).prodMk
        (continuous_fst.comp (continuous_snd.comp continuous_snd)))
    · exact continuous_pi fun i => OnePoint.continuous_coe.comp
        ((Complex.continuous_ofReal.comp continuous_fst).mul
          (((continuous_apply i).comp hR).comp continuous_snd))

theorem continuous_rawNormalForm {q : ℕ} :
    Continuous (@rawNormalForm q) := by
  have H := continuous_rawUpdateAtTime (q := q)
    (h := fun _ => 0) (C := fun _ => 0) (R := fun _ _ => 0)
    continuous_const continuous_const continuous_const
  simpa [Function.comp_def] using H.comp ((continuous_const : Continuous (fun _ : RawState q => (0 : ℝ))).prodMk continuous_id)

def rawUpdateHomotopy {q : ℕ}
    {h : RawState q → ℝ} {C : RawState q → ℂ} {R : RawState q → Fin q → ℂ}
    (hh : Continuous h) (hC : Continuous C) (hR : Continuous R) :
    ContinuousMap.Homotopy
      ⟨rawNormalForm, continuous_rawNormalForm⟩
      ⟨rawUpdate h C R, continuous_rawUpdate hh hC hR⟩ where
  toFun p := rawUpdateAtTime h C R (p.1 : ℝ) p.2
  continuous_toFun := (continuous_rawUpdateAtTime hh hC hR).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  map_zero_left := rawUpdateAtTime_zero h C R
  map_one_left := rawUpdateAtTime_one h C R

theorem rawUpdate_not_surjective {q : ℕ} (hq : 0 < q)
    (h : RawState q → ℝ) (C : RawState q → ℂ) (R : RawState q → Fin q → ℂ) :
    ¬ Function.Surjective (rawUpdate h C R) := by
  intro hs
  obtain ⟨x, hx⟩ := hs (0, ∞, fun _ => ∞)
  have hi := congrArg (fun y : RawState q => y.2.2 ⟨0, hq⟩) hx
  simp [rawUpdate] at hi

theorem rawUpdate_not_bijective {q : ℕ} (hq : 0 < q)
    (h : RawState q → ℝ) (C : RawState q → ℂ) (R : RawState q → Fin q → ℂ) :
    ¬ Function.Bijective (rawUpdate h C R) :=
  fun hb => rawUpdate_not_surjective hq h C R hb.2

end Problem340

end

end OAI
