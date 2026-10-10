import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.ElementaryMotion

namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity.Elementary
open BalancedTransport.Geometry

lemma congr {d : ℕ} [NeZero d] {f g : (Fin d → ℝ) → ℝ} (hf : Elementary f) (he : ∀x, f x = g x) : Elementary g := by
  rwa [← funext he]

end BalancedTransport.Effectivity.Elementary
end

noncomputable section
namespace BalancedTransport.Effectivity.ElementaryCurve
open BalancedTransport.Geometry

lemma deriv {f : ℝ → ℝ} (hf : ElementaryCurve f) : ElementaryCurve (_root_.deriv f) := by
  have hd := (Elementary.coordinateDerivative hf 0)
  have h (x : Fin 1 → ℝ) :
      fderiv ℝ (fun z : Fin 1 → ℝ => f (z 0)) x (Pi.single 0 1) = _root_.deriv f (x 0) := by
    have he : (fun t : ℝ => f ((fun _ : Fin 1 => t) 0)) = f := rfl
    have hg : HasDerivAt (fun t : ℝ => fun _ : Fin 1 => t) (Pi.single 0 1) (x 0) := by
      apply hasDerivAt_pi.mpr
      intro i
      fin_cases i
      change HasDerivAt (fun s : ℝ => s) (1 : ℝ) (x 0)
      exact hasDerivAt_id _
    have hfx : (fun _ : Fin 1 => x 0) = x := by ext i; fin_cases i; rfl
    have hh := ((Elementary.differentiable hf) (fun _ => x 0)).hasFDerivAt
    simpa only [hfx, Function.comp_def] using (hh.comp_hasDerivAt (x 0) hg).deriv.symm
  change Elementary (fun x : Fin 1 → ℝ => _root_.deriv f (x 0))
  exact hd.congr h

end BalancedTransport.Effectivity.ElementaryCurve
end

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry

def fieldArgs {d : ℕ} (p : Fin d → ℝ) (t : ℝ) (x : Space) : Fin (4+d) → ℝ :=
  Fin.append (Fin.cons t x) p

def fieldParam {d : ℕ} (z : Fin (4+d) → ℝ) : Fin d → ℝ := fun k => z (Fin.natAdd 4 k)

def fieldTime {d : ℕ} (z : Fin (4+d) → ℝ) : ℝ := z (Fin.castAdd d 0)

def fieldSpace {d : ℕ} (z : Fin (4+d) → ℝ) : Space := fun k => z (Fin.castAdd d k.succ)

@[simp] lemma fieldParam_args {d : ℕ} (p : Fin d → ℝ) (t : ℝ) (x : Space) :
    fieldParam (fieldArgs p t x) = p := by ext k; simp [fieldParam,fieldArgs]

@[simp] lemma fieldTime_args {d : ℕ} (p : Fin d → ℝ) (t : ℝ) (x : Space) :
    fieldTime (fieldArgs p t x) = t := by simp [fieldTime,fieldArgs]

@[simp] lemma fieldSpace_args {d : ℕ} (p : Fin d → ℝ) (t : ℝ) (x : Space) :
    fieldSpace (fieldArgs p t x) = x := by ext k; simp [fieldSpace,fieldArgs]

@[simp] lemma fieldArgs_parts {d : ℕ} (z : Fin (4+d) → ℝ) :
    fieldArgs (fieldParam z) (fieldTime z) (fieldSpace z) = z := by
  ext k
  refine Fin.addCases ?_ ?_ k
  · intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [fieldArgs,fieldTime]
    · simp [fieldArgs,fieldTime,fieldSpace]
  · intro j
    simp [fieldArgs,fieldParam,fieldTime]

def ElementaryScalar {d : ℕ} (f : (Fin d → ℝ) → Field ℝ) : Prop :=
  Elementary (fun z => f (fieldParam z) (fieldTime z) (fieldSpace z))

def ElementaryField {d : ℕ} (f : (Fin d → ℝ) → Velocity) : Prop :=
  ∀ i, ElementaryScalar (fun p t x => f p t x i)

lemma fieldArgs_time_hasDerivAt {d : ℕ} (p : Fin d → ℝ) (t : ℝ) (x : Space) :
    HasDerivAt (fun s => fieldArgs p s x) (Pi.single (Fin.castAdd d 0) 1) t := by
  apply hasDerivAt_pi.mpr
  intro k
  refine Fin.addCases ?_ ?_ k
  · intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [fieldArgs, Fin.append_left, Fin.cons_zero, Pi.single_eq_same]
      exact hasDerivAt_id _
    · have hn : Fin.castAdd d i.succ ≠ Fin.castAdd d (0 : Fin 4) := by
        intro h; have := congrArg Fin.val h; simp only [Fin.val_castAdd, Fin.val_succ, Fin.val_zero] at this; omega
      simpa only [fieldArgs, Fin.append_left, Fin.cons_succ, Pi.single_apply, ite_eq_right hn] using hasDerivAt_const t (x i)
  · intro j
    have hn : Fin.natAdd 4 j ≠ Fin.castAdd d (0 : Fin 4) := by
      intro h; have := congrArg Fin.val h; simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.val_zero] at this; omega
    simpa only [fieldArgs, Fin.append_right, Pi.single_apply, ite_eq_right hn] using hasDerivAt_const t (p j)

lemma fieldArgs_space_hasFDerivAt {d : ℕ} (p : Fin d → ℝ) (t : ℝ) (x : Space) :
    HasFDerivAt (fun y => fieldArgs p t y)
      (ContinuousLinearMap.pi (fun k : Fin (4+d) =>
        Fin.addCases (Fin.cases (0 : Space →L[ℝ] ℝ) (fun i => ContinuousLinearMap.proj i))
          (fun _ => 0) k)) x := by
  apply hasFDerivAt_pi.mpr
  intro k
  refine Fin.addCases ?_ ?_ k
  · intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · simpa [fieldArgs] using hasFDerivAt_const t x
    · simpa [fieldArgs] using hasFDerivAt_apply i x
  · intro j
    simpa [fieldArgs] using hasFDerivAt_const (p j) x

end BalancedTransport.Effectivity
end

noncomputable section
namespace BalancedTransport.Effectivity.ElementaryScalar
open BalancedTransport.Geometry
variable {d : ℕ} {f g : (Fin d → ℝ) → Field ℝ}

lemma fullTimeD (h : ElementaryScalar f) : ElementaryScalar (fun p => Geometry.fullTimeD (f p)) := by
  have hd := h.coordinateDerivative (Fin.castAdd d 0)
  apply hd.congr
  intro z
  have hh := (h.differentiable (fieldArgs (fieldParam z) (fieldTime z) (fieldSpace z))).hasFDerivAt
  have he := hh.comp_hasDerivAt (fieldTime z) (fieldArgs_time_hasDerivAt (fieldParam z) (fieldTime z) (fieldSpace z))
  simpa only [Function.comp_def, fieldArgs_parts,fieldParam_args,fieldTime_args,fieldSpace_args,Geometry.fullTimeD] using he.deriv.symm

lemma spaceD (h : ElementaryScalar f) (i : Fin 3) : ElementaryScalar (fun p => BalancedTransport.spaceD i (f p)) := by
  have hd := h.coordinateDerivative (Fin.castAdd d i.succ)
  apply hd.congr
  intro z
  have hh := (h.differentiable (fieldArgs (fieldParam z) (fieldTime z) (fieldSpace z))).hasFDerivAt
  have he := hh.comp (fieldSpace z) (fieldArgs_space_hasFDerivAt (fieldParam z) (fieldTime z) (fieldSpace z))
  have hl : (ContinuousLinearMap.pi (fun k : Fin (4+d) =>
        Fin.addCases (Fin.cases (0 : Space →L[ℝ] ℝ) (fun i => ContinuousLinearMap.proj i))
          (fun _ => 0) k) : Space →L[ℝ] (Fin (4+d) → ℝ)) (Pi.single i 1) = Pi.single (Fin.castAdd d i.succ) 1 := by
    ext k
    refine Fin.addCases ?_ ?_ k
    · intro j
      refine Fin.cases ?_ (fun l => ?_) j
      · have hn : Fin.castAdd d (0 : Fin 4) ≠ Fin.castAdd d i.succ := by
          intro h; have := congrArg Fin.val h; simp only [Fin.val_castAdd, Fin.val_succ, Fin.val_zero] at this; omega
        simp only [ContinuousLinearMap.pi_apply, Fin.addCases_left, Fin.cases_zero,
          zero_apply, Pi.single_apply, ite_eq_right hn]
      · simp only [ContinuousLinearMap.pi_apply, Fin.addCases_left, Fin.cases_succ,
          ContinuousLinearMap.proj_apply, Pi.single_apply, Fin.castAdd_inj, Fin.succ_inj]
    · intro j
      have hn : Fin.natAdd 4 j ≠ Fin.castAdd d i.succ := by
        intro h; have := congrArg Fin.val h; simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.val_succ] at this; omega
      simp only [ContinuousLinearMap.pi_apply, Fin.addCases_right,
        zero_apply, Pi.single_apply, ite_eq_right hn]
  simpa only [Function.comp_def, fieldArgs_parts,fieldParam_args,fieldTime_args,fieldSpace_args, BalancedTransport.spaceD,
    ContinuousLinearMap.comp_apply, hl] using congrArg (fun l => l (Pi.single i 1)) he.fderiv.symm

end BalancedTransport.Effectivity.ElementaryScalar
end

end OAI
