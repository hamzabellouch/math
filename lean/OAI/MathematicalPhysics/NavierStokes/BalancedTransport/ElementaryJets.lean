import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.ElementaryCalculus

namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open _root_.OAI.BalancedTransport.Geometry

def fieldCoordinate (d : ℕ) : Option (Fin 3) → Fin (4+d)
  | none => Fin.castAdd d 0
  | some i => Fin.castAdd d i.succ

def scalarMixedD : MultiIndex → Field ℝ → Field ℝ
  | [], f => f
  | none :: a, f => fullTimeD (scalarMixedD a f)
  | some i :: a, f => spaceD i (scalarMixedD a f)

lemma ElementaryScalar.scalarMixedD {d : ℕ} {f : (Fin d → ℝ) → Field ℝ}
    (hf : ElementaryScalar f) (a : MultiIndex) :
    ElementaryScalar (fun p => scalarMixedD a (f p)) := by
  induction a with
  | nil => exact hf
  | cons i a ih => cases i with
    | none => exact ih.fullTimeD
    | some i => exact ih.spaceD i

lemma coordinateDerivative_field_time {d : ℕ} {f : (Fin d → ℝ) → Field ℝ}
    (hf : ElementaryScalar f) (z : Fin (4+d) → ℝ) :
    fderiv ℝ (fun z => f (fieldParam z) (fieldTime z) (fieldSpace z)) z
      (Pi.single (fieldCoordinate d none) 1) =
        fullTimeD (f (fieldParam z)) (fieldTime z) (fieldSpace z) := by
  have hh := (hf.differentiable (fieldArgs (fieldParam z) (fieldTime z) (fieldSpace z))).hasFDerivAt
  have he := hh.comp_hasDerivAt (fieldTime z) (fieldArgs_time_hasDerivAt (fieldParam z) (fieldTime z) (fieldSpace z))
  simpa only [Function.comp_def, fieldArgs_parts,fieldParam_args,fieldTime_args,fieldSpace_args,Geometry.fullTimeD,
    fieldCoordinate] using he.deriv.symm

lemma fieldArgs_space_single {d : ℕ} (i : Fin 3) :
    (ContinuousLinearMap.pi (fun k : Fin (4+d) =>
      Fin.addCases (Fin.cases (0 : Space →L[ℝ] ℝ) (fun i => ContinuousLinearMap.proj i))
        (fun _ => 0) k) : Space →L[ℝ] (Fin (4+d) → ℝ)) (Pi.single i 1) =
      Pi.single (fieldCoordinate d (some i)) 1 := by
  ext k
  refine Fin.addCases ?_ ?_ k
  · intro j
    refine Fin.cases ?_ (fun l => ?_) j
    · have hn : Fin.castAdd d (0 : Fin 4) ≠ Fin.castAdd d i.succ := by
        intro h; have := congrArg Fin.val h; simp only [Fin.val_castAdd, Fin.val_succ, Fin.val_zero] at this; omega
      simp only [ContinuousLinearMap.pi_apply, Fin.addCases_left, Fin.cases_zero,
        zero_apply, Pi.single_apply, ite_eq_right hn,fieldCoordinate]
    · simp only [ContinuousLinearMap.pi_apply, Fin.addCases_left, Fin.cases_succ,
        ContinuousLinearMap.proj_apply, Pi.single_apply, Fin.castAdd_inj, Fin.succ_inj,fieldCoordinate]
  · intro j
    have hn : Fin.natAdd 4 j ≠ Fin.castAdd d i.succ := by
      intro h; have := congrArg Fin.val h; simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.val_succ] at this; omega
    simp only [ContinuousLinearMap.pi_apply, Fin.addCases_right,
      zero_apply, Pi.single_apply, ite_eq_right hn,fieldCoordinate]

lemma coordinateDerivative_field_space {d : ℕ} {f : (Fin d → ℝ) → Field ℝ}
    (hf : ElementaryScalar f) (z : Fin (4+d) → ℝ) (i : Fin 3) :
    fderiv ℝ (fun z => f (fieldParam z) (fieldTime z) (fieldSpace z)) z
      (Pi.single (fieldCoordinate d (some i)) 1) =
        spaceD i (f (fieldParam z)) (fieldTime z) (fieldSpace z) := by
  have hh := (hf.differentiable (fieldArgs (fieldParam z) (fieldTime z) (fieldSpace z))).hasFDerivAt
  have he := hh.comp (fieldSpace z) (fieldArgs_space_hasFDerivAt (fieldParam z) (fieldTime z) (fieldSpace z))
  simpa only [Function.comp_def, fieldArgs_parts,fieldParam_args,fieldTime_args,fieldSpace_args,spaceD,
    ContinuousLinearMap.comp_apply, fieldArgs_space_single] using congrArg (fun l => l (Pi.single i 1)) he.fderiv.symm

end BalancedTransport.Effectivity
end

noncomputable section
namespace BalancedTransport.Effectivity.NumericProgram
open _root_.OAI.BalancedTransport.Geometry

def fieldJet (d : ℕ) : MultiIndex → NumericProgram → NumericProgram
  | [], p => p
  | i :: a, p => (fieldJet d a p).jetStep (fieldCoordinate d i)

lemma fieldJet_fold (d : ℕ) (a : MultiIndex) (p : NumericProgram) :
    fieldJet d a p = a.reverse.foldl (fun q i => q.jetStep (fieldCoordinate d i)) p := by
  induction a with
  | nil => rfl
  | cons i a ih => simp [fieldJet, ih]

lemma computable_fieldCoordinate (d : ℕ) : Computable (fieldCoordinate d) := by
  have h : Primrec (fun i : Option (Fin 3) => (Option.casesOn i 0 (fun j => j.val+1) : ℕ)) :=
    Primrec.option_casesOn Primrec.id (Primrec.const 0)
      (Primrec.succ.comp (Primrec.fin_val.comp Primrec.snd)).to₂
  have hv : Primrec (fun i : Option (Fin 3) => (fieldCoordinate d i).val) :=
    h.of_eq (fun i => by cases i <;> rfl)
  exact (Primrec.fin_val_iff.mp hv).to_comp

lemma computable_fieldJet_step (d : ℕ) :
    Computable (fun z : (MultiIndex × NumericProgram) × (NumericProgram × Option (Fin 3)) =>
      jetStep (fieldCoordinate d z.2.2) z.2.1) := by
  let A := (MultiIndex × NumericProgram) × (NumericProgram × Option (Fin 3))
  have hk : Computable (fun z : A => fieldCoordinate d z.2.2) :=
    (computable_fieldCoordinate d).comp (Computable.snd.comp Computable.snd)
  have hp : Computable (fun z : A => z.2.1) := Computable.fst.comp Computable.snd
  exact Computable.comp
    (f := fun z : Fin (4+d) × NumericProgram => jetStep z.1 z.2)
    (g := fun z : A => (fieldCoordinate d z.2.2, z.2.1))
    (computable_jetStep (d := 4+d)) (hk.pair hp)

lemma computable_fieldJet (d : ℕ) :
    Computable (fun z : MultiIndex × NumericProgram => fieldJet d z.1 z.2) := by
  have hl : Computable (fun z : MultiIndex × NumericProgram => z.1.reverse) :=
    Primrec.list_reverse.to_comp.comp Computable.fst
  have h := computable_foldl hl Computable.snd (computable_fieldJet_step d).to₂
  exact h.of_eq (fun z => (fieldJet_fold d z.1 z.2).symm)

lemma fieldJet_valid (d : ℕ) (a : MultiIndex) (p : NumericProgram) (z : Fin (4+d) → ℝ)
    (hp : p.Valid z) : (fieldJet d a p).Valid z := by
  induction a with
  | nil => exact hp
  | cons i a ih => exact jetStep_valid _ _ ih

lemma fieldJet_real {d : ℕ} {f : (Fin d → ℝ) → Field ℝ} (hf : ElementaryScalar f)
    (p : NumericProgram) (hp : ∀ z : Fin (4+d) → ℝ, p.Valid z)
    (he : ∀z, p.real z = f (fieldParam z) (fieldTime z) (fieldSpace z)) (a : MultiIndex) :
    ∀ z : Fin (4+d) → ℝ, (fieldJet d a p).real z =
      scalarMixedD a (f (fieldParam z)) (fieldTime z) (fieldSpace z) := by
  induction a with
  | nil => exact he
  | cons i a ih =>
    intro z
    rw [fieldJet, jetStep_real _ _ _ (fieldJet_valid d a p z (hp z)), funext ih]
    cases i with
    | none => exact coordinateDerivative_field_time (hf.scalarMixedD a) z
    | some i => exact coordinateDerivative_field_space (hf.scalarMixedD a) z i

end BalancedTransport.Effectivity.NumericProgram
end

noncomputable section
namespace BalancedTransport.Effectivity
open _root_.OAI.BalancedTransport.Geometry

lemma scalarMixedD_component {v : Velocity} (hv : JointSmooth v) (a : MultiIndex) (i : Fin 3) :
    scalarMixedD a (fun t x => v t x i) = fun t x => fullMixedD a v t x i := by
  induction a with
  | nil => rfl
  | cons j a ih =>
    cases j with
    | none =>
      simp only [scalarMixedD, ih, fullMixedD, fullTimeD]
      ext t x
      exact ((hasDerivAt_pi.mp
        (((hv.fullMixedD a).timeSlice x).differentiable (by simp) t).hasDerivAt) i).deriv
    | some j =>
      simp only [scalarMixedD, ih, fullMixedD, spaceD]
      ext t x
      have he := (ContinuousLinearMap.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp x
        (((hv.fullMixedD a).slice t).differentiable (by simp) x).hasFDerivAt
      exact congrArg (fun l => l (Pi.single j 1)) he.fderiv

theorem elementary_jet_programs {d : ℕ} {v : (Fin d → ℝ) → Velocity}
    (hv : ElementaryField v) (hs : ∀p, JointSmooth (v p)) :
    ∃ ps : Fin 3 → NumericProgram,
      ∀ i a z, (NumericProgram.fieldJet d a (ps i)).Valid (fieldArgs (fieldParam z) (fieldTime z) (fieldSpace z)) ∧
        (NumericProgram.fieldJet d a (ps i)).real z =
          fullMixedD a (v (fieldParam z)) (fieldTime z) (fieldSpace z) i := by
  choose ps hne hclosed hp he using (fun i => hv i)
  refine ⟨ps, ?_⟩
  intro i a z
  refine ⟨NumericProgram.fieldJet_valid d a (ps i) _ (hp i _), ?_⟩
  rw [NumericProgram.fieldJet_real (hv i) (ps i) (hp i) (fun z => congrFun (he i) z)]
  exact congrFun (congrFun (scalarMixedD_component (hs (fieldParam z)) a i) (fieldTime z)) (fieldSpace z)

end BalancedTransport.Effectivity
end

end OAI
