import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.RationalFieldDifferences

namespace OAI

/-! Literal rational programs for the three fixed coordinate differences.
Their scalar sampler is supplied as a concrete Procedure, and is evaluated
only a fixed number of times per gradient or Laplacian sample. -/

namespace ContinuumCoulomb.FiniteDifferenceProgram
open ExactQuantumFactoring.BitStackProgram
open CappedKernelProgram (Triple tripleCode)
open RationalFieldDifferences

noncomputable opaque shiftProgram (a : Fin 3) : Procedure (prodCode tripleCode ratCode) tripleCode
    (fun x => shift x.1 x.2 a) := by
  let q := Procedure.first tripleCode ratCode
  let h := Procedure.second tripleCode ratCode
  let zero := Procedure.constant (prodCode tripleCode ratCode) ratCode (0:ℚ)
  let x := (Procedure.first ratCode (prodCode ratCode ratCode)).comp q
  let yz := (Procedure.second ratCode (prodCode ratCode ratCode)).comp q
  let y := (Procedure.first ratCode ratCode).comp yz
  let z := (Procedure.second ratCode ratCode).comp yz
  let dx : Procedure (prodCode tripleCode ratCode) ratCode (fun z => if a=0 then z.2 else 0) := by
    by_cases ha : a=0
    · exact h.congrFun (by intro z; simp only [ha,ite_true])
    · exact zero.congrFun (by intro z; simp only [ha,ite_false])
  let dy : Procedure (prodCode tripleCode ratCode) ratCode (fun z => if a=1 then z.2 else 0) := by
    by_cases ha : a=1
    · exact h.congrFun (by intro z; simp only [ha,ite_true])
    · exact zero.congrFun (by intro z; simp only [ha,ite_false])
  let dz : Procedure (prodCode tripleCode ratCode) ratCode (fun z => if a=2 then z.2 else 0) := by
    by_cases ha : a=2
    · exact h.congrFun (by intro z; simp only [ha,ite_true])
    · exact zero.congrFun (by intro z; simp only [ha,ite_false])
  let xx := Procedure.ratAdd.comp (x.pair dx)
  let yy := Procedure.ratAdd.comp (y.pair dy)
  let zz := Procedure.ratAdd.comp (z.pair dz)
  exact (xx.pair (yy.pair zz)).congrFun (by intro x; rfl)

variable {E : Type} {ce : E → List Bool} {sample : E → Triple → ℚ} {step : E → ℚ}

noncomputable opaque plusArgumentProgram (a : Fin 3)
    (stepProgram : Procedure ce ratCode step) :
    Procedure (prodCode ce tripleCode) tripleCode (fun x => shift x.2 (step x.1) a) :=
  (shiftProgram a).comp ((Procedure.second ce tripleCode).pair
    (stepProgram.comp (Procedure.first ce tripleCode)))

noncomputable opaque minusArgumentProgram (a : Fin 3)
    (stepProgram : Procedure ce ratCode step) :
    Procedure (prodCode ce tripleCode) tripleCode (fun x => shift x.2 (-step x.1) a) :=
  (shiftProgram a).comp ((Procedure.second ce tripleCode).pair
    (Procedure.ratNeg.comp (stepProgram.comp (Procedure.first ce tripleCode))))

noncomputable opaque plusSampleProgram (a : Fin 3)
    (sampleProgram : Procedure (prodCode ce tripleCode) ratCode (fun x => sample x.1 x.2))
    (stepProgram : Procedure ce ratCode step) :
    Procedure (prodCode ce tripleCode) ratCode (fun x => sample x.1 (shift x.2 (step x.1) a)) :=
  sampleProgram.comp ((Procedure.first ce tripleCode).pair (plusArgumentProgram a stepProgram))

noncomputable opaque minusSampleProgram (a : Fin 3)
    (sampleProgram : Procedure (prodCode ce tripleCode) ratCode (fun x => sample x.1 x.2))
    (stepProgram : Procedure ce ratCode step) :
    Procedure (prodCode ce tripleCode) ratCode (fun x => sample x.1 (shift x.2 (-step x.1) a)) :=
  sampleProgram.comp ((Procedure.first ce tripleCode).pair (minusArgumentProgram a stepProgram))

noncomputable opaque firstProgram (a : Fin 3)
    (sampleProgram : Procedure (prodCode ce tripleCode) ratCode (fun x => sample x.1 x.2))
    (stepProgram : Procedure ce ratCode step) :
    Procedure (prodCode ce tripleCode) ratCode
      (fun x => first (sample x.1) (step x.1) x.2 a) := by
  let diff := Procedure.ratSub.comp ((plusSampleProgram a sampleProgram stepProgram).pair sampleProgram)
  exact Procedure.ratDiv.comp (diff.pair (stepProgram.comp (Procedure.first ce tripleCode)))

noncomputable opaque secondNumeratorProgram (a : Fin 3)
    (sampleProgram : Procedure (prodCode ce tripleCode) ratCode (fun x => sample x.1 x.2))
    (stepProgram : Procedure ce ratCode step) :
    Procedure (prodCode ce tripleCode) ratCode (fun x =>
      sample x.1 (shift x.2 (step x.1) a)+sample x.1 (shift x.2 (-step x.1) a)-2*sample x.1 x.2) := by
  let ends := Procedure.ratAdd.comp ((plusSampleProgram a sampleProgram stepProgram).pair
    (minusSampleProgram a sampleProgram stepProgram))
  let center := Procedure.ratMul.comp
    ((Procedure.constant (prodCode ce tripleCode) ratCode (2:ℚ)).pair sampleProgram)
  exact Procedure.ratSub.comp (ends.pair center)

noncomputable opaque stepSquareProgram (stepProgram : Procedure ce ratCode step) :
    Procedure (prodCode ce tripleCode) ratCode (fun x => step x.1^2) := by
  let h := stepProgram.comp (Procedure.first ce tripleCode)
  exact (Procedure.ratMul.comp (h.pair h)).congrFun (by intro x; simp only [pow_two]; rfl)

noncomputable opaque secondProgram (a : Fin 3)
    (sampleProgram : Procedure (prodCode ce tripleCode) ratCode (fun x => sample x.1 x.2))
    (stepProgram : Procedure ce ratCode step) :
    Procedure (prodCode ce tripleCode) ratCode
      (fun x => second (sample x.1) (step x.1) x.2 a) :=
  Procedure.ratDiv.comp ((secondNumeratorProgram a sampleProgram stepProgram).pair
    (stepSquareProgram stepProgram))

noncomputable opaque laplacianProgram
    (sampleProgram : Procedure (prodCode ce tripleCode) ratCode (fun x => sample x.1 x.2))
    (stepProgram : Procedure ce ratCode step) :
    Procedure (prodCode ce tripleCode) ratCode
      (fun x => laplacian (sample x.1) (step x.1) x.2) := by
  let p0 := secondProgram (0:Fin 3) sampleProgram stepProgram
  let p1 := secondProgram (1:Fin 3) sampleProgram stepProgram
  let p2 := secondProgram (2:Fin 3) sampleProgram stepProgram
  exact (Procedure.ratAdd.comp (p0.pair (Procedure.ratAdd.comp (p1.pair p2)))).congrFun (by
    intro x
    simp only [RationalFieldDifferences.laplacian,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    rfl)

end ContinuumCoulomb.FiniteDifferenceProgram

end OAI
