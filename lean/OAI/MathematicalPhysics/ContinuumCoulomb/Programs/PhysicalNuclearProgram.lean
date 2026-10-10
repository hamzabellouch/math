import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.CenteredNuclearProgram

namespace OAI

/-! Physical nuclear coordinates for h=1/N. The exact rational factor is
1/λ=rho/(8N^3), matching the manuscript's y=λx convention. -/

namespace ContinuumCoulomb.PhysicalNuclearProgram
open ExactQuantumFactoring.BitStackProgram
open CappedKernelProgram (Triple tripleCode position)

def factor (rho N : ℕ) : ℚ := (rho:ℚ)/(8*(N:ℚ)^3)
def scale (a : ℚ) (p : Triple) : Triple := (a*p.1,(a*p.2.1,a*p.2.2))

theorem factor_positive {rho N : ℕ} (hrho : 0 < rho) (hN : 0 < N) : 0 < factor rho N := by
  unfold factor
  positivity

theorem factor_real (rho N : ℕ) : (factor rho N:ℝ) = (rho:ℝ)/(8*(N:ℝ)^3) := by
  simp only [factor,Rat.cast_div,Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat]

theorem scale_position (a : ℚ) (p : Triple) : position (scale a p) = (a:ℝ) • position p := by
  ext i
  fin_cases i <;> simp [position,scale]

theorem scale_injective {a : ℚ} (ha : a ≠ 0) : Function.Injective (scale a) := by
  intro p q h
  have hx : a*p.1 = a*q.1 := congrArg Prod.fst h
  have hy : a*p.2.1 = a*q.2.1 := congrArg (fun p : Triple => p.2.1) h
  have hz : a*p.2.2 = a*q.2.2 := congrArg (fun p : Triple => p.2.2) h
  exact Prod.ext (mul_left_cancel₀ ha hx)
    (Prod.ext (mul_left_cancel₀ ha hy) (mul_left_cancel₀ ha hz))

theorem scale_error {a : ℚ} (ha : 0 ≤ a) (p : Triple) (x : Position) {ε : ℝ}
    (he : ‖position p-x‖ ≤ ε) : ‖position (scale a p)-(a:ℝ) • x‖ ≤ (a:ℝ)*ε := by
  rw [scale_position,← smul_sub,norm_smul,Real.norm_of_nonneg (by exact_mod_cast ha)]
  exact mul_le_mul_of_nonneg_left he (by exact_mod_cast ha)

abbrev Input := CenteredNuclearProgram.Input
def inputCode : Input → List Bool := CenteredNuclearProgram.inputCode

noncomputable def triples (rho U C K : ℕ) (x : Input) : List Triple :=
  (TransformedGauss.nodes rho U C K (x.1,CenteredGaussLabels.labels x.2)).map
    (scale (factor rho x.1.1.2))
noncomputable def nuclei (rho U C K : ℕ) (x : Input) : List BinaryPosition :=
  NuclearCoordinateOutput.positions (triples rho U C K x)

noncomputable opaque meshProgram : Procedure inputCode Nat.bits (fun x => x.1.1.2) :=
  (Procedure.second unaryCode Nat.bits).comp
    ((Procedure.first _ _).comp (Procedure.first _ _))

noncomputable opaque factorProgram (rho : ℕ) : Procedure inputCode ratCode
    (fun x => factor rho x.1.1.2) := by
  let n := meshProgram
  let n2 := Procedure.binaryMul.comp (n.pair n)
  let n3 := Procedure.binaryMul.comp (n2.pair n)
  let denominator := Procedure.binaryMul.comp
    ((Procedure.constant inputCode Nat.bits 8).pair n3)
  let p := Procedure.ratDiv.comp
    ((Procedure.constant inputCode ratCode (rho:ℚ)).pair (Procedure.natToRat.comp denominator))
  exact p.congrFun (by
    intro x
    change (rho:ℚ)/((8*((x.1.1.2*x.1.1.2)*x.1.1.2):ℕ):ℚ) = factor rho x.1.1.2
    simp only [factor,Nat.cast_mul,Nat.cast_ofNat,pow_succ,pow_zero,one_mul])

noncomputable opaque scaleProgram : Procedure (prodCode ratCode tripleCode) tripleCode
    (fun x => scale x.1 x.2) := by
  let a := Procedure.first ratCode tripleCode
  let p := Procedure.second ratCode tripleCode
  let x := EulerRegisters.tripleFirstProgram.comp p
  let y := EulerRegisters.tripleSecondProgram.comp p
  let z := EulerRegisters.tripleThirdProgram.comp p
  exact (Procedure.ratMul.comp (a.pair x)).pair
    ((Procedure.ratMul.comp (a.pair y)).pair (Procedure.ratMul.comp (a.pair z)))

noncomputable opaque triplesProgram (rho U C K : ℕ) :
    Procedure inputCode (listCode tripleCode) (triples rho U C K) := by
  let raw := (TransformedGauss.listProgram rho U C K).comp CenteredNuclearProgram.argumentsProgram
  exact (Procedure.listMapWith (ea := ratCode) (eb := tripleCode) (ec := tripleCode)
    (f := scale) (0,(0,0)) (0,(0,0)) scaleProgram).comp ((factorProgram rho).pair raw)

noncomputable opaque program (rho U C K : ℕ) :
    Procedure inputCode (BinaryEncoding.list binaryPositionCodec).encode (nuclei rho U C K) :=
  NuclearCoordinateOutput.positionsProgram.comp (triplesProgram rho U C K)

noncomputable def certificate (rho U C K : ℕ) : Turing.TM2ComputableInPolyTime inputCode
    (BinaryEncoding.list binaryPositionCodec).encode (nuclei rho U C K) :=
  (program rho U C K).toTM2

theorem nuclei_length (rho U C K : ℕ) (x : Input) :
    (nuclei rho U C K x).length = 8*((2*x.2.1+1)*(2*x.2.2.1+1)*(2*x.2.2.2+1)) := by
  rw [nuclei,NuclearCoordinateOutput.positions_length,triples,List.length_map,
    TransformedGauss.nodes_length,CenteredGaussLabels.labels_length]

theorem nuclei_valid (rho U C K : ℕ) (x : Input) {p : BinaryPosition}
    (hp : p ∈ nuclei rho U C K x) : p.Valid := NuclearCoordinateOutput.positions_valid _ hp

theorem nuclei_nonempty (rho U C K : ℕ) (x : Input) : 0 < (nuclei rho U C K x).length := by
  rw [nuclei_length]
  positivity

theorem nuclei_values_nodup (rho U C K : ℕ) (x : Input) (hrho : 0 < rho)
    (hN : 0 < x.1.1.2)
    (hnodes : (TransformedGauss.nodes rho U C K (x.1,CenteredGaussLabels.labels x.2)).Nodup) :
    ((nuclei rho U C K x).map BinaryPosition.value).Nodup := by
  have hs := hnodes.map (scale_injective (factor_positive hrho hN).ne')
  have hm := hs.map NuclearCoordinateOutput.position_value_injective
  simpa only [nuclei,NuclearCoordinateOutput.positions,List.map_map,Function.comp_def,triples] using hm

end ContinuumCoulomb.PhysicalNuclearProgram

end OAI
