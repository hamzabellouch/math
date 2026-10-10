import OAI.Combinatorics.ContingencyTables.Machines.SignedFloorProgram
import OAI.Combinatorics.ContingencyTables.Machines.ScaledWordProgram
import OAI.Combinatorics.ContingencyTables.Counting.CompanionBinIntervals

namespace OAI

/-! # Binary evaluation of a bin interval and its bounded quotient draw

The lower endpoint is computed as the negative floor of a negative
rational. Thus the executed arithmetic uses natural quotient/remainder,
without enumerating any of the integers in the interval.
-/

namespace ContingencyTables.BinIntervalProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped SignedPairProgram ProfilePrograms

/-- `(number of bins, range size, bin index)`. -/
abbrev Input := (ℕ×ℕ)×ℕ

def negativeInput (z : Input) : SignedFloorProgram.Input :=
  ((0,z.2*z.1.2),z.1.1)
def negativeInputRealizer : Realizer negativeInput :=
  pair (pair (constant 0)
    (composition (f := fun z : Input => (z.2,z.1.2))
      (g := fun p : ℕ×ℕ => p.1*p.2)
      (pair second (composition first second)) multiply)) (composition first first)
lemma polynomial_negativeInput : PolynomialTime negativeInputRealizer :=
  polynomial_pair (polynomial_pair (polynomial_constant 0)
    (polynomial_composition (polynomial_pair polynomial_second
      (polynomial_composition polynomial_first polynomial_second)) polynomial_multiply))
    (polynomial_composition polynomial_first polynomial_first)

def endpoint (z : Input) : ℕ :=
  (SignedPairProgram.normalize (SignedFloorProgram.floorCode (negativeInput z))).2
def endpointRealizer : Realizer endpoint :=
  composition (f := fun z : Input => SignedPairProgram.normalize
      (SignedFloorProgram.floorCode (negativeInput z))) (g := Prod.snd)
    (composition (f := fun z : Input => SignedFloorProgram.floorCode (negativeInput z))
      (g := SignedPairProgram.normalize)
      (composition negativeInputRealizer SignedFloorProgram.floorCodeRealizer)
      SignedPairProgram.normalizeRealizer) second
theorem polynomial_endpoint : PolynomialTime endpointRealizer :=
  polynomial_composition (polynomial_composition
    (polynomial_composition polynomial_negativeInput SignedFloorProgram.polynomial_floorCode)
    SignedPairProgram.polynomial_normalize) polynomial_second

theorem endpoint_eq (K N beta : ℕ) : endpoint ((K,N),beta)=FairBits.endpoint K N beta := by
  unfold endpoint negativeInput
  rw [SignedPairProgram.normalize_eq,SignedFloorProgram.floorCode_value]
  change (-⌊((0:ℚ)-((beta*N:ℕ):ℚ))/K⌋).toNat=FairBits.endpoint K N beta
  have he : ((0:ℚ)-((beta*N:ℕ):ℚ))/K= -((beta:ℚ)*N/K) := by
    push_cast
    ring
  rw [he,Int.floor_neg,neg_neg,Int.ceil_toNat]
  rfl

def next (z : Input) : Input := (z.1,z.2+1)
def nextRealizer : Realizer next := pair first (composition second successor)
lemma polynomial_next : PolynomialTime nextRealizer :=
  polynomial_pair polynomial_first (polynomial_composition polynomial_second polynomial_successor)

def intervalSize (z : Input) : ℕ := endpoint (next z)-endpoint z
def intervalSizeRealizer : Realizer intervalSize :=
  composition (f := fun z : Input => (endpoint (next z),endpoint z))
    (g := fun p : ℕ×ℕ => p.1-p.2)
    (pair (composition (f := next) (g := endpoint) nextRealizer endpointRealizer)
      endpointRealizer) subtract
theorem polynomial_intervalSize : PolynomialTime intervalSizeRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_next polynomial_endpoint) polynomial_endpoint)
    polynomial_subtract

theorem intervalSize_eq (K N beta : ℕ) :
    intervalSize ((K,N),beta)=CompanionOracleDensity.intervalSize K N beta := by
  unfold intervalSize next
  rw [endpoint_eq,endpoint_eq]
  rfl

def draw (z : Input×List Bool) : ℕ :=
  endpoint z.1+scaledWordValue (intervalSize z.1,z.2)
def drawRealizer : Realizer draw :=
  composition (f := fun z : Input×List Bool =>
      (endpoint z.1,scaledWordValue (intervalSize z.1,z.2)))
    (g := fun p : ℕ×ℕ => p.1+p.2)
    (pair (composition (f := fun z : Input×List Bool => z.1) (g := endpoint)
        first endpointRealizer)
      (composition (f := fun z : Input×List Bool => (intervalSize z.1,z.2))
        (g := scaledWordValue)
        (pair (composition (f := fun z : Input×List Bool => z.1) (g := intervalSize)
          first intervalSizeRealizer) second) scaledWordRealizer)) add
theorem polynomial_draw : PolynomialTime drawRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_endpoint)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_intervalSize) polynomial_second)
      polynomial_scaledWord)) polynomial_add

theorem draw_mem (K N beta : ℕ) (hK : 0<K) (hN : 0<N) (hb : beta<K)
    (hsize : 0<CompanionOracleDensity.intervalSize K N beta) (bits : List Bool) :
    draw (((K,N),beta),bits)∈FairBits.fiber K N beta := by
  have hd := scaledWordValue_lt (CompanionOracleDensity.intervalSize K N beta) hsize bits
  rw [FairBits.fiber_eq_interval hK hN hb,Finset.mem_Ico]
  simp only [draw,endpoint_eq,intervalSize_eq]
  unfold CompanionOracleDensity.intervalSize at *
  omega

theorem draw_ofFn (K N beta k : ℕ) (hK : 0<K) (hN : 0<N) (hb : beta<K)
    (hsize : 0<CompanionOracleDensity.intervalSize K N beta) (bits : Fin k → Bool) :
    draw (((K,N),beta),List.ofFn bits)=
      (CompanionOracleDensity.intervalEquiv K N beta hK hN hb
        (FairBits.scaledBitInteger (CompanionOracleDensity.intervalSize K N beta) k hsize bits)).val := by
  change draw (((K,N),beta),List.ofFn bits)=FairBits.endpoint K N beta+
    (FairBits.scaledBitInteger (CompanionOracleDensity.intervalSize K N beta) k hsize bits).val
  rw [draw,endpoint_eq,intervalSize_eq,scaledWordValue_ofFn _ _ hsize]

end ContingencyTables.BinIntervalProgram

end OAI
