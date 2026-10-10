import Mathlib
import OAI.Probability.SKGap.Localization.TAPGauge
import OAI.Probability.SKGap.Entropy.RootBadMeasurable

namespace OAI

section

noncomputable section
namespace SKGap.ObservationBridge
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
variable {n : ℕ}
local instance matrixMeasurable : MeasurableSpace (Matrix (Fin n) (Fin n) ℝ) := borel _
local instance matrixBorel : BorelSpace (Matrix (Fin n) (Fin n) ℝ) := ⟨rfl⟩

def operatorBound (K : ℝ) (J : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ z : Field n,vectorNorm (J*ᵥz) ≤ K*vectorNorm z

lemma isClosed_operatorBound (K : ℝ) : IsClosed {J : Matrix (Fin n) (Fin n) ℝ | operatorBound K J} := by
  have he : {J : Matrix (Fin n) (Fin n) ℝ | operatorBound K J} =
      ⋂ z : Field n,{J | vectorNorm (J*ᵥz) ≤ K*vectorNorm z} := by ext J; simp [operatorBound]
  rw [he]
  apply isClosed_iInter
  intro z
  exact isClosed_le ((continuous_vectorNorm n).comp (by unfold Matrix.mulVec; fun_prop)) continuous_const

def literalBadPair (j A K ε c ρ : ℝ) : Set (Matrix (Fin n) (Fin n) ℝ × Field n) :=
  {p | operatorBound K p.1 ∧ rootBad j A ε c ρ p.1 p.2}

lemma measurableSet_literalBadPair (j A K ε c ρ : ℝ) :
    MeasurableSet (literalBadPair (n:=n) j A K ε c ρ) :=
  ((isClosed_operatorBound K).measurableSet.preimage measurable_fst).inter
    (measurableSet_rootBad j A ε c ρ)

lemma spinMatrixAct_involutive (s : Spin n) (J : Matrix (Fin n) (Fin n) ℝ) :
    spinMatrixAct s (spinMatrixAct s J)=J := by
  ext i k
  dsimp [spinMatrixAct]
  calc
    _ = (spinValue (s i))^2*(spinValue (s k))^2*J i k := by ring
    _ = _ := by rw [spinValue_sq,spinValue_sq,one_mul,one_mul]

lemma spinMatrixAct_mulVec (s : Spin n) (J : Matrix (Fin n) (Fin n) ℝ) (z : Field n) :
    spinMatrixAct s J*ᵥspinAct s z=spinAct s (J*ᵥz) := by
  ext i
  simp only [Matrix.mulVec,dotProduct,spinMatrixAct,spinAct,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  calc
    _ = spinValue (s i)*(J i k*z k)*(spinValue (s k))^2 := by ring
    _ = _ := by rw [spinValue_sq,mul_one]

lemma operatorBound_spin_iff (s : Spin n) (K : ℝ) (J : Matrix (Fin n) (Fin n) ℝ) :
    operatorBound K (spinMatrixAct s J) ↔ operatorBound K J := by
  have htrans (J : Matrix (Fin n) (Fin n) ℝ) (hJ : operatorBound K J) :
      operatorBound K (spinMatrixAct s J) := by
    intro z
    have hh := hJ (spinAct s z)
    have he := spinMatrixAct_mulVec s J (spinAct s z)
    rw [spinAct_involutive] at he
    rw [he,spinAct_norm]
    simpa only [spinAct_norm] using hh
  exact ⟨fun h=>by simpa only [spinMatrixAct_involutive] using htrans _ h,htrans _⟩

lemma literalBadPair_spin_iff (s : Spin n) (j A K ε c ρ : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (h : Field n) :
    (spinMatrixAct s J,spinAct s h)∈literalBadPair j A K ε c ρ ↔
      (J,h)∈literalBadPair j A K ε c ρ := by
  change (operatorBound K (spinMatrixAct s J) ∧ rootBad j A ε c ρ (spinMatrixAct s J) (spinAct s h)) ↔ _
  rw [operatorBound_spin_iff]
  refine and_congr_right (fun _=>⟨fun hh=>?_,spinAct_bad s j A ε c ρ J h⟩)
  simpa only [spinMatrixAct_involutive,spinAct_involutive] using
    spinAct_bad s j A ε c ρ (spinMatrixAct s J) (spinAct s h) hh

lemma gaussianSign_variance_preserving {κ : Type*} [Fintype κ]
    (q : κ→ℝ) (hq : ∀ i,q i^2=1) (v : ℝ≥0) :
    MeasurePreserving (gaussianSignEquiv q hq)
      (Measure.pi (fun _ : κ=>gaussianReal 0 v)) (Measure.pi (fun _ : κ=>gaussianReal 0 v)) := by
  refine ⟨(gaussianSignEquiv q hq).measurable,?_⟩
  have he (i : κ) : (gaussianReal 0 v).map (fun x=>q i*x)=gaussianReal 0 v := by
    rcases sq_eq_one_iff.mp (hq i) with h|h
    · simp [h]
    · simpa only [h,neg_one_mul,neg_zero] using (gaussianReal_map_neg (μ:=(0:ℝ)) (v:=v))
  change (Measure.pi (fun _ : κ=>gaussianReal 0 v)).map (fun g i=>q i*g i)=_
  rw [Measure.pi_map_pi (fun _=>by fun_prop)]
  simp only [he]

def edgeSpinSign (s : Spin n) (e : Edge n) : ℝ := spinValue (s e.1.1)*spinValue (s e.1.2)
lemma edgeSpinSign_sq (s : Spin n) (e : Edge n) : edgeSpinSign s e^2=1 := by
  simp only [edgeSpinSign,mul_pow,spinValue_sq,one_mul]

def plantedEdges (r : ℝ) (s : Spin n) (g : Disorder n) : Disorder n :=
  fun e=>sqrt r*g e+r*spinValue (s e.1.1)*spinValue (s e.1.2)
def plusPlantedEdges (r : ℝ) (g : Disorder n) : Disorder n := fun e=>sqrt r*g e+r

lemma coupling_planted_gauge (s : Spin n) (r : ℝ) (g : Disorder n) :
    spinMatrixAct s (coupling (plantedEdges r s g)) =
      coupling (plusPlantedEdges r (gaussianSignEquiv (edgeSpinSign s) (edgeSpinSign_sq s) g)) := by
  ext i k
  unfold spinMatrixAct coupling
  split_ifs with h h
  · dsimp [plantedEdges,plusPlantedEdges,gaussianSignEquiv,edgeSpinSign]
    calc
      _ = sqrt r*(spinValue (s i)*spinValue (s k)*g ⟨(i,k),h⟩)+r*(spinValue (s i))^2*(spinValue (s k))^2 := by ring
      _ = _ := by rw [spinValue_sq,spinValue_sq,mul_one,mul_one]; rfl
  · dsimp [plantedEdges,plusPlantedEdges,gaussianSignEquiv,edgeSpinSign]
    calc
      _ = sqrt r*(spinValue (s k)*spinValue (s i)*g ⟨(k,i),h⟩)+r*(spinValue (s i))^2*(spinValue (s k))^2 := by ring
      _ = _ := by rw [spinValue_sq,spinValue_sq,mul_one,mul_one]; rfl
  · simp

lemma spin_observation (s : Spin n) (t : ℝ) (b : Field n) :
    spinAct s (fun i=>t*spinValue (s i)+b i)=(fun i=>t+spinAct s b i) := by
  ext i
  dsimp [spinAct]
  calc
    _ = t*(spinValue (s i))^2+spinValue (s i)*b i := by ring
    _ = _ := by rw [spinValue_sq,mul_one]

lemma continuous_coupling : Continuous (coupling (n:=n)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro k
  unfold coupling
  split_ifs <;> fun_prop

theorem gauged_fixed_time_probability (s : Spin n) (r j A K ε c ρ t : ℝ) :
    ((gaussianCoordinates (Edge n)).prod (Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal)))
      {p | (coupling (plantedEdges r s p.1),(fun i=>t*spinValue (s i)+p.2 i))∈literalBadPair j A K ε c ρ} =
    ((gaussianCoordinates (Edge n)).prod (Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal)))
      {p | (coupling (plusPlantedEdges r p.1),(fun i=>t+p.2 i))∈literalBadPair j A K ε c ρ} := by
  let V := gaussianSignEquiv (edgeSpinSign s) (edgeSpinSign_sq s)
  let W := gaussianSignEquiv (fun i=>spinValue (s i)) (fun i=>spinValue_sq (s i))
  have hV := gaussianSign_variance_preserving (edgeSpinSign s) (edgeSpinSign_sq s) 1
  have hW := gaussianSign_variance_preserving (fun i=>spinValue (s i)) (fun i=>spinValue_sq (s i)) t.toNNReal
  have hm := hV.prod hW
  let E := {p : Disorder n × Field n |
    (coupling (plusPlantedEdges r p.1),(fun i=>t+p.2 i))∈literalBadPair j A K ε c ρ}
  have hmap : Continuous (fun p : Disorder n × Field n =>
      ((coupling (plusPlantedEdges r p.1)),(fun i=>t+p.2 i)) :
      Disorder n × Field n → Matrix (Fin n) (Fin n) ℝ × Field n) :=
    (continuous_coupling.comp (by unfold plusPlantedEdges;fun_prop)).prodMk (by fun_prop)
  have hmmap : Measurable (fun p : Disorder n × Field n =>
      ((coupling (plusPlantedEdges r p.1)),(fun i=>t+p.2 i)) :
      Disorder n × Field n → Matrix (Fin n) (Fin n) ℝ × Field n) := hmap.measurable
  have hE : MeasurableSet E := (measurableSet_literalBadPair j A K ε c ρ).preimage hmmap
  have he : {p : Disorder n × Field n |
    (coupling (plantedEdges r s p.1),(fun i=>t*spinValue (s i)+p.2 i))∈literalBadPair j A K ε c ρ} =
      (Prod.map V W) ⁻¹' E := by
    ext p
    change _ ↔ (coupling (plusPlantedEdges r (V p.1)),fun i=>t+W p.2 i)∈literalBadPair j A K ε c ρ
    have hh := literalBadPair_spin_iff s j A K ε c ρ
      (coupling (plantedEdges r s p.1)) (fun i=>t*spinValue (s i)+p.2 i)
    rw [coupling_planted_gauge,spin_observation] at hh
    exact hh.symm
  rw [he]
  exact hm.measure_preimage hE.nullMeasurableSet
end SKGap.ObservationBridge

end
end

end OAI
