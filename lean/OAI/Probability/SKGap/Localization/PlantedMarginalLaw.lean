import Mathlib
import OAI.Probability.SKGap.Stability.GaugeStabilityLaw
import OAI.Probability.SKGap.Stability.DiagonalStability

namespace OAI

section

noncomputable section
namespace SKGap.ObservationBridge
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
variable {n : ℕ}
local instance marginalMatrixMeasurable : MeasurableSpace (Matrix (Fin n) (Fin n) ℝ) := borel _
local instance marginalMatrixBorel : BorelSpace (Matrix (Fin n) (Fin n) ℝ) := ⟨rfl⟩

def goeEdges (r : ℝ) (g : MatrixCoordinates (Fin n)→ℝ) : Disorder n :=
  fun e=>goeMatrix r g e.1.1 e.1.2
lemma continuous_goeEdges (r : ℝ) : Continuous (goeEdges (n:=n) r) := by
  apply continuous_pi
  intro e
  unfold goeEdges goeMatrix
  fun_prop
lemma goeEdges_gaussian (r : ℝ) :
    HasGaussianLaw (goeEdges (n:=n) r) (gaussianCoordinates (MatrixCoordinates (Fin n))) := by
  let L : ((Fin n×Fin n)→ℝ)→L[ℝ] Disorder n :=
    ContinuousLinearMap.pi (fun e=>ContinuousLinearMap.proj e.1)
  exact (goe_matrix_gaussian r).map L
lemma goeEdges_hasLaw {r : ℝ} (hr : 0≤r) (e : Edge n) :
    HasLaw (fun g : MatrixCoordinates (Fin n)→ℝ=>goeEdges r g e)
      (gaussianReal 0 r.toNNReal) (gaussianCoordinates (MatrixCoordinates (Fin n))) := by
  have hg := (goeEdges_gaussian (n:=n) r).eval e
  refine ⟨hg.aemeasurable,?_⟩
  have hm : (∫ g,goeEdges r g e ∂gaussianCoordinates (MatrixCoordinates (Fin n)))=0 :=
    goe_mean_zero r e.1.1 e.1.2
  rw [hg.map_eq_gaussianReal,hm,← covariance_self hg.aemeasurable]
  change gaussianReal 0 (cov[fun g=>goeMatrix r g e.1.1 e.1.2,
      fun g=>goeMatrix r g e.1.1 e.1.2; gaussianCoordinates (MatrixCoordinates (Fin n))]).toNNReal = _
  rw [goe_entry_cov hr]
  have hne := ne_of_lt e.property
  simp [hne,hne.symm]
lemma goeEdges_independent {r : ℝ} (hr : 0≤r) :
    iIndepFun (fun e : Edge n=>fun g=>goeEdges r g e)
      (gaussianCoordinates (MatrixCoordinates (Fin n))) := by
  apply (goeEdges_gaussian (n:=n) r).iIndepFun_of_covariance_eq_zero
  intro e f hef
  change cov[fun g=>goeMatrix r g e.1.1 e.1.2,
    fun g=>goeMatrix r g f.1.1 f.1.2; gaussianCoordinates (MatrixCoordinates (Fin n))]=0
  rw [goe_entry_cov hr]
  have h1 : ¬(e.1.1=f.1.1 ∧ e.1.2=f.1.2) := by
    intro h; apply hef; exact Subtype.ext (Prod.ext h.1 h.2)
  have h2 : ¬(e.1.1=f.1.2 ∧ e.1.2=f.1.1) := by
    intro h
    have he := e.property
    have hf := f.property
    simp only [h.1,h.2] at he
    exact (not_lt_of_ge hf.le) he
  split_ifs <;> simp_all

theorem measurePreserving_goeEdges {r : ℝ} (hr : 0≤r) :
    MeasurePreserving (goeEdges (n:=n) r)
      (gaussianCoordinates (MatrixCoordinates (Fin n)))
      (Measure.pi (fun _ : Edge n=>gaussianReal 0 r.toNNReal)) := by
  refine ⟨(continuous_goeEdges _).measurable,?_⟩
  rw [iIndepFun.map_fun_eq_pi_map (fun e=>(goeEdges_hasLaw hr e).aemeasurable)
    (goeEdges_independent hr)]
  exact congrArg Measure.pi (funext fun e=>(goeEdges_hasLaw hr e).map_eq)

lemma measurePreserving_scaled_edges {r : ℝ} (hr : 0≤r) :
    MeasurePreserving (fun g : Disorder n=>fun e=>sqrt r*g e)
      (gaussianCoordinates (Edge n)) (Measure.pi (fun _ : Edge n=>gaussianReal 0 r.toNNReal)) := by
  refine ⟨by fun_prop,?_⟩
  change (Measure.pi (fun _ : Edge n=>gaussianReal 0 1)).map (fun g e=>sqrt r*g e)=_
  rw [Measure.pi_map_pi (fun _=>by fun_prop)]
  apply congrArg Measure.pi
  funext e
  rw [gaussianReal_map_const_mul]
  congr 1
  · simp
  · apply NNReal.eq
    change (sqrt r)^2*1=↑r.toNNReal
    rw [mul_one,sq_sqrt hr,coe_toNNReal _ hr]

lemma coupling_shifted_goe (j : ℝ) (g : MatrixCoordinates (Fin n)→ℝ) :
    coupling (fun e=>goeEdges (j/(n:ℝ)) g e+j/(n:ℝ)) =
      eraseDiagonal (plantedInteraction j (goeMatrix (j/(n:ℝ)) g)) := by
  ext i k
  by_cases hik : i < k
  · have hne := ne_of_lt hik
    simp [coupling,hik,goeEdges,eraseDiagonal,plantedInteraction,hne,Matrix.vecMulVec]
  · by_cases hki : k < i
    · have hne := ne_of_lt hki
      simp [coupling,hik,hki,goeEdges,eraseDiagonal,plantedInteraction,hne.symm,
        Matrix.vecMulVec,goeMatrix,add_comm]
    · have he : i=k := le_antisymm (le_of_not_gt hki) (le_of_not_gt hik)
      subst k
      simp [coupling,eraseDiagonal]

theorem plus_planted_marginal_probability {j : ℝ} (hj : 0≤j) (A K ε c ρ t : ℝ) :
    ((gaussianCoordinates (Edge n)).prod (Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal)))
      {p | (coupling (plusPlantedEdges (j/(n:ℝ)) p.1),(fun i=>t+p.2 i))∈literalBadPair j A K ε c ρ} =
    ((gaussianCoordinates (MatrixCoordinates (Fin n))).prod
      (Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal)))
      (erasedPlantedRootBad n j A K ε c ρ t) := by
  let r := j/(n:ℝ)
  have hr : 0≤r := div_nonneg hj (Nat.cast_nonneg _)
  let ν := Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal)
  let E := {p : Disorder n × Field n |
    (coupling (fun e=>p.1 e+r),(fun i=>t+p.2 i))∈literalBadPair j A K ε c ρ}
  have hmap : Continuous (fun p : Disorder n × Field n=>
      (coupling (fun e=>p.1 e+r),(fun i=>t+p.2 i)) :
      Disorder n × Field n → Matrix (Fin n) (Fin n) ℝ × Field n) :=
    (continuous_coupling.comp (by fun_prop)).prodMk (by fun_prop)
  have hmmap : Measurable (fun p : Disorder n × Field n=>
      (coupling (fun e=>p.1 e+r),(fun i=>t+p.2 i)) :
      Disorder n × Field n → Matrix (Fin n) (Fin n) ℝ × Field n) := hmap.measurable
  have hE : MeasurableSet E := (measurableSet_literalBadPair j A K ε c ρ).preimage hmmap
  have h1 := ((measurePreserving_scaled_edges (n:=n) hr).prod (MeasurePreserving.id ν)).measure_preimage hE.nullMeasurableSet
  have h2 := ((measurePreserving_goeEdges (n:=n) hr).prod (MeasurePreserving.id ν)).measure_preimage hE.nullMeasurableSet
  calc
    _ = _ := h1
    _ = ((gaussianCoordinates (MatrixCoordinates (Fin n))).prod ν)
        ((Prod.map (goeEdges r) id) ⁻¹' E) := h2.symm
    _ = _ := by
      congr 1
      ext p
      change (coupling (fun e=>goeEdges r p.1 e+r),fun i=>t+p.2 i)∈literalBadPair j A K ε c ρ ↔ _
      rw [coupling_shifted_goe]
      rfl
end SKGap.ObservationBridge

end
end

end OAI
