import Mathlib
import OAI.Probability.SKBarriers.Interpolation.ZeroFieldEndpoint

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 1900] cascadeNormedGroup cascadeNormedSpace
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def scalarStep (m v : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  gaussianStep m (fun z : ℝ × ℝ => f (z.1+v*z.2))

def scalarHierarchy : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ) → (ℝ → ℝ) → ℝ → ℝ
  | 0,_,_,f => f
  | n+1,m,v,f => scalarHierarchy n (fun i => m i.castSucc) (fun i => v i.castSucc)
      (scalarStep (m (Fin.last n)) (v (Fin.last n)) f)

@[simp] theorem scalarStep_zero (m : ℝ) (f : ℝ → ℝ) : scalarStep m 0 f = f := by
  simp only [scalarStep,zero_mul,add_zero]
  exact gaussianStep_prefix f m

section Cascade
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def cascadeCoordinate : (n : ℕ) → Fin n → CascadeSpace E n → ℝ
  | 0,i => Fin.elim0 i
  | n+1,i => Fin.lastCases (fun z => z.2) (fun j z => cascadeCoordinate n j z.1) i

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
@[simp] theorem cascadeCoordinate_last (n : ℕ) (z : CascadeSpace E (n+1)) :
    cascadeCoordinate (n+1) (Fin.last n) z = z.2 := by simp [cascadeCoordinate]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
@[simp] theorem cascadeCoordinate_castSucc (n : ℕ) (i : Fin n) (z : CascadeSpace E (n+1)) :
    cascadeCoordinate (n+1) i.castSucc z = cascadeCoordinate n i z.1 := by
  simp [cascadeCoordinate]

theorem cascadePressure_single_coordinate (n : ℕ) (m : Fin n → ℝ) (f : ℝ → ℝ)
    (g : E → ℝ) (v : ℝ) (i : Fin n) :
    cascadePressure n m (fun z => f (g (cascadeRoot (E := E) n z)+v*cascadeCoordinate n i z)) =
      fun x => scalarStep (m i) v f (g x) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [cascadeCoordinate_last,cascadePressure]
      change cascadePressure n (fun j => m j.castSucc)
        (fun z => scalarStep (m (Fin.last n)) v f (g (cascadeRoot (E := E) n z))) = _
      exact cascadePressure_root (E := E) n (fun j => m j.castSucc)
        (fun x => scalarStep (m (Fin.last n)) v f (g x))
    · simp only [cascadeCoordinate_castSucc,cascadePressure]
      change cascadePressure n (fun j => m j.castSucc)
        (gaussianStep (m (Fin.last n)) (fun z =>
          f (g (cascadeRoot (E := E) n z.1)+v*cascadeCoordinate n j z.1))) = _
      rw [gaussianStep_prefix (fun z => f (g (cascadeRoot (E := E) n z)+v*cascadeCoordinate n j z))
        (m (Fin.last n))]
      exact ih _ j
end Cascade

theorem coordinateProjection_append_tail (a b : ℕ) (i : Fin b)
    (z : CascadeSpace (ParameterSpace a) b) :
    coordinateProjection (a+b) (Fin.natAdd a i) (parameterAppend a b z) =
      cascadeCoordinate b i z := by
  induction b with
  | zero => exact Fin.elim0 i
  | succ b ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [Fin.natAdd_last,parameterAppend,coordinateProjection,cascadeCoordinate]
    · simp only [Fin.natAdd_castSucc,cascadeCoordinate_castSucc]
      change coordinateProjection ((a+b)+1) (Fin.natAdd a j).castSucc
        (parameterAppend a b z.1,z.2) = _
      rw [coordinateProjection_castSucc]
      exact ih _ z.1

theorem hierarchyPressure_scalar_linear (n : ℕ) (m v : Fin n → ℝ) (f c : ℝ → ℝ) :
    hierarchyPressure n m (fun z => f (c (parameter n z)+∑ j, v j*coordinateProjection n j z)) =
      fun x => scalarHierarchy n m v f (c x) := by
  induction n generalizing f with
  | zero => simp [hierarchyPressure,scalarHierarchy,parameter]
  | succ n ih =>
    have he : (fun z : ParameterSpace (n+1) =>
        f (c (parameter (n+1) z)+∑ j, v j*coordinateProjection (n+1) j z)) =
        fun z => f ((c (parameter n z.1)+∑ j : Fin n, v j.castSucc*coordinateProjection n j z.1)+
          v (Fin.last n)*z.2) := by
      funext z
      rw [Fin.sum_univ_castSucc]
      simp [coordinateProjection,parameter,add_assoc]
    rw [he,hierarchyPressure]
    change hierarchyPressure n (fun j => m j.castSucc)
      (fun z => scalarStep (m (Fin.last n)) (v (Fin.last n)) f
        (c (parameter n z)+∑ j, v j.castSucc*coordinateProjection n j z)) = _
    rw [ih]
    rfl
end SK.Analytic

end
end

end

end OAI
