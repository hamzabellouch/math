import Mathlib
import OAI.Combinatorics.IndependentSets.Reduction.DyadicPrecision
import OAI.Combinatorics.IndependentSets.Geometry.CoordinateAverage

namespace OAI

namespace LargeIndependentSets
open MeasureTheory Set
open scoped BigOperators Classical unitInterval NNReal

noncomputable def clampCube {n : ℕ} (x : Fin n → ℝ) : Fin n → I :=
  fun i => projIcc 0 1 (by norm_num) (x i)

lemma clampCube_lipschitz (n : ℕ) : LipschitzWith 1 (@clampCube n) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff (dist_nonneg)).mpr
  intro i
  exact ((LipschitzWith.projIcc (by norm_num : (0:ℝ) ≤ 1)).dist_le_mul (x i) (y i)).trans
    (by simpa using (dist_le_pi_dist x y i))

lemma clampCube_coe {n : ℕ} (x : Fin n → I) : clampCube (fun i => (x i : ℝ)) = x := by
  funext i
  exact projIcc_of_mem (by norm_num) (x i).property

lemma cube_coe_preserving (n : ℕ) :
    MeasurePreserving (fun x : Fin n → I => fun i => (x i : ℝ))
      volume (BooleanJunta.unitCubeLaw n) := by
  exact measurePreserving_pi (fun _ => (volume : Measure I))
    (fun _ => BooleanJunta.unitLaw) (fun _ => unitInterval.measurePreserving_coe)

lemma cube_average_clamp {n : ℕ} (S : Finset (Fin n))
    {f : (Fin n → I) → ℝ} (hf : Measurable f) (x : Fin n → I) :
    ProductAveraging.average BooleanJunta.unitLaw S (f ∘ clampCube) (fun i => (x i : ℝ)) =
      coordinateAverage S f x := by
  let g : (Fin n → ℝ) → ℝ := fun y => f (clampCube (ProductAveraging.mix S ((fun i => (x i : ℝ)),y)))
  have hg : Measurable g := hf.comp ((clampCube_lipschitz n).continuous.measurable.comp
    ((ProductAveraging.mix_measurable S).comp (measurable_const.prodMk measurable_id)))
  have h := ProductAveraging.integral_preserving (cube_coe_preserving n) hg.aestronglyMeasurable
  change (∫ y, g y ∂BooleanJunta.unitCubeLaw n) = _
  rw [← h]
  unfold coordinateAverage
  apply integral_congr_ae
  filter_upwards [] with y
  dsimp [g]
  congr 1
  funext i
  by_cases hi : i ∈ S <;> simp [clampCube, ProductAveraging.mix, hi, projIcc_of_mem, (x i).property, (y i).property]

theorem cubeJunta : CubeJuntaStatement := by
  intro L τ hτ
  obtain ⟨J,hJ,H⟩ := BooleanJunta.real_cube_junta_uniform L (sq_pos_of_pos hτ)
  refine ⟨J,hJ,?_⟩
  intro n hn f hf hb
  have he : LipschitzWith L (f ∘ clampCube (n:=n)) := by
    simpa using hf.comp (clampCube_lipschitz n)
  obtain ⟨S,hS,hi,herr⟩ := H n (f ∘ clampCube) he (fun x => hb _)
  have hpoint (x : Fin n → I) :
      ((f ∘ clampCube) (fun i => (x i : ℝ)) -
        ProductAveraging.average BooleanJunta.unitLaw S (f ∘ clampCube) (fun i => (x i : ℝ)))^2 =
      (f x-coordinateAverage S f x)^2 := by
    rw [cube_average_clamp S hf.continuous.measurable]
    simp only [Function.comp_def, clampCube_coe]
  have hi' := (cube_coe_preserving n).integrable_comp_of_integrable hi
  refine ⟨S,hS,?_,?_⟩
  · change Integrable (fun x => (f x-coordinateAverage S f x)^2) volume
    convert hi' using 1
    funext x
    exact (hpoint x).symm
  · have ht := ProductAveraging.integral_preserving (cube_coe_preserving n) hi.aestronglyMeasurable
    simp only [hpoint] at ht
    exact ht.trans_lt herr

end LargeIndependentSets

end OAI
