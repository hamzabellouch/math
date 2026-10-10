import Mathlib
import OAI.Analysis.Conductivity.Flux.C1WeakDivergence
import OAI.Analysis.Conductivity.Sobolev.AxialPairRank

namespace OAI


noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma axialPair_mem_regularRegion_of_model
    {f F : Coord3 → ℝ} {A B : Coord3 → Symmetric3} {x : Coord3}
    (hF : ContDiff ℝ (↑(⊤:ℕ∞)) F)
    (hB : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y => (B y).val))
    (hf : f =ᶠ[𝓝 x] F) (hA : A =ᶠ[𝓝 x] B)
    {i : Fin 3} (hi : i≠0) (hd : direction (Pi.single i 1) F x≠0)
    {U : Set Coord3} (hU : IsOpen U) (hx : x∈U) :
    x∈regularRegion (axialPair f) A U := by
  have hc : Continuous (direction (Pi.single i 1) F) :=
    direction_continuous (hF.of_le (by simp)) _
  have hn : ∀ᶠ y in 𝓝 x,direction (Pi.single i 1) F y≠0 :=
    (isOpen_ne_fun hc continuous_const).mem_nhds hd
  have hh : {y | y∈U ∧ f y=F y ∧ A y=B y ∧ direction (Pi.single i 1) F y≠0}∈𝓝 x := by
    filter_upwards [hU.mem_nhds hx,hf,hA,hn] with y hy hfy hAy hny
    exact ⟨hy,hfy,hAy,hny⟩
  obtain ⟨O,hOsub,hO,hxO⟩ := mem_nhds_iff.mp hh
  refine mem_regularRegion_iff.mpr ⟨O,fun y hy => (hOsub hy).1,?_,hxO⟩
  apply (axialPair_regularPatch hF hB hi hO (fun y hy => (hOsub hy).2.2.2)).congr
  · intro y hy
    simp only [axialPair,(hOsub hy).2.1]
  · intro y hy
    exact (hOsub hy).2.2.1

lemma axialPair_mem_regularRegion_of_zero
    {f : Coord3 → ℝ} {A B : Coord3 → Symmetric3} {x : Coord3}
    (hB : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y => (B y).val))
    (hf : f =ᶠ[𝓝 x] fun _ => 0) (hA : A =ᶠ[𝓝 x] B)
    {U : Set Coord3} (hU : IsOpen U) (hx : x∈U) :
    x∈regularRegion (axialPair f) A U := by
  have hh : {y | y∈U ∧ f y=0 ∧ A y=B y}∈𝓝 x := by
    filter_upwards [hU.mem_nhds hx,hf,hA] with y hy hfy hAy
    exact ⟨hy,hfy,hAy⟩
  obtain ⟨O,hOsub,hO,hxO⟩ := mem_nhds_iff.mp hh
  have hp : RegularPatch (axialPair (fun _ => 0)) B O :=
    ⟨hO,(axialPair_smooth contDiff_const).contDiffOn,hB.contDiffOn,axialPair_zero_rank O⟩
  refine mem_regularRegion_iff.mpr ⟨O,fun y hy => (hOsub hy).1,?_,hxO⟩
  apply hp.congr
  · intro y hy
    simp only [axialPair,(hOsub hy).2.1]
  · intro y hy
    exact (hOsub hy).2.2

lemma pureModeValue_smooth {f : ℝ → ℝ} (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) (a : Fin 3) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (pureModeValue f a) := by
  unfold pureModeValue
  fun_prop

lemma pureModeTensor_smooth {f : Coord3 → ℝ} (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) (a : Fin 3) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (fun x => pureModeTensor (f x) a) := by
  apply contDiff_pi.mpr; intro i
  apply contDiff_pi.mpr; intro j
  simp only [pureModeTensor,Matrix.diagonal_apply]
  split_ifs <;> first | exact hf | exact contDiff_const

lemma crossingTensor_smooth (L : ℝ) (a b : Fin 3) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (crossingTensor L a b) := by
  have hf := crossingResidualFirst_smooth L
  have hg := crossingResidualSecond_smooth L
  have hff := crossingFirst_smooth L
  have hgg := crossingSecond_smooth L
  have hxx : ContDiff ℝ (↑(⊤:ℕ∞)) (fun x : Coord3 => crossingXX L (x 0) (x a) (x b)) := by
    unfold crossingXX crossingHxx
    fun_prop (disch := intro x; positivity)
  have hyy : ContDiff ℝ (↑(⊤:ℕ∞)) (fun x : Coord3 => crossingYY L (x 0) (x a) (x b)) := by
    unfold crossingYY crossingHxx
    fun_prop (disch := intro x; positivity)
  have hxy : ContDiff ℝ (↑(⊤:ℕ∞)) (fun x : Coord3 => crossingXY L (x 0) (x a) (x b)) := by
    unfold crossingXY crossingHxy
    fun_prop (disch := intro x; positivity)
  apply contDiff_pi.mpr; intro i
  apply contDiff_pi.mpr; intro j
  unfold crossingTensor
  split_ifs <;> fun_prop

end ScalarConductivity

end

end OAI
