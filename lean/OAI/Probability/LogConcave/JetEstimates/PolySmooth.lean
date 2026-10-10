import Mathlib
import OAI.Probability.LogConcave.Sampling.AdjointCoordinateContinuous

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace NNReal

structure PolySmooth {d : ℕ} (f : Point d → ℝ) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) f
  growth : ∀l : List (Point d),HasPolynomialGrowth (JetCalculus.jet id l f)

namespace PolySmooth
variable {d : ℕ} {f g H : Point d → ℝ}

lemma jet_growth (hf : PolySmooth f) {ι : Type*} (b : ι → Point d) (l : List ι) :
    HasPolynomialGrowth (JetCalculus.jet b l f) := by
  have hh := hf.growth (l.map b)
  simpa only [JetCalculus.jet_map,Function.id_comp] using hh

lemma directional (hf : PolySmooth f) (v : Point d) : PolySmooth (LogConcaveSampling.directional v f) := by
  refine ⟨directional_smooth hf.smooth v,fun l => ?_⟩
  have he : JetCalculus.jet id [v] f=LogConcaveSampling.directional v f := rfl
  have hh := hf.growth (l++[v])
  rw [JetCalculus.jet_append,he] at hh
  exact hh

lemma jet (hf : PolySmooth f) {ι : Type*} (b : ι → Point d) (l : List ι) :
    PolySmooth (JetCalculus.jet b l f) := by
  induction l with
  | nil => exact hf
  | cons i l ih => exact ih.directional (b i)

lemma polyC1 (hf : PolySmooth f) : PolyC1 f :=
  ⟨hf.smooth.of_le (by simp),hf.growth [],fun v => (hf.directional v).growth []⟩

lemma add (hf : PolySmooth f) (hg : PolySmooth g) : PolySmooth (fun x => f x+g x) := by
  refine ⟨hf.smooth.add hg.smooth,fun l => ?_⟩
  rw [JetCalculus.jet_add hf.smooth hg.smooth]
  exact Appell.HasGrowth.add (hf.growth l) (hg.growth l)

lemma neg (hf : PolySmooth f) : PolySmooth (fun x => -f x) := by
  refine ⟨hf.smooth.neg,fun l => ?_⟩
  rw [jet_neg hf.smooth]
  simpa only [HasPolynomialGrowth,Appell.HasGrowth,neg_one_mul] using
    Appell.HasGrowth.mul (growth_const (-1:ℝ)) (hf.growth l)

lemma mul (hf : PolySmooth f) (hg : PolySmooth g) : PolySmooth (fun x => f x*g x) := by
  refine ⟨hf.smooth.mul hg.smooth,fun l => ?_⟩
  induction l generalizing f g with
  | nil => exact Appell.HasGrowth.mul (hf.growth []) (hg.growth [])
  | cons v l ih =>
    change HasPolynomialGrowth (LogConcaveSampling.directional v
      (JetCalculus.jet id l (fun x => f x*g x)))
    rw [←jet_directional (hf.smooth.mul hg.smooth),
      directional_mul hf.polyC1.differentiable hg.polyC1.differentiable,
      JetCalculus.jet_add ((hf.directional v).smooth.mul hg.smooth)
        (hf.smooth.mul (hg.directional v).smooth)]
    exact Appell.HasGrowth.add (ih (hf.directional v) hg) (ih hf (hg.directional v))

lemma sum {ι : Type*} (s : Finset ι) {f : ι → Point d → ℝ}
    (hf : ∀i∈s,PolySmooth (f i)) : PolySmooth (fun x => ∑i∈s,f i x) := by
  refine ⟨ContDiff.sum (fun i hi => (hf i hi).smooth),fun l => ?_⟩
  rw [JetCalculus.jet_sum s (fun i hi => (hf i hi).smooth)]
  exact Appell.HasGrowth.sum s (fun i hi => (hf i hi).growth l)

lemma adjoint (hH : PolySmooth H) (hf : PolySmooth f) (v : Point d) :
    PolySmooth (adjointCoordinate H v f) :=
  (hf.directional v).neg.add ((hH.directional v).mul hf)

lemma const (c : ℝ) : PolySmooth (fun _ : Point d => c) := by
  refine ⟨contDiff_const,fun l => ?_⟩
  rw [JetCalculus.jet_const]
  split_ifs <;> exact growth_const _

lemma prod {ι : Type*} (s : Finset ι) {f : ι → Point d → ℝ}
    (hf : ∀i∈s,PolySmooth (f i)) : PolySmooth (fun x => ∏i∈s,f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using const (d:=d) 1
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).mul
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma integrable (hf : PolySmooth f) (hH : Continuous H) (ht : HasGaussianLowerTail H) :
    Integrable f (gibbs H) :=
  integrable_polynomial_gibbs hH ht hf.smooth.continuous (hf.growth [])

lemma tensorAdjoint {ι : Type*} [Fintype ι] {V : ι → Point d → ℝ}
    (hH : PolySmooth H) (hV : ∀i,PolySmooth (V i)) (b : ι → Point d) :
    PolySmooth (LogConcaveSampling.tensorAdjoint H b V) :=
  sum Finset.univ (fun i _ => hH.adjoint (hV i) (b i))
end PolySmooth
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
