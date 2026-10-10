import Mathlib
import OAI.Probability.SKGap.Model

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
namespace SKGap.ComplexSpectral
variable {ι : Type*} [Fintype ι]

def quadratic (M : Matrix ι ι ℂ) (x : EuclideanSpace ℂ ι) : ℝ :=
  (dotProduct (star x.ofLp) (M *ᵥ x.ofLp)).re

def unitSphere (ι : Type*) [Fintype ι] : Set (EuclideanSpace ℂ ι) := Metric.sphere 0 1

def lowerRayleigh (M : Matrix ι ι ℂ) : ℝ := sInf (quadratic M '' unitSphere ι)

lemma continuous_quadratic :
    Continuous (fun p : Matrix ι ι ℂ × EuclideanSpace ℂ ι => quadratic p.1 p.2) := by
  unfold quadratic dotProduct mulVec
  fun_prop

lemma compact_unitSphere : IsCompact (unitSphere ι) := isCompact_sphere _ _

lemma continuous_lowerRayleigh : Continuous (lowerRayleigh (ι := ι)) :=
  compact_unitSphere.continuous_sInf continuous_quadratic

lemma quadratic_neg (M : Matrix ι ι ℂ) (x : EuclideanSpace ℂ ι) :
    quadratic (-M) x = -quadratic M x := by simp [quadratic,Matrix.neg_mulVec,dotProduct_neg]

lemma lowerRayleigh_le (M : Matrix ι ι ℂ) {x : EuclideanSpace ℂ ι}
    (hx : x ∈ unitSphere ι) : lowerRayleigh M ≤ quadratic M x := by
  have hb : BddBelow (quadratic M '' unitSphere ι) :=
    (compact_unitSphere.image (continuous_quadratic.comp (continuous_const.prodMk continuous_id))).bddBelow
  exact csInf_le hb ⟨x,hx,rfl⟩

lemma lowerRayleigh_ge [Nonempty ι] {M : Matrix ι ι ℂ} {c : ℝ}
    (hc : ∀ x ∈ unitSphere ι, c ≤ quadratic M x) : c ≤ lowerRayleigh M := by
  classical
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hn : (quadratic M '' unitSphere ι).Nonempty := by
    refine ⟨quadratic M (EuclideanSpace.single i (1:ℂ)),?_⟩
    exact ⟨_,by simp [unitSphere],rfl⟩
  exact le_csInf hn (by rintro _ ⟨x,hx,rfl⟩; exact hc x hx)

variable [DecidableEq ι]

lemma quadratic_eigenvector {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (i : ι) :
    quadratic M (hM.eigenvectorBasis i) = hM.eigenvalues i := by
  exact (hM.eigenvalues_eq i).symm

lemma eigenvalue_lower_bound {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (i : ι) :
    lowerRayleigh M ≤ hM.eigenvalues i := by
  rw [← quadratic_eigenvector hM i]
  apply lowerRayleigh_le
  simpa only [unitSphere,Metric.mem_sphere,dist_zero_right] using hM.eigenvectorBasis.orthonormal.1 i

lemma eigenvalue_upper_bound {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (i : ι) :
    hM.eigenvalues i ≤ -lowerRayleigh (-M) := by
  have hh := lowerRayleigh_le (-M) (x := hM.eigenvectorBasis i)
    (by simpa only [unitSphere,Metric.mem_sphere,dist_zero_right] using hM.eigenvectorBasis.orthonormal.1 i)
  rw [quadratic_neg,quadratic_eigenvector] at hh
  linarith

lemma spectral_interval_eventually {S : ℝ → Matrix ι ι ℂ} {t lo hi : ℝ}
    (hS : ContinuousAt S t) (hself : ∀ s, (S s).IsHermitian)
    (hlo : lo < lowerRayleigh (S t)) (hhi : lowerRayleigh (-(S t)) > -hi) :
    ∀ᶠ s in 𝓝 t, ∀ i, (hself s).eigenvalues i ∈ Icc lo hi := by
  have hl := (continuous_lowerRayleigh.continuousAt.comp hS).eventually (lt_mem_nhds hlo)
  have hu := (continuous_lowerRayleigh.continuousAt.comp hS.neg).eventually (lt_mem_nhds hhi)
  filter_upwards [hl,hu] with s hs hs' i
  refine ⟨hs.le.trans (eigenvalue_lower_bound (hself s) i),?_⟩
  have hh := eigenvalue_upper_bound (hself s) i
  change -hi < lowerRayleigh (-(S s)) at hs'
  linarith

end SKGap.ComplexSpectral

noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius

end
end
end
end
end
end
end
end
end
end
end

end OAI
