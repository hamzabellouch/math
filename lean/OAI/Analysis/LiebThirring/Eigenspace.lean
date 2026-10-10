import OAI.Analysis.LiebThirring.SpectralMoment

namespace OAI


noncomputable section
namespace SharpLiebThirring.OperatorProof
open MeasureTheory Set Filter
open scoped Topology ENNReal

/-- The true eigenspace, including the operator-domain condition. -/
def eigenSpace (A : L2C →ₗ.[ℂ] L2C) (e : ℝ) : Submodule ℂ L2C :=
  A.graph.comap ((LinearMap.id : L2C →ₗ[ℂ] L2C).prod
    ((e:ℂ) • (LinearMap.id : L2C →ₗ[ℂ] L2C)))

lemma mem_eigenSpace (A : L2C →ₗ.[ℂ] L2C) (e : ℝ) (f : L2C) :
    f ∈ eigenSpace A e ↔ IsOperatorEigenfunction A e f := by
  change (f,(e:ℂ) • f) ∈ A.graph ↔ _
  simp only [LinearPMap.mem_graph_iff,Subtype.exists,exists_and_left,exists_eq_left,
    IsOperatorEigenfunction]

lemma eigenSpace_closed {A : L2C →ₗ.[ℂ] L2C} (hA : IsSelfAdjoint A) (e : ℝ) :
    IsClosed (eigenSpace A e : Set L2C) := by
  change IsClosed ((fun f : L2C ↦ (f,(e:ℂ) • f)) ⁻¹' (A.graph : Set (L2C × L2C)))
  exact hA.isClosed.preimage (continuous_id.prodMk (continuous_id.const_smul (e:ℂ)))

lemma eigenSpace_orthogonal {A : L2C →ₗ.[ℂ] L2C} (hA : IsSelfAdjoint A)
    {e t : ℝ} (het : e ≠ t) {f g : L2C}
    (hf : f ∈ eigenSpace A e) (hg : g ∈ eigenSpace A t) : inner ℂ f g = 0 := by
  obtain ⟨hfd,hfe⟩ := (mem_eigenSpace A e f).mp hf
  obtain ⟨hgd,hge⟩ := (mem_eigenSpace A t g).mp hg
  have hs : A.IsFormalAdjoint A := by
    have h := A.adjoint_isFormalAdjoint hA.dense_domain
    rwa [LinearPMap.isSelfAdjoint_def.mp hA] at h
  have h := hs ⟨f,hfd⟩ ⟨g,hgd⟩
  rw [hfe,hge,inner_smul_left,inner_smul_right] at h
  simp only [Complex.conj_ofReal] at h
  have hc : (e:ℂ) ≠ (t:ℂ) := by exact_mod_cast het
  exact (mul_eq_mul_right_iff.mp h).resolve_left hc

lemma eigenBasis_exists (A : L2C →ₗ.[ℂ] L2C) (hA : IsSelfAdjoint A) (e : ℝ) :
    ∃ I : Set (eigenSpace A e), Nonempty (HilbertBasis I ℂ (eigenSpace A e)) := by
  let : CompleteSpace (eigenSpace A e) := (eigenSpace_closed hA e).completeSpace_coe
  obtain ⟨I,b,_⟩ := exists_hilbertBasis ℂ (eigenSpace A e)
  exact ⟨I,⟨b⟩⟩

def eigenBasisSet (A : L2C →ₗ.[ℂ] L2C) (hA : IsSelfAdjoint A) (e : ℝ) :
    Set (eigenSpace A e) := Classical.choose (eigenBasis_exists A hA e)

def eigenBasis (A : L2C →ₗ.[ℂ] L2C) (hA : IsSelfAdjoint A) (e : ℝ) :
    HilbertBasis (eigenBasisSet A hA e) ℂ (eigenSpace A e) :=
  Classical.choice (Classical.choose_spec (eigenBasis_exists A hA e))

abbrev NegativeEnergy := {e : ℝ // e < 0}
abbrev EigenIndex (A : L2C →ₗ.[ℂ] L2C) (hA : IsSelfAdjoint A) :=
  (e : NegativeEnergy) × eigenBasisSet A hA e.1

def eigenBasisVector (A : L2C →ₗ.[ℂ] L2C) (hA : IsSelfAdjoint A)
    (i : EigenIndex A hA) : L2C := eigenBasis A hA i.1.1 i.2

lemma eigenBasisVector_member (A : L2C →ₗ.[ℂ] L2C) (hA : IsSelfAdjoint A)
    (i : EigenIndex A hA) : IsOperatorEigenfunction A i.1.1 (eigenBasisVector A hA i) :=
  (mem_eigenSpace A i.1.1 _).mp (eigenBasis A hA i.1.1 i.2).2

lemma eigenBasisVector_orthonormal (A : L2C →ₗ.[ℂ] L2C) (hA : IsSelfAdjoint A) :
    Orthonormal ℂ (eigenBasisVector A hA) := by
  classical
  apply orthonormal_iff_ite.mpr
  rintro ⟨e,i⟩ ⟨t,j⟩
  by_cases het : e = t
  · subst t
    have h := orthonormal_iff_ite.mp (eigenBasis A hA e.1).orthonormal i j
    change inner ℂ (eigenBasisVector A hA ⟨e,i⟩) (eigenBasisVector A hA ⟨e,j⟩) =
      if i = j then 1 else 0 at h
    simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using h
  · have hne : e.1 ≠ t.1 := fun h ↦ het (Subtype.ext h)
    have hp : (⟨e,i⟩ : EigenIndex A hA) ≠ ⟨t,j⟩ := fun h ↦ het (congrArg Sigma.fst h)
    rw [ite_eq_right hp]
    exact eigenSpace_orthogonal hA hne (eigenBasis A hA e.1 i).2 (eigenBasis A hA t.1 j).2

/-- The extended sum over every negative eigenvalue, repeated once for each
member of a full Hilbert basis of its eigenspace. This is a literal spectral
sum with multiplicities; no enumeration and no finiteness assumption is made. -/
def eigenvalueSum (γ : ℝ) (A : L2C →ₗ.[ℂ] L2C) (hA : IsSelfAdjoint A) : ℝ≥0∞ :=
  ∑' i : EigenIndex A hA, (ENNReal.ofReal |i.1.1|)^γ

end SharpLiebThirring.OperatorProof

end

end OAI
