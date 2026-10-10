import Mathlib
import OAI.Analysis.HardSphere.PathBounds.VisitCounts
import OAI.Analysis.HardSphere.PathBounds.CertificateUnion

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.FreeVisits
lemma finite_failure_union_finset {W V : Type*} [MeasurableSpace W] [DecidableEq V]
    (μ : Measure W) {q : ℕ} (hq : 0<q) (bad : Fin q→V→W→Prop)
    {p : ℝ≥0∞} (hp : p≤1)
    (hjoint : ∀i : Fin q,∀A : Finset V,μ {ω | ∀v∈A,bad i v ω}≤p^(q*A.card))
    (A : Finset V) :
    μ {ω | ∀v∈A,∃i,bad i v ω}≤((q:ℝ≥0∞)*p)^A.card := by
  let bad' (i : Fin q) (v : A) (ω : W) := bad i v ω
  have hj (i : Fin q) (B : Finset A) :
      μ {ω | ∀v∈B,bad' i v ω}≤p^(q*B.card) := by
    have h := hjoint i (B.image Subtype.val)
    rw [Finset.card_image_of_injective _ Subtype.val_injective] at h
    simpa only [Finset.mem_image,Set.ofPred_forall,forall_exists_index,and_imp,forall_apply_eq_imp_iff₂] using h
  have h := finite_failure_union μ hq bad' hp hj
  convert h using 1
  · congr 1
    ext ω
    simp only [Set.mem_ofPred_eq,Subtype.forall,bad']
  · simp only [Fintype.card_coe]
end HardSphere.FreeVisits
namespace HardSphere.Groups
open PathCutoff FreeVisits CellOrbital BathSlice Wiener HardSphere.Lattice

def certificateBad {N K : ℕ} [Nontrivial (Fin N)] {L : Length}
    (m : ℕ) (r R C S s₀ ell θ H D : ℝ) (u : Time) (i : Fin 6)
    (v : Fin 3→Fin K) (ω : ConfigurationPath N L) : Prop :=
  ![(centeredCount L (gridCenter L v) (ω 0):ℝ)<ell*D,
    θ*D≤((localCloseLabels L s₀ (gridCenter L v) (ω 0)).card:ℝ),
    θ*D≤((localCloseLabels L s₀ (gridCenter L v) (ω 1)).card:ℝ),
    H*D<((visitors (gridCenter L v) ω).card:ℝ),
    ¬(∀i,pathVisitsBall L 12 (gridCenter L v) i ω→Regular m r R C u S (onePathAt i ω)),
    θ*D≤((longVisitors (gridCenter L v) ω).card:ℝ)] i

lemma not_certificate_iff {N K : ℕ} [Nontrivial (Fin N)] {L : Length}
    (m : ℕ) (r R C S s₀ ell θ H D : ℝ) (u : Time) (v : Fin 3→Fin K)
    (ω : ConfigurationPath N L) :
    ¬Certificate m r R C S s₀ ell θ H D u v ω ↔
      ∃i,certificateBad m r R C S s₀ ell θ H D u i v ω := by
  classical
  constructor
  · intro hn
    by_contra h
    have h0 := not_exists.mp h (0:Fin 6)
    have h1 := not_exists.mp h (1:Fin 6)
    have h2 := not_exists.mp h (2:Fin 6)
    have h3 := not_exists.mp h (3:Fin 6)
    have h4 := not_exists.mp h (4:Fin 6)
    have h5 := not_exists.mp h (5:Fin 6)
    simp [certificateBad] at h0 h1 h2 h3 h4 h5
    exact hn ⟨h0,h1,h2,h3,h4,h5⟩
  · rintro ⟨i,hi⟩ h
    fin_cases i
    · exact (not_lt.mpr h.low) hi
    · exact (not_le.mpr h.closeY) hi
    · exact (not_le.mpr h.closeZ) hi
    · exact (not_lt.mpr h.visit) hi
    · exact hi h.regular
    · exact (not_le.mpr h.long) hi

lemma certificate_joint {N K : ℕ} [Nontrivial (Fin N)] {L : Length}
    (m : ℕ) (r R C S s₀ ell θ H D : ℝ) (u : Time)
    (μ : Measure (ConfigurationPath N L)) {p : ℝ≥0∞} (hp : p≤1)
    (hjoint : ∀i : Fin 6,∀A : Finset (Fin 3→Fin K),
      μ {ω | ∀v∈A,certificateBad m r R C S s₀ ell θ H D u i v ω}≤p^(6*A.card))
    (A : Finset (Fin 3→Fin K)) :
    μ {ω | ∀v∈A,¬Certificate m r R C S s₀ ell θ H D u v ω}≤(6*p)^A.card := by
  simp only [not_certificate_iff]
  exact finite_failure_union_finset μ (by norm_num) _ hp hjoint A

end HardSphere.Groups

end
end

end

end OAI
