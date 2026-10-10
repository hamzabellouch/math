import Mathlib
import OAI.Analysis.AffineBernstein.NoOrthant
import OAI.Analysis.AffineBernstein.ModelCenteringFurther
import OAI.Analysis.AffineBernstein.AffineImageCoordinates

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section NoZeroTransverse
lemma IsModelShape.zero_transverse_mem {k : ℕ} {C : Set (Space k × Space 0)}
    (hC : IsModelShape C) (p : Space k × Space 0) :
    p ∈ C ↔ ∀ i, 0 ≤ p.1 i := by
  constructor
  · exact hC.support p
  · intro hp
    have hz : p.2 = 0 := Subsingleton.elim _ _
    simpa only [← hz] using hC.orthant p.1 hp

lemma IsModelShape.zero_transverse_orthant {n : ℕ} {C : Set (Space (n+1) × Space 0)}
    (hC : IsModelShape C) :
    ((ContinuousLinearEquiv.prodUnique ℝ (Space (n+1)) (Space 0)).trans
      (extendBaseEquiv n).symm) '' C = ambientOrthant n := by
  let B := (ContinuousLinearEquiv.prodUnique ℝ (Space (n+1)) (Space 0)).trans
      (extendBaseEquiv n).symm
  change B '' C = _
  ext z
  have he : z ∈ B '' C ↔ B.symm z ∈ C := by
    constructor
    · rintro ⟨p,hp,rfl⟩
      simpa only [B.symm_apply_apply] using hp
    · intro hp
      exact ⟨B.symm z,hp,B.apply_symm_apply z⟩
  rw [he]
  change B.symm z ∈ C ↔ ∀ i, 0 ≤ ambientCoordinates n z i
  rw [hC.zero_transverse_mem]
  constructor
  · intro hz i
    cases i with
    | inl i => exact hz i.succ
    | inr i =>
      rw [ambientCoordinates_inr]
      exact hz 0
  · intro hz i
    refine Fin.cases ?_ (fun j => ?_) i
    · change 0 ≤ z.2
      simpa only [ambientCoordinates_inr] using hz (Sum.inr ())
    · exact hz (Sum.inl j)

/-- A pure orthant cannot lie in the actual full affine local-limit family. -/
theorem complete_affineMaximal_no_orthant_family {n : ℕ} (hn : 0 < n)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hcv : Convex ℝ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (hc : EuclideanGraphComplete Ω u) :
    ¬ InAffineLimitFamily (sourceEpigraph Ω u) (ambientOrthant n) := by
  intro hf
  obtain ⟨A,hA⟩ := hf.approximation
  let L := fun j => (A j).toAffineEquiv.linear.toContinuousLinearEquiv
  let v := fun j => A j 0
  apply complete_affineMaximal_no_orthant_limit hn hΩ hne hcv hu hp hm hc L v
  have he j : (fun z => L j z + v j) = A j := by
    funext z
    exact (continuousAffineEquiv_decomposition (A j) z).symm
  simpa only [he] using hA

/-- The transverse dimension of every actual model is positive; this is the
nontrivial m=0 part of the manuscript, using the original PDE cap lower mass. -/
theorem complete_affineMaximal_model_transverse_pos {n k m : ℕ} (hn : 0 < n)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hcv : Convex ℝ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (hc : EuclideanGraphComplete Ω u)
    {C : Set (Space k × Space m)} (hC : IsModelShape C)
    (hf : InAffineLimitFamily (sourceEpigraph Ω u) C) : 1 ≤ m := by
  by_contra hm0
  have hm0' : m = 0 := by omega
  subst m
  have hdim := model_dimension hf
  have hk : k = n+1 := by simpa [Module.finrank_prod,finrank_euclideanSpace] using hdim
  subst k
  have hcl := sourceEpigraph_closed hΩ hne hcv hu hp hc
  have hned : (sourceEpigraph Ω u).Nonempty := by
    obtain ⟨x,hx⟩ := hne
    exact ⟨(x,u x),hx,le_rfl⟩
  apply complete_affineMaximal_no_orthant_family hn hΩ hne hcv hu hp hm hc
  rw [← hC.zero_transverse_orthant]
  exact hf.affine_image hcl hned
    (((ContinuousLinearEquiv.prodUnique ℝ (Space (n+1)) (Space 0)).trans
      (extendBaseEquiv n).symm).toContinuousAffineEquiv)
end NoZeroTransverse


end
end AffineBernstein
end

end OAI
