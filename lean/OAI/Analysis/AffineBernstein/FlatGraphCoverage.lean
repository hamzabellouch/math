import Mathlib
import OAI.Analysis.AffineBernstein.GaussCoordinates
import OAI.Analysis.AffineBernstein.FlatProductCoordinates
import OAI.Analysis.AffineBernstein.FiniteProjectiveCharts

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section FlatGraphCoverage
variable {S E F : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma flatGraphChart_covers_direction {n : ℕ} (Ω : Set (Space n)) (u : Space n → ℝ)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    (bS : OrthonormalBasis ι ℝ S) (bF : OrthonormalBasis κ ℝ F)
    (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E) (e : Fin n ≃ ι ⊕ κ)
    (φ : OpenPartialHomeomorph (Space n) (Space n)) {D Q : Set S}
    (hsource : φ.source = {x | (flatProductCoordinates bS bF e x).1 ∈ D})
    (heφ : ∀ x ∈ φ.source, a+L ((flatProductCoordinates bS bF e x).1,
      gaussPoint {y | ((flatProductCoordinates bS bF e x).1,y) ∈ affineEpigraphPullback Ω u a L}
        (f (WithLp.toLp 2 ((flatProductCoordinates bS bF e x).2,(1:ℝ))))) = (φ x,u (φ x)))
    (hQD : Q ⊆ D) {s : S} (hs : s ∈ Q) {y v : E}
    (hgauss : ∀ c : ℝ, 0 < c → gaussPoint {q | (s,q) ∈ affineEpigraphPullback Ω u a L} (c • v) = y)
    (hdir : 0 < inner ℝ v (projectiveAxis f)) :
    (a+L (s,y)).1 ∈ φ '' ((flatProductCoordinates bS bF e) ⁻¹' (Q ×ˢ Set.univ)) := by
  let Z := flatProductCoordinates bS bF e
  let c := (inner ℝ v (projectiveAxis f))⁻¹
  have hc : 0 < c := inv_pos.mpr hdir
  let p := f.symm (c • v)
  have hp : (WithLp.ofLp p).2 = 1 := by
    rw [← projectiveAxis_inner f (c • v)]
    simp only [inner_smul_left,conj_trivial]
    exact inv_mul_cancel₀ hdir.ne'
  let x := Z.symm (s,(WithLp.ofLp p).1)
  have hx : Z x = (s,(WithLp.ofLp p).1) := Z.apply_symm_apply _
  have hxQ : x ∈ Z ⁻¹' (Q ×ˢ univ) := by simp only [mem_preimage,hx,mem_prod,mem_univ,and_true]; exact hs
  have hxs : x ∈ φ.source := by rw [hsource]; change (Z x).1 ∈ D; rw [hx]; exact hQD hs
  have hflat : f (WithLp.toLp 2 ((WithLp.ofLp p).1,(1:ℝ))) = c • v := by
    rw [← hp]
    change f p = c • v
    exact f.apply_symm_apply _
  refine ⟨x,hxQ,?_⟩
  have h := heφ x hxs
  change a+L ((Z x).1,gaussPoint _ (f (WithLp.toLp 2 ((Z x).2,(1:ℝ))))) = _ at h
  rw [hx,hflat,hgauss c hc] at h
  exact (congrArg Prod.fst h).symm

end FlatGraphCoverage

-- WholeGraphAreaTransport

end
end AffineBernstein
end

end OAI
