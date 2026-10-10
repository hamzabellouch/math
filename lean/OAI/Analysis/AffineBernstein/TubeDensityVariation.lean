import Mathlib
import OAI.Analysis.AffineBernstein.DeterminantVariation
import OAI.Analysis.AffineBernstein.JetCalculus
import OAI.Analysis.AffineBernstein.TubeFrame

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section TubeDensityVariation
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def tubeAreaDensity (B : Matrix ι ι ℝ) (R : Matrix κ κ ℝ) (δ : ℝ) : ℝ :=
  Real.rpow B.det δ * Real.rpow R.det (1-δ)

/- Literal Jacobi first variation of the tube density, including empty
angular matrices. This is the integrand needed in source (tube-euler). -/
lemma hasDerivAt_tubeAreaDensity (B D : Matrix ι ι ℝ) (R T : Matrix κ κ ℝ)
    (hB : B.PosDef) (hR : R.PosDef) (δ : ℝ) :
    HasDerivAt (fun t : ℝ => tubeAreaDensity (B + t • D) (R + t • T) δ)
      (δ * Real.rpow B.det (δ-1) * Real.rpow R.det (1-δ) *
        (∑ i, ∑ j, B.adjugate j i * D i j) +
       (1-δ) * Real.rpow B.det δ * Real.rpow R.det (-δ) *
        (∑ i, ∑ j, R.adjugate j i * T i j)) 0 := by
  have hd := (hasDerivAt_affineArea_matrix B D hB δ).mul
    (hasDerivAt_affineArea_matrix R T hR (1-δ))
  simp only [zero_smul, add_zero] at hd
  convert! hd using 1
  simp only [show 1-δ-1 = -δ by ring, Real.rpow_eq_pow]
  ring

end TubeDensityVariation

open Matrix
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

lemma second_fderiv_affine_comp {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : F → G} (L : S →L[ℝ] F) (a : F)
    {x : S} (hf : ContDiffAt ℝ ∞ f (a + L x)) (v w : S) :
    fderiv ℝ (fderiv ℝ (fun z => f (a + L z))) x v w =
      fderiv ℝ (fderiv ℝ f) (a + L x) (L v) (L w) := by
  have hd (z : S) : fderiv ℝ (fun z => a + L z) z = L := by
    exact ((L.hasFDerivAt).const_add a).fderiv
  have hdd : fderiv ℝ (fderiv ℝ (fun z => a + L z)) x = 0 := by
    rw [show fderiv ℝ (fun z => a + L z) = (fun _ => L) from funext hd]
    simp
  change fderiv ℝ (fderiv ℝ (f ∘ (fun z => a + L z))) x v w = _
  rw [second_fderiv_comp (g := fun z => a + L z) hf (contDiffAt_const.add L.contDiff.contDiffAt), hd, hdd]
  simp

lemma second_fderiv_prod_left {H : S × E → ℝ} {s : S} {e : E}
    (hH : ContDiffAt ℝ ∞ H (s,e)) (v w : S) :
    fderiv ℝ (fderiv ℝ (fun y => H (y,e))) s v w =
      fderiv ℝ (fderiv ℝ H) (s,e) (v,0) (w,0) := by
  simpa using second_fderiv_affine_comp (ContinuousLinearMap.inl ℝ S E) (0,e) (by simpa using hH) v w

lemma second_fderiv_prod_right {H : S × E → ℝ} {s : S} {e : E}
    (hH : ContDiffAt ℝ ∞ H (s,e)) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => H (s,y))) e v w =
      fderiv ℝ (fderiv ℝ H) (s,e) (0,v) (0,w) := by
  simpa using second_fderiv_affine_comp (ContinuousLinearMap.inr ℝ S E) (s,0) (by simpa using hH) v w

lemma bilinear_matrix_posDef {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : F →L[ℝ] F →L[ℝ] ℝ) (b : ι → F)
    (hb : LinearIndependent ℝ b) (hsym : ∀ v w, A v w = A w v)
    (hp : ∀ z : ι → ℝ, (∑ i, z i • b i) ≠ 0 →
      0 < A (∑ i, z i • b i) (∑ i, z i • b i)) :
    (Matrix.of fun i j => A (b i) (b j)).PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨?_, fun z hz => ?_⟩
  · rw [Matrix.IsHermitian]
    ext i j
    simpa [Matrix.conjTranspose_apply] using hsym (b j) (b i)
  · have hne : (∑ i, z i • b i) ≠ 0 := by
      intro he
      apply hz
      funext i
      exact (Fintype.linearIndependent_iff.mp hb z he) i
    have h := hp z hne
    simpa [dotProduct, Matrix.mulVec, map_sum, map_smul, Finset.mul_sum,
      mul_assoc, mul_left_comm, mul_comm, hsym] using h

lemma tubeBaseMatrix_posDef {H : S × E → ℝ} {x : S × E}
    (hH : ContDiffAt ℝ ∞ H x) (bS : Module.Basis ι ℝ S)
    (hneg : ∀ v : S, v ≠ 0 → fderiv ℝ (fderiv ℝ H) x (v,0) (v,0) < 0) :
    (tubeBaseMatrix H x bS).PosDef := by
  let A := -(fderiv ℝ (fderiv ℝ H) x)
  have hb : LinearIndependent ℝ (fun i => (bS i, (0:E))) :=
    bS.linearIndependent.map' (ContinuousLinearMap.inl ℝ S E).toLinearMap (by
      apply LinearMap.ker_eq_bot.mpr
      intro x y h; exact congrArg Prod.fst h)
  have hs := hH.isSymmSndFDerivAt (by simp)
  apply bilinear_matrix_posDef A _ hb (fun v w => by simp [A,hs.eq v w])
  intro z hz
  have he : (∑ i, z i • (bS i,(0:E))) = ((∑ i, z i • bS i),0) := by
    apply Prod.ext <;> simp [Prod.fst_sum, Prod.snd_sum]
  rw [he] at hz ⊢
  have hn : (∑ i, z i • bS i) ≠ 0 := by simpa using hz
  exact neg_pos.mpr (hneg _ hn)

lemma tubeRadiusMatrix_posDef {H : S × E → ℝ} {x : S × E}
    (hH : ContDiffAt ℝ ∞ H x) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (he : bE (Sum.inr ()) = x.2)
    (hpos : ∀ v : E, v ≠ 0 → inner ℝ x.2 v = 0 →
      0 < fderiv ℝ (fderiv ℝ H) x (0,v) (0,v)) :
    (tubeRadiusMatrix H x bE).PosDef := by
  have hb : LinearIndependent ℝ (fun i : κ => ((0:S),bE (Sum.inl i))) :=
    (bE.toBasis.linearIndependent.comp _ Sum.inl_injective).map'
      (ContinuousLinearMap.inr ℝ S E).toLinearMap (by
        apply LinearMap.ker_eq_bot.mpr
        intro x y h; exact congrArg Prod.snd h)
  have hs := hH.isSymmSndFDerivAt (by simp)
  apply bilinear_matrix_posDef (fderiv ℝ (fderiv ℝ H) x) _ hb hs.eq
  intro z hz
  have heq : (∑ i, z i • ((0:S),bE (Sum.inl i))) = (0,(∑ i, z i • bE (Sum.inl i))) := by
    apply Prod.ext <;> simp [Prod.fst_sum, Prod.snd_sum]
  rw [heq] at hz ⊢
  apply hpos _ (by simpa using hz)
  rw [← he]
  simp [inner_sum, inner_smul_right, bE.inner_eq_ite]

end AffineBernstein
end

end OAI
