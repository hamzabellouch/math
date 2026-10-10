import Mathlib
import OAI.Probability.LogConcave.Sampling.CoordinateProjection

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators

lemma Appell.HasGrowth.comp_linear {E F Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup Z]
    {f : F → Z} (hf : Appell.HasGrowth f) (L : E →L[ℝ] F) :
    Appell.HasGrowth (fun x => f (L x)) := by
  obtain ⟨C,hC,n,hf⟩ := hf
  refine ⟨C*(1+‖L‖^n),by positivity,n,fun x => (hf (L x)).trans ?_⟩
  have hp : ‖L x‖^n≤‖L‖^n*‖x‖^n := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (L.le_opNorm x) n
  have hLn := pow_nonneg (norm_nonneg L) n
  have hxn := pow_nonneg (norm_nonneg x) n
  nlinarith [mul_le_mul_of_nonneg_left hp hC,mul_nonneg hC hLn,mul_nonneg hC hxn]

lemma PolySmooth.comp_linear {d e : ℕ} {f : Point e → ℝ}
    (hf : PolySmooth f) (L : Point d →L[ℝ] Point e) : PolySmooth (fun x => f (L x)) := by
  refine ⟨hf.smooth.comp L.contDiff,fun l => ?_⟩
  have he := JetCalculus.jet_comp_affine hf.smooth L 0 id l
  simp only [add_zero,id_eq] at he
  rw [he]
  have hh := hf.growth (l.map L)
  rw [JetCalculus.jet_map] at hh
  exact Appell.HasGrowth.comp_linear hh L

lemma productPotential_polySmooth {d e : ℕ} {H : Point d → ℝ} {G : Point e → ℝ}
    (hH : PolySmooth H) (hG : PolySmooth G) : PolySmooth (productPotential H G) :=
  (hH.comp_linear ((ContinuousLinearMap.fst ℝ (Point d) (Point e)).comp
    (productPointEquiv d e).toContinuousLinearMap)).add
    (hG.comp_linear ((ContinuousLinearMap.snd ℝ (Point d) (Point e)).comp
      (productPointEquiv d e).toContinuousLinearMap))

lemma gaussianPotential_polySmooth (d : ℕ) : PolySmooth (fun y : Point d => ‖y‖^2/2) := by
  have h (i : Fin d) : PolySmooth (fun y : Point d => y i) := PolySmooth.linear (PiLp.proj 2 _ i)
  have hs := PolySmooth.sum Finset.univ (fun i _ => (h i).mul (h i))
  have hh := (PolySmooth.const (1/2)).mul hs
  have he : (fun y : Point d => ‖y‖^2/2)=(fun y : Point d => (1/2 : ℝ)*(∑i,y i*y i)) := by
    funext y
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [pow_two]
    ring
  rw [he]
  exact hh

lemma productPotential_lowerTail {d e : ℕ} {H : Point d → ℝ} {G : Point e → ℝ}
    (hH : HasGaussianLowerTail H) (hG : HasGaussianLowerTail G) :
    HasGaussianLowerTail (productPotential H G) := by
  obtain ⟨a,ha,A,hA⟩ := hH
  obtain ⟨b,hb,B,hB⟩ := hG
  refine ⟨min a b,lt_min ha hb,A+B,fun y => ?_⟩
  rw [productPointEquiv_norm_sq]
  have h₁ := mul_le_mul_of_nonneg_right (min_le_left a b) (sq_nonneg ‖(productPointEquiv d e y).1‖)
  have h₂ := mul_le_mul_of_nonneg_right (min_le_right a b) (sq_nonneg ‖(productPointEquiv d e y).2‖)
  have h₃ := hA (productPointEquiv d e y).1
  have h₄ := hB (productPointEquiv d e y).2
  dsimp [productPotential]
  nlinarith

lemma gaussianPotential_lowerTail (d : ℕ) : HasGaussianLowerTail (fun y : Point d => ‖y‖^2/2) := by
  exact ⟨1/2,by norm_num,0,fun _ => by linarith⟩
end LogConcaveSampling

end

end

end

end OAI
