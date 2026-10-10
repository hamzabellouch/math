import Mathlib
import OAI.Probability.SKGap.Brownian.PathEquivalents
import OAI.Probability.SKGap.Localization.ProjectedReal

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set Filter
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def pathK (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 0 ≤ R) (j : ℝ) (a : ι → ℝ)
    (z : ℝ) (M : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  realTruncatedK f R hR (pathDiagonal a z)
    (pathShift z ((j/(Fintype.card ι:ℝ))*∑ b, a b)) M

lemma pathK_bounds [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A z : ℝ} (hR : 0 ≤ R) (hj : 0 ≤ j)
    (hA : 0 ≤ A) {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (haA : ∀ i, a i ≤ A)
    (hz : z ∈ Icc (0:ℝ) 1) :
    (∀ M, opNorm (pathK f R hR j a z M) ≤ pathBound f R j A) ∧
    (∀ M N, ‖pathK f R hR j a z M-pathK f R hR j a z N‖ ≤ pathLip f R j A*‖M-N‖) := by
  have hq := diagonal_mean_bounds hj ha haA
  have hc := path_constants_bound f hR hj hA haA hq.1 hq.2 hz
  constructor
  · intro M
    exact (realTruncatedK_opNorm f hR _ _ M (diagonal_transpose _) (diagonal_transpose _)).trans hc.1
  · intro M N
    exact (realTruncatedK_sub_norm f hR _ _ M N (diagonal_transpose _) (diagonal_transpose _)).trans
      (mul_le_mul_of_nonneg_right hc.2.1 (norm_nonneg _))

lemma pathK_continuous [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A z : ℝ} (hR : 0 ≤ R) (hj : 0 ≤ j)
    (hA : 0 ≤ A) {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (haA : ∀ i, a i ≤ A)
    (hz : z ∈ Icc (0:ℝ) 1) : Continuous (pathK f R hR j a z) := by
  apply LipschitzWith.continuous (K := ⟨pathLip f R j A,(path_constants_nonneg f hR hj hA).2⟩)
  apply LipschitzWith.of_dist_le_mul
  intro M N
  change ‖pathK f R hR j a z M-pathK f R hR j a z N‖ ≤ pathLip f R j A*‖M-N‖
  exact (pathK_bounds f hR hj hA ha haA hz).2 M N

lemma pathK_sign (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R) (j : ℝ) (a : ι → ℝ)
    (z : ℝ) (s : ι → ℝ) (hs : ∀ i, s i^2=1) (M : Matrix ι ι ℝ) :
    pathK f R hR j a z (signConjugate s M)=signConjugate s (pathK f R hR j a z M) :=
  realTruncatedK_sign f hR s hs _ _ M

theorem actual_projected_path_equivalents {j A : ℝ}
    (hj : 0 < j) (hA : 0 < A) (hs : sqrt j*A < 1) :
    ∃ (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 0 ≤ R) (lo hi C : ℝ) (N : ℕ),
      R = 2*sqrt j+1+1 ∧ lo = (1-sqrt j*A)^2/4 ∧ hi = 2+A*(2*sqrt j+1+j*A) ∧
      0 < lo ∧ (∀ x ∈ Icc lo hi, f x=(x:ℂ)⁻¹) ∧ (∀ x, star (f x)=f x) ∧
      0 < C ∧ 0 < N ∧
      (∀ (n : ℕ), N ≤ n → ∀ (a : Fin n → ℝ), (∀ i, 0 ≤ a i) →
        (∀ i, a i ≤ A) → ∀ z ∈ Icc (0:ℝ) 1, ∀ i,
          |pathExpected f R hR j a z i-1| ≤ C/(n:ℝ) ∧
          |(∫ g, (realProject R hR (goeMatrix (j/(n:ℝ)) g)*
            pathK f R hR j a z (goeMatrix (j/(n:ℝ)) g)) i i
            ∂Measure.pi (fun _ : MatrixCoordinates (Fin n) => gaussianReal 0 1))-
              z*((j/(n:ℝ))*∑ b, a b)| ≤ C/(n:ℝ)) := by
  obtain ⟨f,R,hR,lo,hi,C₀,N,hReq,hloeq,hhieq,hlo,hf,hfr,hC₀,hN,hEquiv⟩ :=
    actual_path_equivalents hj hA hs
  let B := pathBound f R j A
  let rate := pathRate j A
  let CP := projectedErrorConstant j R B rate
  have hB : 0 ≤ B := (path_constants_nonneg f hR hj.le hA.le).1
  have hrate : 0 < rate := pathRate_pos hj hA hs
  have hCP : 0 ≤ CP := by dsimp [CP,projectedErrorConstant]; positivity
  obtain ⟨N₁,hN₁⟩ := eventually_atTop.mp (path_size_eventually hs)
  refine ⟨f,R,hR,lo,hi,C₀+CP,max N N₁,hReq,hloeq,hhieq,hlo,hf,hfr,
    by positivity,lt_of_lt_of_le hN (le_max_left _ _),?_⟩
  intro n hn a ha haA z hz i
  have hnN : N ≤ n := (le_max_left N N₁).trans hn
  have hn0 : 0 < n := hN.trans_le hnN
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn0
  have hnr : (0:ℝ) < n := Nat.cast_pos.mpr hn0
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn0
  have hEquiv' := hEquiv n hnN a ha haA z hz i
  have hp := path_goodSet_exponential hj hA ha haA hs
    (by simpa only [Fintype.card_fin] using hN₁ n ((le_max_right N N₁).trans hn)) hz
  rw [← hReq,← hloeq,← hhieq] at hp
  let s := truncationGoodSet (j/(n:ℝ)) R lo hi (pathDiagonal a z)
    (pathShift z ((j/(n:ℝ))*∑ b, a b))
  have hep := projected_product_expectation_error hR (div_nonneg hj.le hnr.le) hB
    (pathK f R hR j a z) (pathK_continuous f hR hj.le hA.le ha haA hz)
    (pathK_bounds f hR hj.le hA.le ha haA hz).1
    (truncationGoodSet_measurable _ _ _ _ _ _) (s := s)
    (fun g hg => le_of_lt hg.1) i
  simp only [Fintype.card_fin] at hp hep
  have he := hep.trans (projected_error_absorption hj.le hR hB hrate hn1 hp)
  constructor
  · exact hEquiv'.1.trans (div_le_div_of_nonneg_right (by linarith) hnr.le)
  · have hw : |(∫ g, (goeMatrix (j/(n:ℝ)) g*pathK f R hR j a z (goeMatrix (j/(n:ℝ)) g)) i i
        ∂Measure.pi (fun _ : MatrixCoordinates (Fin n) => gaussianReal 0 1))-
          z*((j/(n:ℝ))*∑ b, a b)| ≤ C₀/(n:ℝ) := by
      simpa only [pathExpectedWK,pathK,Fintype.card_fin] using hEquiv'.2
    have hh := (abs_sub_le _ _ _).trans (add_le_add he hw)
    exact hh.trans_eq (show projectedErrorConstant j R B rate/(n:ℝ)+C₀/(n:ℝ)=(C₀+CP)/(n:ℝ) by dsimp only [CP]; ring)
end SKGap
end
end

end OAI
