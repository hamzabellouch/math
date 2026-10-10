import OAI.Geometry.Kahler.BaseLaterNegative

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open Set Filter Topology MeasureTheory
open scoped ContDiff
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

structure TestSystem where
  a : ℝ
  ε : ℝ
  η : ℝ
  d : ℝ
  D : ℝ
  Q : ℕ
  P : ℕ → Finset Sphere
  pr : RadialProfiles a
  a_pos : 0 < a
  eps_pos : 0 < ε
  eta_pos : 0 < η
  eta_lt : η < 1/2
  d_pos : 0 < d
  D_ge : 1 ≤ D
  Q_ge : 2 ≤ Q
  separated : ∀ j, ProjectivelySeparated (D/Real.sqrt (Q^(j+1):ℕ)) (P (Q^(j+1)))
  positive : ∀ N (ξ : Sphere), 0 ≤ density Q pr.R pr.f pr.b P N ξ
  probability : ∀ N, IsProbabilityMeasure (densityMeasure (density Q pr.R pr.f pr.b P N))
  representing : ∀ N, Represents (densityMeasure (density Q pr.R pr.f pr.b P N))
  negative : ∀ N j, j+1 ≤ N → ∀ r ∈ Icc (0:ℝ) 1, 1-η ≤ r^(Q^(j+1)) →
    (∫ ξ : Sphere, logarithmicTest a ε (P (Q^(j+1))) (Q^(j+1)) ((r:ℂ) • (ξ:Base))
      ∂densityMeasure (density Q pr.R pr.f pr.b P N)) ≤ -d

lemma exists_testSystem : Nonempty TestSystem := by
  classical
  let a : ℝ := 3/2
  have ha : 1 < a := by norm_num [a]
  have ha2 : a < 2 := by norm_num [a]
  have ha0 : 0 < a := by linarith
  obtain ⟨pr,hoff⟩ := profiles_off_patch ha ha2
  obtain ⟨ε,η,Dstar,he,he1,heta,heta1,hDs,hnegative⟩ := negative_scale_parameters ha pr hoff
  let D := max Dstar (2*Real.sqrt (2*pr.R)+1)
  have hDstar : Dstar ≤ D := le_max_left _ _
  have hD : 1 ≤ D := hDs.trans hDstar
  have hDR : 2*Real.sqrt (2*pr.R) < D := by
    have := le_max_right Dstar (2*Real.sqrt (2*pr.R)+1)
    dsimp [D]; linarith
  obtain ⟨kmin,d,hd,hneg⟩ := hnegative D hDstar
  obtain ⟨M,θ,hθ,hθ1,herr,hθb⟩ := logarithmicTest_later_threshold ha0.le he.ne' (by positivity : 0 < d/2)
  obtain ⟨c,K,hc,hK,hden⟩ := uniform_representing_densities pr
  obtain ⟨Q₀,hQ₀⟩ := hden D hDR kmin
  obtain ⟨nD,hnD⟩ := exists_nat_ge (D^2)
  let Q := max Q₀ (max nD (M+3))
  obtain ⟨hQ,hQk,hQT⟩ := hQ₀ Q (le_max_left _ _)
  have hQM : M+2 < Q := by
    have := (le_max_right nD (M+3)).trans (le_max_right Q₀ (max nD (M+3)))
    dsimp [Q]; omega
  have hQD : D^2 ≤ Q := hnD.trans (by exact_mod_cast (le_max_left nD (M+3)).trans (le_max_right Q₀ (max nD (M+3))))
  have hex (k : ℕ) : ∃ P : Finset Sphere,
      D^2 ≤ k → ProjectivelySeparated (D/Real.sqrt k) P ∧ ProjectiveCover (D/Real.sqrt k) P := by
    by_cases hk : D^2 ≤ k
    · have hk0 : 0 < (k:ℝ) := by nlinarith
      have hs : 0 < Real.sqrt (k:ℝ) := Real.sqrt_pos.2 hk0
      have hρ1 : D/Real.sqrt k ≤ 1 := (div_le_one hs).2 ((Real.le_sqrt (by linarith) hk0.le).2 hk)
      obtain ⟨P,hP⟩ := exists_separated_cover (div_pos (by linarith) hs) hρ1
      exact ⟨P,fun _ => hP⟩
    · exact ⟨∅,fun hh => False.elim (hk hh)⟩
  choose P hP using hex
  have hdegree (j : ℕ) : Q ≤ Q^(j+1) := by
    calc Q = Q^1 := (pow_one Q).symm
         _ ≤ Q^(j+1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hsets (j : ℕ) := hP (Q^(j+1)) (hQD.trans (by exact_mod_cast hdegree j))
  have hsep := fun j => (hsets j).1
  have ht := hQT P hsep
  have hpositive : ∀ N (ξ : Sphere), 0 ≤ density Q pr.R pr.f pr.b P N ξ :=
    fun N ξ => ((ht N).2.1.positive ξ).le
  have hprob := fun N => (ht N).2.2.2.2.1
  have hrep := fun N => (ht N).2.2.2.2.2
  refine ⟨⟨a,ε,η,d/2,D,Q,P,pr,ha0,he,heta,heta1,by positivity,hD,hQ,hsep,hpositive,hprob,hrep,?_⟩⟩
  intro N j hjN r hr hnear
  let := hprob N
  let := hprob (j+1)
  have hlow : (∫ ξ : Sphere, logarithmicTest a ε (P (Q^(j+1))) (Q^(j+1)) ((r:ℂ) • (ξ:Base))
      ∂densityMeasure (density Q pr.R pr.f pr.b P (j+1))) ≤ -d := by
    rw [densityMeasure_integral (ht (j+1)).1.continuous (hpositive (j+1))]
    simp only [smul_eq_mul]
    simp_rw [mul_comm (density Q pr.R pr.f pr.b P (j+1) _)]
    rw [logarithmicTests_exact_averaging pr he.ne' hQ P j r]
    have hh := hneg (Q^(j+1)) (hQk.trans (hdegree j)) (P (Q^(j+1))) (hsets j).1 (hsets j).2
      (r^(Q^(j+1))) ⟨hnear,pow_le_one₀ hr.1 hr.2⟩
    simpa only [logarithmicTest,peakPolynomial_homogeneous,Complex.ofReal_pow] using hh
  have hcomp := logarithmicTest_later_comparison ha0.le pr hQ hQM (by omega : 1 ≤ j+1) hjN P hD
    (hsep j) he.ne' hθ.le hθ1 hr.1 hr.2 hθb (hpositive (j+1)) (hpositive N)
  have hb := (le_abs_self _).trans (hcomp.trans herr)
  linarith

end PinchedHartogs.BaseConstruction

end

end OAI
