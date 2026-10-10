import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFiniteCongruenceCover
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaEisensteinCusp

namespace OAI

/-! A Siegel-set reduction for the full Eisenstein modular group, and
its finite translate cover of the actual principal level-three quotient. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicTheta_nearest_normSq_bound (z : ℂ) :
    Complex.normSq (z-(nearestEisenstein z:ℂ)) ≤ 3/4 := by
  let a := z.re+z.im/Real.sqrt 3
  let b := 2*z.im/Real.sqrt 3
  have he : z-(nearestEisenstein z:ℂ)=
      ((a-round a:ℝ):ℂ)+((b-round b:ℝ):ℂ)*omega := by
    conv_lhs => lhs; rw [complex_coordinates z]
    simp only [nearestEisenstein,ofCoords_coe]
    dsimp [a,b]
    push_cast
    ring
  have ha : (a-round a)^2 ≤ (1/2:ℝ)^2 := sq_le_sq.mpr (by simpa using abs_sub_round a)
  have hb : (b-round b)^2 ≤ (1/2:ℝ)^2 := sq_le_sq.mpr (by simpa using abs_sub_round b)
  rw [he,real_coordinates_norm]
  nlinarith [sq_nonneg (a-round a+b-round b)]

def cubicThetaFullTranslation (m : Eisenstein) : SL(2,Eisenstein) :=
  ⟨!![1,m;0,1],by simp [Matrix.det_fin_two]⟩

def cubicThetaFullInversion : SL(2,Eisenstein) :=
  ⟨!![0,-1;1,0],by simp [Matrix.det_fin_two]⟩

lemma cubicThetaFullTranslation_complex (m : Eisenstein) :
    cubicThetaFullComplex (cubicThetaFullTranslation m)=cubicThetaTranslationMatrix (m:ℂ) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

lemma cubicThetaFullInversion_complex :
    cubicThetaFullComplex cubicThetaFullInversion=cubicThetaInversionMatrix 1 one_ne_zero := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  all_goals first | rfl | (change (-1:ℂ)= -(1:ℂ)⁻¹; norm_num)

lemma cubicThetaFullInversion_height (p : ℂ × ℝ) :
    (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p).2=
      p.2/(Complex.normSq p.1+p.2^2) := by
  rw [cubicThetaFullInversion_complex]
  simp [cubicThetaMobius,cubicThetaMobiusDenominator,cubicThetaInversionMatrix]

/-- A single full-group cusp chart with a uniform positive lower height. -/
def cubicThetaSiegelSet : Set (ℂ × ℝ) :=
  {p | 0<p.2 ∧ Complex.normSq p.1 ≤ 3/4 ∧ 1/2 ≤ p.2}

theorem cubicThetaSiegelSet_meets_orbit {p : ℂ × ℝ} (hp : 0<p.2) :
    ∃ u : SL(2,Eisenstein), cubicThetaMobius (cubicThetaFullComplex u) p∈cubicThetaSiegelSet := by
  obtain ⟨g,hg⟩ := cubicThetaFullGroup_exists_max_height hp
  let q := cubicThetaMobius (cubicThetaFullComplex g) p
  let m := -nearestEisenstein q.1
  let u := cubicThetaFullTranslation m*g
  have hu : cubicThetaMobius (cubicThetaFullComplex u) p=
      (q.1-(nearestEisenstein q.1:ℂ),q.2) := by
    dsimp only [u]
    rw [map_mul,← cubicThetaMobius_comp _ _ hp,cubicThetaFullTranslation_complex,
      cubicThetaMobius_translation]
    simp only [m,Subalgebra.coe_neg,sub_eq_add_neg]
    rfl
  have hq : 0<q.2 := cubicThetaMobius_height_pos _ hp
  have hmax (h : SL(2,Eisenstein)) :
      (cubicThetaMobius (cubicThetaFullComplex h) p).2 ≤
        (cubicThetaMobius (cubicThetaFullComplex u) p).2 := by
    rw [hu]
    exact hg h
  have hinv := hmax (cubicThetaFullInversion*u)
  rw [map_mul,← cubicThetaMobius_comp _ _ hp,cubicThetaFullInversion_height,hu] at hinv
  have hn := cubicTheta_nearest_normSq_bound q.1
  have hD : 0<Complex.normSq (q.1-(nearestEisenstein q.1:ℂ))+q.2^2 :=
    add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _) (sq_pos_of_pos hq)
  have hmul := (div_le_iff₀ hD).mp hinv
  have hD1 : 1 ≤ Complex.normSq (q.1-(nearestEisenstein q.1:ℂ))+q.2^2 := by nlinarith
  refine ⟨u,?_⟩
  rw [hu]
  exact ⟨hq,hn,by nlinarith⟩

theorem cubicThetaFiniteSiegelCover :
    ∃ S : Finset SL(2,Eisenstein), ∀ p : ℂ × ℝ, 0<p.2 →
      ∃ δ ∈ S, ∃ k : cubicThetaPrincipalGroup,
        cubicThetaMobius (cubicThetaFullComplex (δ*k.val)) p∈cubicThetaSiegelSet := by
  obtain ⟨S,hS⟩ := cubicThetaFiniteCongruenceCover
  refine ⟨S,?_⟩
  intro p hp
  obtain ⟨u,hu⟩ := cubicThetaSiegelSet_meets_orbit hp
  obtain ⟨δ,hδ,k,hk⟩ := hS u
  exact ⟨δ,hδ,k,hk ▸ hu⟩

end CubicFirstMoment

end

end OAI
