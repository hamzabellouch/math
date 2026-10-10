import OAI.Geometry.RCD.Sobolev.SobolevQuadraticEnergy
import OAI.Geometry.RCD.Harmonic.GramDirectionalError

namespace OAI

/-! # Recovering all Gram entries from directional L1 errors -/

open Set MeasureTheory
open scoped InnerProductSpace
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem directional_error_implies_gram (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    {n : ℕ} (u : Fin n → SobolevSpace μ hQ) (S : Set X) (hf : μ S ≠ ⊤)
    {D : ℝ} (hD : 0 ≤ D)
    (herr : ∀ z : Euclidean n, (μ.real S)⁻¹*(∫ x in S,
      |localGamma μ hQ (sobolevColumnMap μ hQ u z) (sobolevColumnMap μ hQ u z) x-‖z‖^2| ∂μ)
      ≤ D*‖z‖^2) :
    ∀ i j : Fin n, (μ.real S)⁻¹*(∫ x in S,
      |localGamma μ hQ (u i) (u j) x-(if i=j then 1 else 0)| ∂μ) ≤ 2*D := by
  classical
  have hd (i : Fin n) : (μ.real S)⁻¹*(∫ x in S,
      |localGamma μ hQ (u i) (u i) x-1| ∂μ) ≤ D := by
    simpa only [sobolevColumnMap_single,PiLp.norm_single,norm_one,one_pow,mul_one]
      using herr (EuclideanSpace.single i 1)
  intro i j
  by_cases hij : i=j
  · subst j
    simpa using (hd i).trans (by linarith : D ≤ 2*D)
  let ei : Euclidean n := EuclideanSpace.single i 1
  let ej : Euclidean n := EuclideanSpace.single j 1
  have hn : ‖ei+ej‖^2=2 := by
    rw [norm_add_sq_real]
    norm_num [ei,ej,EuclideanSpace.inner_single_left,hij]
  have hsum : (μ.real S)⁻¹*(∫ x in S,
      |localGamma μ hQ (u i+u j) (u i+u j) x-2| ∂μ) ≤ 2*D := by
    have he := herr (ei+ej)
    rw [hn,map_add,sobolevColumnMap_single,sobolevColumnMap_single] at he
    simpa only [mul_comm] using he
  have hi (g : SobolevSpace μ hQ) (a : ℝ) :
      IntegrableOn (fun x => |localGamma μ hQ g g x-a|) S μ :=
    ((localGamma_memL1 μ hQ g g).integrableOn.sub (integrableOn_const hf)).abs
  have he := localGamma_add_smul_square μ hQ (u i) (u j) 1
  simp only [one_smul,one_pow,mul_one,one_mul] at he
  have hpt : ∀ᵐ x ∂μ.restrict S,
      2*|localGamma μ hQ (u i) (u j) x| ≤
        |localGamma μ hQ (u i+u j) (u i+u j) x-2|+
        (|localGamma μ hQ (u i) (u i) x-1|+|localGamma μ hQ (u j) (u j) x-1|) := by
    filter_upwards [ae_restrict_of_ae he] with x hx
    have habs : 2*|localGamma μ hQ (u i) (u j) x| =
        |(localGamma μ hQ (u i+u j) (u i+u j) x-2)-
          (localGamma μ hQ (u i) (u i) x-1)-
          (localGamma μ hQ (u j) (u j) x-1)| := by
      rw [hx]
      have hr : localGamma μ hQ (u i) (u i) x+2*localGamma μ hQ (u i) (u j) x+
          localGamma μ hQ (u j) (u j) x-2-(localGamma μ hQ (u i) (u i) x-1)-
          (localGamma μ hQ (u j) (u j) x-1)=2*localGamma μ hQ (u i) (u j) x := by ring
      rw [hr,abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [habs]
    exact (abs_sub _ _).trans (by
      have hh := abs_sub (localGamma μ hQ (u i+u j) (u i+u j) x-2)
        (localGamma μ hQ (u i) (u i) x-1)
      linarith)
  have hint := integral_mono_ae
    ((localGamma_memL1 μ hQ (u i) (u j)).abs.integrableOn.const_mul 2)
    ((hi (u i+u j) 2).add ((hi (u i) 1).add (hi (u j) 1))) hpt
  have hadd := integral_add (hi (u i+u j) 2) ((hi (u i) 1).add (hi (u j) 1))
  have hadd' := integral_add (hi (u i) 1) (hi (u j) 1)
  simp only [Pi.add_apply] at hint hadd hadd'
  rw [integral_const_mul,hadd,hadd'] at hint
  have hh := mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr (measureReal_nonneg : 0 ≤ μ.real S))
  simp only [ite_eq_right hij,sub_zero]
  nlinarith [hd i,hd j]

end RegularPointCoordinates

end

end OAI
