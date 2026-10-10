import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.TracialCohomology.MatrixExtensions

namespace OAI

/-! Small expectations for bounded Hochschild cohomology. -/

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace PopaMatrices
open BoundedHochschild HochschildRigidity HochschildDiffuse
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
  (h1 : τ 1=1)
  (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1:M))

def trivialSystem : System 1 (1:M) where
  entry _ _ := 1
  star_entry _ _ := star_one _
  mul_entry i j k l := by simp [Subsingleton.elim j k]
  sum_diag := by simp

def energy {r n : ℕ} (F : Fin r → M) (s : System n (1:M)) : ℝ :=
  ∑ i, ‖τ.toPreGNS (s.expect (F i))‖^2

lemma energy_nonneg {r n : ℕ} (F : Fin r → M) (s : System n (1:M)) :
    0 ≤ energy τ F s := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

include e hτ htr hfaith h1 hfactor in
lemma energy_contract (hdiff : NoMinimalProjections M)
    {r : ℕ} (hr : 0 < r) (F : Fin r → M) (hF : ∀ i, τ (F i)=0)
    {n : ℕ} (s : System n (1:M)) (hn : 0 < n) :
    ∃ m : ℕ, 0 < m ∧ ∃ t : System m (1:M),
      energy τ F t ≤ (1-1/(1024*(r:ℝ)))*energy τ F s := by
  classical
  have hrR : 0 < (r:ℝ) := Nat.cast_pos.mpr hr
  by_cases hz : energy τ F s=0
  · exact ⟨n,hn,s,by rw [hz]; simp⟩
  have hE : 0 < energy τ F s := lt_of_le_of_ne (energy_nonneg τ F s) (Ne.symm hz)
  have hsum : (∑ _i : Fin r, energy τ F s/(r:ℝ)) = energy τ F s := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
  obtain ⟨i,_hi,hmax⟩ := Finset.exists_le_of_sum_le
    (s := Finset.univ) (f := fun _i : Fin r => energy τ F s/(r:ℝ))
    (g := fun i : Fin r => ‖τ.toPreGNS (s.expect (F i))‖^2)
    ⟨⟨0,hr⟩,Finset.mem_univ _⟩ (by rw [hsum]; rfl)
  have hi : 0 < ‖τ.toPreGNS (s.expect (F i))‖ := by
    have hh := (div_pos hE hrR).trans_le hmax
    nlinarith [norm_nonneg (τ.toPreGNS (s.expect (F i)))]
  obtain ⟨m,hm,t,hle,hlt⟩ := extend_energy_decrease e τ hτ htr hfaith h1 hfactor
    hdiff s hn (F i) (hF i) hi
  have hdiffs (j : Fin r) : 0 ≤ ‖τ.toPreGNS (s.expect (F j))‖^2-
      ‖τ.toPreGNS (t.expect (F j))‖^2 := by
    have hj := hle (F j)
    nlinarith [norm_nonneg (τ.toPreGNS (t.expect (F j)))]
  have hdrop := Finset.single_le_sum (s := Finset.univ) (f := fun j : Fin r =>
    ‖τ.toPreGNS (s.expect (F j))‖^2-‖τ.toPreGNS (t.expect (F j))‖^2)
    (fun j _ => hdiffs j) (Finset.mem_univ i)
  rw [Finset.sum_sub_distrib] at hdrop
  change _ ≤ energy τ F s-energy τ F t at hdrop
  have hmax' : energy τ F s ≤ (r:ℝ)*‖τ.toPreGNS (s.expect (F i))‖^2 := by
    exact (div_le_iff₀ hrR).mp hmax |>.trans_eq (mul_comm _ _)
  refine ⟨m,hm,t,?_⟩
  apply (le_of_mul_le_mul_left ?_ (show 0 < 1024*(r:ℝ) by positivity))
  have hh : (1024*(r:ℝ))*((1-1/(1024*(r:ℝ)))*energy τ F s)=
      (1024*(r:ℝ)-1)*energy τ F s := by field_simp
  rw [hh]
  have hlow : ‖τ.toPreGNS (s.expect (F i))‖^2/1024 < energy τ F s-energy τ F t := by linarith
  have hmul := mul_lt_mul_of_pos_left hlow hrR
  nlinarith

include e hτ htr hfaith h1 hfactor in

theorem exists_small_expectation (hdiff : NoMinimalProjections M)
    {r : ℕ} (F : Fin r → M) (hF : ∀ i, τ (F i)=0) (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ ∃ s : System n (1:M), energy τ F s < ε := by
  by_cases hr : r=0
  · subst r
    exact ⟨1,by omega,trivialSystem,by simpa [energy] using hε⟩
  have hrp : 0 < r := Nat.pos_of_ne_zero hr
  let q : ℝ := 1-1/(1024*(r:ℝ))
  have hrR : 1 ≤ (r:ℝ) := by exact_mod_cast hrp
  have hq0 : 0 ≤ q := by
    have hh : 1/(1024*(r:ℝ)) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; exact sub_lt_self _ (by positivity)
  have hi : ∀ k : ℕ, ∃ n : ℕ, 0 < n ∧ ∃ s : System n (1:M),
      energy τ F s ≤ q^k*energy τ F (trivialSystem (M:=M)) := by
    intro k
    induction k with
    | zero => exact ⟨1,by omega,trivialSystem,by simp⟩
    | succ k ih =>
      obtain ⟨n,hn,s,hs⟩ := ih
      obtain ⟨m,hm,t,ht⟩ := energy_contract e τ hτ htr hfaith h1 hfactor hdiff hrp F hF s hn
      refine ⟨m,hm,t,ht.trans ?_⟩
      have hh := mul_le_mul_of_nonneg_left hs hq0
      change q*energy τ F s ≤ _
      simpa only [pow_succ,mul_assoc,mul_comm q,mul_left_comm q] using hh
  have ht : Tendsto (fun k : ℕ => q^k*energy τ F (trivialSystem (M:=M))) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const
      (energy τ F (trivialSystem (M:=M)))
  obtain ⟨k,hk⟩ := ((tendsto_order.mp ht).2 ε hε).exists
  obtain ⟨n,hn,s,hs⟩ := hi k
  exact ⟨n,hn,s,hs.trans_lt hk⟩
end PopaMatrices

open scoped ComplexOrder
namespace PopaMatrices.System
open HochschildRigidity PopaQuantization
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {n : ℕ} (s : PopaMatrices.System n (1:M))
variable (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))

include htr in
lemma flatProjection_energy (i0 : Fin n) (a : Fin n → Bool) (x : M) :
    (n:ℝ)*‖τ.toPreGNS (s.flatProjection i0 a*x*s.flatProjection i0 a)‖^2=
      (n:ℝ)⁻¹*‖∑ i, ∑ j, (sign (a i)*sign (a j)) • τ.toPreGNS (s.entry i0 i*x*s.entry j i0)‖^2 := by
  rw [s.flatProjection_compression_norm τ htr,s.flatColumn_compression,
    ← Complex.coe_smul,map_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)),mul_pow]
  have hn : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Fin.pos i0))
  have he : (n:ℝ)*((n:ℝ)⁻¹)^2=(n:ℝ)⁻¹ := by field_simp
  rw [← mul_assoc,he]
  congr 2

include htr in
lemma flatProjection_mean (i0 : Fin n) (x : M) :
    (∑ a : Fin n → Bool, (n:ℝ)*‖τ.toPreGNS (s.flatProjection i0 a*x*s.flatProjection i0 a)‖^2) ≤
      (2:ℝ)^n*(‖τ.toPreGNS (s.expect x)‖^2+(2/(n:ℝ))*‖τ.toPreGNS x‖^2) := by
  let : InnerProductSpace ℝ τ.PreGNS := InnerProductSpace.rclikeToReal ℂ _
  simp_rw [s.flatProjection_energy τ htr]
  rw [← Finset.mul_sum]
  have hh := quadratic_mean_square_bound (fun i j => τ.toPreGNS (s.entry i0 i*x*s.entry j i0))
  have hh' := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (Nat.cast_nonneg n))
  apply hh'.trans_eq
  rw [← map_sum,s.diagonal_sum_norm τ htr,s.blocks_norm_sum τ htr]
  have hn : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Fin.pos i0))
  field_simp

include htr in

lemma exists_flat_projection {r : ℕ} (i0 : Fin n) (F : Fin r → M) :
    ∃ a : Fin n → Bool,
      (∑ j, (n:ℝ)*‖τ.toPreGNS (s.flatProjection i0 a*F j*s.flatProjection i0 a)‖^2) ≤
        PopaMatrices.energy τ F s+(2/(n:ℝ))*(∑ j, ‖τ.toPreGNS (F j)‖^2) := by
  classical
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ => s.flatProjection_mean τ htr i0 (F j))
  rw [Finset.sum_comm] at hh
  simp only [mul_add,Finset.sum_add_distrib,← Finset.mul_sum] at hh
  have he : ((2:ℝ)^n*PopaMatrices.energy τ F s+(2:ℝ)^n*((2/(n:ℝ))*(∑ j, ‖τ.toPreGNS (F j)‖^2)))=
      ∑ _a : Fin n → Bool, (PopaMatrices.energy τ F s+(2/(n:ℝ))*(∑ j, ‖τ.toPreGNS (F j)‖^2)) := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_bool,
      Fintype.card_fin,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
    ring
  change _ ≤ (2:ℝ)^n*PopaMatrices.energy τ F s+(2:ℝ)^n*((2/(n:ℝ))*(∑ j, ‖τ.toPreGNS (F j)‖^2)) at hh
  rw [he,Finset.mul_sum] at hh
  obtain ⟨a,_,ha⟩ := Finset.exists_le_of_sum_le (s := Finset.univ)
    ⟨(fun _ => false),Finset.mem_univ _⟩ hh
  exact ⟨a,by simpa only [Finset.mul_sum] using ha⟩
end PopaMatrices.System

end

end OAI
