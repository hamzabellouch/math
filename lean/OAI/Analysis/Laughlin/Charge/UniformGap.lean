import OAI.Analysis.Laughlin.Charge.FiniteGap
import OAI.Analysis.Laughlin.Charge.Comparison

namespace OAI

namespace Laughlin.Charge
open Fock
open scoped BigOperators InnerProductSpace

theorem neutralGap_ge_of_fock_eigenvalues (Q n : ℕ) (γ : ℝ) (hγ : 0≤γ)
    (hex : {x | x ∈ unitSector Q n ∧ x ∈ (groundKernel Q n)ᗮ}.Nonempty)
    (heigen : ∀ v : Space Q, v≠0 → ∀ a : ℝ,
      sourceFockHamiltonian Q v=(a : ℂ) • v → a=0 ∨ γ≤a) : γ≤neutralGap Q n := by
  have hsector : ∀ v : particleSector Q n, v≠0 → ∀ a : ℝ,
      sectorHamiltonian Q n v=(a : ℂ) • v → a=0 ∨ γ≤a := by
    intro v hv a ha
    apply heigen ((occupationEuclidean Q).symm v)
    · intro hz
      apply hv
      apply Subtype.ext
      apply_fun occupationEuclidean Q at hz
      simpa using hz
    · have hh := congrArg Subtype.val ha
      change euclideanFockHamiltonian Q (v : Hilbert Q)=(a : ℂ) • (v : Hilbert Q) at hh
      have hh' := congrArg (occupationEuclidean Q).symm hh
      simpa only [euclideanFockHamiltonian,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,
        LinearEquiv.symm_apply_apply,map_smul] using hh' 
  apply le_csInf (hex.image _)
  rintro t ⟨x,hx,rfl⟩
  obtain ⟨y,hy,hbound⟩ := spectral_kernel_distance (E := ↥(particleSector Q n)) (sectorHamiltonian Q n)
    (sectorHamiltonian_symmetric Q n) γ hγ hsector ⟨x,hx.1.1⟩
  have hyK : (y : Hilbert Q) ∈ groundKernel Q n :=
    ⟨y.property,congrArg Subtype.val hy⟩
  have horth : inner ℂ x (y : Hilbert Q)=0 :=
    (Submodule.mem_orthogonal' _ _).mp hx.2 _ hyK
  have hnorm : (1 : ℝ) ≤ ‖x-(y : Hilbert Q)‖^2 := by
    rw [norm_sub_sq (𝕜 := ℂ),horth]
    change 1≤‖x‖^2-2*(0 : ℝ)+‖(y : Hilbert Q)‖^2
    rw [hx.1.2]
    nlinarith [sq_nonneg ‖(y : Hilbert Q)‖]
  have hbound' : γ*‖x-(y : Hilbert Q)‖^2≤energy Q x := by
    change γ*‖x-(y : Hilbert Q)‖^2≤
      (inner ℂ (euclideanFockHamiltonian Q x) x).re at hbound
    rwa [← energy_eq_inner] at hbound
  exact (le_mul_of_one_le_right hγ hnorm).trans hbound'

theorem neutralGap_uniform_of_ground (hground : LaughlinChargeGroundInput) :
    ∃ n₀ : ℕ, 2≤n₀ ∧ ∀ n : ℕ, n₀≤n → (1/25 : ℝ)≤neutralGap (3*(n-1)) n := by
  obtain ⟨Q₀,h25,hgap⟩ := physical_fock_eigenvalue_gap_uniform_sharp (1/25)
    one_twenty_fifth_lt_gammaStar
  refine ⟨Q₀+2,by omega,fun n hn => ?_⟩
  have hn2 : 2≤n := by omega
  apply neutralGap_ge_of_fock_eigenvalues _ _ _ (by norm_num)
  · exact excited_unit_nonempty _ _ (by omega) (by omega) (hground n hn2).2.2
  · exact hgap _ (by omega)

theorem charge_neutral_full_of_published (hrec : LNWYRecursionInput)
    (hrank : LNWYRankOneInput) (hground : LaughlinChargeGroundInput) :
    (∀ n : ℕ, 2≤n →
      chargeGap (3*(n-1)) n=groundEnergy (3*(n-1)) (n+1) ∧
      0<neutralGap (3*(n-1)) n ∧
      (n : ℝ)*neutralGap (3*(n-1)) n/((n : ℝ)-1)≤chargeGap (3*(n-1)) n ∧
      0<chargeGap (3*(n-1)) n) ∧
    (∃ n₀ : ℕ, 2≤n₀ ∧ ∀ n : ℕ, n₀≤n →
      (n : ℝ)/(25*((n : ℝ)-1))≤chargeGap (3*(n-1)) n) := by
  constructor
  · intro n hn
    have h := charge_neutral_of_published hrec hrank hground n hn
    have hp := neutralGap_pos _ _ (by omega) (by omega) (hground n hn).2.2
    have hnR : (2 : ℝ)≤n := by exact_mod_cast hn
    have hd : (0 : ℝ)<(n : ℝ)-1 := by linarith
    exact ⟨h.1,hp,h.2,(div_pos (mul_pos (by linarith) hp) hd).trans_le h.2⟩
  · obtain ⟨n₀,hn₀,hgap⟩ := neutralGap_uniform_of_ground hground
    exact ⟨n₀,hn₀,fun n hn => charge_uniform_of_published hrec hrank hground n
      (by omega) (hgap n hn)⟩

end Laughlin.Charge

end OAI
