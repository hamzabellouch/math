import OAI.NumberTheory.Ostmann.QuadraticCenter.KernelFunctions
import OAI.NumberTheory.Ostmann.QuadraticCenter.RootCollisionAlgebra

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem rootCollision_units_of_not_dvd {p m : ℕ} {u v : ℤ}
    (hp : ¬ p ∣ 4*m*(u*v).natAbs) :
    (m:ZMod p) ≠ 0 ∧ (u:ZMod p) ≠ 0 ∧ (v:ZMod p) ≠ 0 := by
  have hmd : m ∣ 4*m*(u*v).natAbs := ⟨4*(u*v).natAbs,by ring⟩
  have hud : u.natAbs ∣ 4*m*(u*v).natAbs := by
    refine ⟨4*m*v.natAbs,?_⟩
    rw [Int.natAbs_mul]
    ring
  have hvd : v.natAbs ∣ 4*m*(u*v).natAbs := by
    refine ⟨4*m*u.natAbs,?_⟩
    rw [Int.natAbs_mul]
    ring
  refine ⟨?_,?_,?_⟩
  · intro hm
    exact hp (((ZMod.natCast_eq_zero_iff m p).mp hm).trans hmd)
  · intro hu
    exact hp ((Int.natCast_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hu)).trans hud)
  · intro hv
    exact hp ((Int.natCast_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hv)).trans hvd)

theorem canonicalKernelRoots_split_collision (S T : Finset ℤ) (m : ℕ) (h u v : ℤ)
    {p : ℕ} [Fact p.Prime]
    (hU : (canonicalKernelRoots S m h u).Nonempty)
    (hV : (canonicalKernelRoots T m h v).Nonempty)
    (hprime : ∀ x ∈ S,∀ y ∈ T,Nat.Prime (x-y).natAbs)
    (hsmall : ∀ x ∈ S,∀ y ∈ T,p < (x-y).natAbs)
    (hp : ¬p ∣ 4*m*(u*v).natAbs) (hsplit : jacobiSym (u*v) p=1) :
    4/(p:ℝ) ≤ rootCollisionProbability (canonicalKernelRoots S m h u) p+
      rootCollisionProbability (canonicalKernelRoots T m h v) p := by
  obtain ⟨hm,hu,hv⟩ := rootCollision_units_of_not_dvd hp
  obtain ⟨c,hc,hcu⟩ := exists_root_residue_scaling_of_jacobi hu hv hsplit
  apply rootCollisionProbability_add_ge_four _ _ hU hV c hc
  intro r hr s hs
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hs
  exact root_residues_ne_of_prime_separation (by simpa only [Int.cast_natCast] using hm)
    (canonicalKernelFiber_factorization hx) (canonicalKernelFiber_factorization hy)
    (hprime x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1)
    (hsmall x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1) c hcu

theorem kernel_root_diameter_scale {X η : ℝ} (hX : 1 ≤ X) (hη : 0 ≤ η)
    {m : ℕ} {u : ℤ} (hu : u ≠ 0) (hm : (m:ℝ) ≤ X^η) :
    Real.sqrt ((m:ℝ)*X/|(u:ℝ)|) ≤ X^(1/2+η:ℝ) := by
  have hXp : 0 < X := by linarith
  have huabs : (1:ℝ) ≤ |(u:ℝ)| := by
    have hn : 1 ≤ u.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hu)
    have hh : (1:ℝ) ≤ (u.natAbs:ℝ) := by exact_mod_cast hn
    have he : ((u.natAbs:ℤ):ℝ) = |(u:ℝ)| := by
      rw [Int.natCast_natAbs,Int.cast_abs]
    simp only [Int.cast_natCast] at he
    rwa [he] at hh
  have hdiv : (m:ℝ)*X/|(u:ℝ)| ≤ (m:ℝ)*X := by
    apply div_le_self (by positivity) huabs
  have hmul := mul_le_mul_of_nonneg_right hm hXp.le
  have hp : X^η*X=X^(1+η) := by
    calc
      _ = X^η*X^(1:ℝ) := by rw [Real.rpow_one]
      _ = X^(η+1) := (Real.rpow_add hXp _ _).symm
      _ = _ := by congr 1; ring
  rw [hp] at hmul
  have hpow : X^(1+η) ≤ X^(1+2*η) :=
    Real.rpow_le_rpow_of_exponent_le hX (by linarith)
  apply Real.sqrt_le_iff.mpr
  refine ⟨Real.rpow_nonneg hXp.le _,?_⟩
  have he : (X^(1/2+η:ℝ))^2 = X^(1+2*η) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hXp.le]
    norm_num
    congr 1
    ring
  rw [he]
  exact hdiv.trans (hmul.trans hpow)

theorem canonicalKernelRoots_diameter_scale {S : Finset ℤ} {m : ℕ} {h u : ℤ}
    (hu : u ≠ 0) {X η : ℝ} (hX : 1 ≤ X) (hη : 0 ≤ η)
    (hm : (m:ℝ) ≤ X^η)
    (hdiam : ∀ x∈S,∀ y∈S,|(x:ℝ)-(y:ℝ)|≤X) :
    ∀ r∈canonicalKernelRoots S m h u,∀ s∈canonicalKernelRoots S m h u,
      |(r:ℝ)-(s:ℝ)|≤X^(1/2+η:ℝ) := by
  intro r hr s hs
  exact (canonicalKernelRoots_diameter hu (by linarith) hdiam r hr s hs).trans
    (kernel_root_diameter_scale hX hη hu hm)

end Ostmann.QuadraticCenter

end

end OAI
