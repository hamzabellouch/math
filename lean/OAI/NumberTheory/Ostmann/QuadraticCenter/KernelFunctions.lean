import OAI.NumberTheory.Ostmann.QuadraticCenter.KernelCharacterTransfer
import OAI.NumberTheory.Ostmann.QuadraticCenter.KernelPopulationBound

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

def canonicalSignedKernel (z : ℤ) : ℤ :=
  if hz : z=0 then 0 else (kernelFactorization z hz).kernel

def canonicalSquareFactor (z : ℤ) : ℕ :=
  if hz : z=0 then 0 else (kernelFactorization z hz).squareFactor

theorem canonical_kernel_factorization (z : ℤ) :
    z = canonicalSignedKernel z*(canonicalSquareFactor z:ℤ)^2 := by
  by_cases hz : z=0
  · simp [canonicalSignedKernel,canonicalSquareFactor,hz]
  · simpa only [canonicalSignedKernel,canonicalSquareFactor,dite_eq_right hz] using
      (kernelFactorization z hz).factorization

theorem canonicalSignedKernel_ne_zero {z : ℤ} (hz : z≠0) : canonicalSignedKernel z≠0 := by
  simpa only [canonicalSignedKernel,dite_eq_right hz] using (kernelFactorization z hz).kernel_ne_zero

theorem canonicalSignedKernel_squarefree {z : ℤ} (hz : z≠0) :
    Squarefree (canonicalSignedKernel z) := by
  simpa only [canonicalSignedKernel,dite_eq_right hz] using (kernelFactorization z hz).kernel_squarefree

theorem canonicalSquareFactor_pos {z : ℤ} (hz : z≠0) : 0<canonicalSquareFactor z := by
  simpa only [canonicalSquareFactor,dite_eq_right hz] using (kernelFactorization z hz).squareFactor_pos

theorem canonicalSignedKernel_abs_le (z : ℤ) : (canonicalSignedKernel z).natAbs ≤ z.natAbs := by
  by_cases hz : z=0
  · simp [canonicalSignedKernel,hz]
  · simpa only [canonicalSignedKernel,dite_eq_right hz] using (kernelFactorization z hz).kernel_abs_le

theorem signedJacobiAverage_zero {P : Finset ℕ} (hP : ∀p∈P,Nat.Prime p)
    (ε : ℕ → ℤ) : signedJacobiAverage P ε 0=0 := by
  unfold signedJacobiAverage
  rw [Finset.sum_eq_zero]
  · simp
  · intro p hp
    rw [jacobiSym.zero_left (hP p hp).one_lt]
    simp

theorem numerator_ne_zero_of_signed_average {P : Finset ℕ}
    (hP : ∀p∈P,Nat.Prime p) (ε : ℕ → ℤ) {z : ℤ} {c : ℝ}
    (hc : 0<c) (hbias : c≤|signedJacobiAverage P ε z|) : z≠0 := by
  intro hz
  subst z
  rw [signedJacobiAverage_zero hP,abs_zero] at hbias
  exact (not_le_of_gt hc) hbias

def canonicalKernelFiber (S : Finset ℤ) (m : ℕ) (h u : ℤ) : Finset ℤ :=
  S.filter (fun x => canonicalSignedKernel ((m:ℤ)*x-h)=u)

def canonicalKernelRoots (S : Finset ℤ) (m : ℕ) (h u : ℤ) : Finset ℕ :=
  (canonicalKernelFiber S m h u).image (fun x => canonicalSquareFactor ((m:ℤ)*x-h))

theorem canonicalKernelFiber_factorization {S : Finset ℤ} {m : ℕ} {h u x : ℤ}
    (hx : x∈canonicalKernelFiber S m h u) :
    (m:ℤ)*x-h=u*(canonicalSquareFactor ((m:ℤ)*x-h):ℤ)^2 := by
  have hh := canonical_kernel_factorization ((m:ℤ)*x-h)
  rwa [(Finset.mem_filter.mp hx).2] at hh

theorem canonicalKernelRoots_card {S : Finset ℤ} {m : ℕ} (hm : 0 < m) (h u : ℤ) :
    (canonicalKernelRoots S m h u).card=(canonicalKernelFiber S m h u).card := by
  apply Finset.card_image_of_injOn
  intro x hx y hy he
  have hx' := canonicalKernelFiber_factorization hx
  have hy' := canonicalKernelFiber_factorization hy
  dsimp only at he
  rw [he] at hx'
  have hmm : (m:ℤ)≠0 := by exact_mod_cast hm.ne'
  exact mul_left_cancel₀ hmm (by linarith [hx',hy'])

theorem canonicalKernelRoots_diameter {S : Finset ℤ} {m : ℕ} {h u : ℤ}
    (hu : u≠0) {X : ℝ} (hX : 0≤X)
    (hdiam : ∀x∈S,∀y∈S,|(x:ℝ)-(y:ℝ)|≤X) :
    ∀r∈canonicalKernelRoots S m h u,∀s∈canonicalKernelRoots S m h u,
      |(r:ℝ)-(s:ℝ)|≤Real.sqrt ((m:ℝ)*X/|(u:ℝ)|) := by
  intro r hr s hs
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hs
  simpa only [Int.cast_natCast,(show |(m:ℝ)|=(m:ℝ) from abs_of_nonneg (Nat.cast_nonneg m))] using
    kernel_squareFactor_diameter hu hX (canonicalKernelFiber_factorization hx)
      (canonicalKernelFiber_factorization hy)
      (hdiam x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1)

theorem canonicalKernelFiber_population_bound {S : Finset ℤ} {m : ℕ}
    (hm : 0 < m) {h u : ℤ} (hcop : IsCoprime h (m:ℤ)) (hu : u≠0)
    {X : ℝ} (hX : 0≤X) (hdiam : ∀x∈S,∀y∈S,|(x:ℝ)-(y:ℝ)|≤X) :
    ((canonicalKernelFiber S m h u).card:ℝ) ≤
      4*Real.sqrt (X/|(u:ℝ)|)+8*Real.sqrt (m:ℝ) := by
  exact kernel_population_real_bound (canonicalKernelFiber S m h u) hm hcop hu
    (fun x => canonicalSquareFactor ((m:ℤ)*x-h)) hX
    (fun _ hx => canonicalKernelFiber_factorization hx)
    (fun x hx y hy => hdiam x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1)

end Ostmann.QuadraticCenter

end

end OAI
