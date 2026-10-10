import OAI.Analysis.Mahler.FiniteStrips
import OAI.Analysis.Mahler.GlobalPlanarMonotonicity

namespace OAI

namespace SymmetricMahler
open Real Complex Set Finset
open MahlerConformal
variable {I J : Type*} [Fintype I] [fintypeJ : Fintype J]

noncomputable def stripCoordinate (A : J → I → ℝ) (z : (I → ℝ) × (I → ℝ)) (j : J) : ℂ :=
  (measurement A z.1 j : ℂ)+(measurement A z.2 j : ℂ)*Complex.I

noncomputable def stripDomain (A : J → I → ℝ) : Set ((I → ℝ) × (I → ℝ)) :=
  {z | ∀ j, stripCoordinate A z j ∈ Omega}

noncomputable def stripTau (A : J → I → ℝ) (m : ℕ) (z : (I → ℝ) × (I → ℝ)) : ℝ :=
  ∑ j, ‖inverseF (stripCoordinate A z j)‖^(2*(m : ℝ) : ℝ)

noncomputable def stripMap (A : J → I → ℝ) (m : ℕ) (z : (I → ℝ) × (I → ℝ)) :
    (I → ℝ) × (I → ℝ) :=
  (z.1,push A (fun j => planarPrimitive m (measurement A z.1 j) (measurement A z.2 j)))

lemma verticalFiber_realPart {q t : ℝ} (ht : t ∈ verticalFiber q) : q ∈ Ioo (-1 : ℝ) 1 := by
  have hu : (q : ℂ)+(t : ℂ)*Complex.I ∈ Omega := ht
  have h := F_re_mem_strip (w := inverseF ((q : ℂ)+(t : ℂ)*Complex.I))
    (by simpa using inverseF_mem hu)
  rw [inverseF_right hu] at h
  simpa using h

lemma strictMonoOn_planarPrimitive_any {m : ℕ} (hm : 0 < m) (q : ℝ) :
    StrictMonoOn (planarPrimitive m q) (verticalFiber q) := by
  intro a ha b hb hab
  exact strictMonoOn_planarPrimitive_global hm (verticalFiber_realPart ha) ha hb hab

/-- The finite-strip map is injective on its entire complex strip domain. -/
theorem stripMap_injOn (A : J → I → ℝ) (hA : Function.Injective (measurement A))
    {m : ℕ} (hm : 0 < m) : InjOn (stripMap A m) (stripDomain A) := by
  exact full_map_injOn A hA (fun x j => verticalFiber (measurement A x j))
    (fun x j => planarPrimitive m (measurement A x j))
    (fun x j => strictMonoOn_planarPrimitive_any hm _)

omit fintypeJ in
lemma stripDomain_realPart [Fintype J] (A : J → I → ℝ) {z : (I → ℝ) × (I → ℝ)}
    (hz : z ∈ stripDomain A) : z.1 ∈ stripBody A := by
  intro j
  exact (abs_lt.mpr (verticalFiber_realPart (hz j))).le

/-- The image functional bound uses the literal P and tau, with the
uniform analytic estimate proved rather than supplied as a premise. -/
theorem stripMap_pairing_bound (A : J → I → ℝ) {m : ℕ} (hm : 2 ≤ m)
    {z : (I → ℝ) × (I → ℝ)} (hz : z ∈ stripDomain A) (hτ : stripTau A m z < 1)
    {v : I → ℝ} (hv : v ∈ stripBody A) :
    (∑ i, (stripMap A m z).2 i*v i) < 1+Fintype.card J*planarError m := by
  apply image_bound_with_error A
    (fun j => planarPrimitive m (measurement A z.1 j) (measurement A z.2 j))
    (fun j => ‖inverseF (stripCoordinate A z j)‖^(2*(m : ℝ) : ℝ)) (planarError m)
    _ hτ v hv
  intro j
  simpa [stripCoordinate] using planarPrimitive_abs_bound hm (hz j)

/-- Polar body for the coordinate pairing. -/
def coordinatePolar (K : Set (I → ℝ)) : Set (I → ℝ) :=
  {p | ∀ v ∈ K, (∑ i, p i*v i) ≤ 1}

/-- Dividing the image's vertical component by 1+N epsilon places it in the
literal polar body of the strip intersection. -/
theorem normalized_stripMap_mem_polar (A : J → I → ℝ) {m : ℕ} (hm : 2 ≤ m)
    {z : (I → ℝ) × (I → ℝ)} (hz : z ∈ stripDomain A) (hτ : stripTau A m z < 1) :
    (fun i => (stripMap A m z).2 i/(1+Fintype.card J*planarError m)) ∈
      coordinatePolar (stripBody A) := by
  have hc : 0 < 1+Fintype.card J*planarError m := by
    have := planarError_nonneg (m : ℝ)
    positivity
  intro v hv
  have h := (stripMap_pairing_bound A hm hz hτ hv).le
  calc
    _ = (∑ i, (stripMap A m z).2 i*v i)/(1+Fintype.card J*planarError m) := by
      simp only [div_mul_eq_mul_div, sum_div]
    _ ≤ 1 := (div_le_one hc).mpr h

end SymmetricMahler

end OAI
