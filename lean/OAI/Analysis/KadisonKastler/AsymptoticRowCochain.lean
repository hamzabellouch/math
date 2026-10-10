import OAI.Analysis.KadisonKastler.HaagerupWeakLimits
import OAI.Analysis.KadisonKastler.RowCochainResidual
import OAI.Analysis.KadisonKastler.CochainStarBounds

namespace OAI

/-! Passage from asymptotically modular row averages to a quadratic cochain.
The asymptotic modularity hypothesis is explicit; its general construction is
not asserted by this adapter. -/

namespace KadisonKastler

noncomputable section

open Filter
open scoped Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance asymptoticRowAlgebraOrder (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance asymptoticRowAlgebraStarOrder (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

theorem cochain_coboundary_weak_limit (M : VonNeumannAlgebra H)
    {ι : Type*} (ω : Ultrafilter ι) (F : ι → Algebra M →ₗ[ℂ] Algebra M)
    (L : Algebra M →ₗ[ℂ] Algebra M)
    (ht : ∀ a ξ η, Tendsto (fun i => inner ℂ η ((F i a : H →L[ℂ] H) ξ))
      (ω : Filter ι) (𝓝 (inner ℂ η ((L a : H →L[ℂ] H) ξ)))) :
    ∀ a b ξ η, Tendsto (fun i => inner ℂ η ((linearCoboundary (F i) a b : H →L[ℂ] H) ξ))
      (ω : Filter ι) (𝓝 (inner ℂ η ((linearCoboundary L a b : H →L[ℂ] H) ξ))) := by
  intro a b ξ η
  have h := ((ht b ξ ((a : H →L[ℂ] H).adjoint η)).sub (ht (a * b) ξ η)).add
    (ht a ((b : H →L[ℂ] H) ξ) η)
  simpa [linearCoboundary_apply, inner_sub_right, inner_add_right,
    mul_apply_eq_comp, ContinuousLinearMap.adjoint_inner_left] using h

/-- Asymptotically right-modular normalized rows produce the exact local
cochain estimate used by the Newton iteration. -/
theorem quadratic_cochain_of_asymptotic_rows (M : VonNeumannAlgebra H)
    (m : Algebra M →ₗ[ℂ] Algebra M →ₗ[ℂ] Algebra M)
    (hm : ∀ x y z, m (m x y) z = m x (m y z))
    (hstar : ∀ x y, star (m x y) = m (star y) (star x))
    {c : ℝ} (hc : 0 ≤ c) (hf : HaagerupBound (m - LinearMap.mul ℂ (Algebra M)) c)
    {ι : Type*} (ω : Ultrafilter ι) (n : ι → ℕ) (r : (i : ι) → Fin (n i) → Algebra M)
    (hr : ∀ i, ∑ k, r i k * star (r i k) = 1)
    (hmod : ∀ a b ξ η, Tendsto
      (fun i => inner ℂ η ((finiteCochainModuleDefect (r i)
        (m - LinearMap.mul ℂ (Algebra M)) a b : H →L[ℂ] H) ξ))
      (ω : Filter ι) (𝓝 0)) :
    ∃ D : Algebra M →ₗ[ℂ] Algebra M, CompletelyBoundedBy D c ∧
      (∀ x, D (star x) = star (D x)) ∧
      HaagerupBound (m - LinearMap.mul ℂ (Algebra M) - linearCoboundary D) (2 * c ^ 2) := by
  let f := m - LinearMap.mul ℂ (Algebra M)
  let F (i : ι) := finiteCochainAverage (r i) f
  have hF (i : ι) : CompletelyBoundedBy (F i) c := hf.finiteCochainAverage hc (r i) (hr i)
  obtain ⟨L, hL, ht⟩ := exists_completelyBounded_weak_ultralimit M ω F hc hF
  have hd := cochain_coboundary_weak_limit M ω F L ht
  let G (i : ι) := -finiteAveragedDifferential (r i) f
  have hG (i : ι) : HaagerupBound (G i) (2 * c ^ 2) := by
    have h := (finiteAveragedDifferential_defect_bound (r i) (hr i) m hm hc hf).smul (-1 : ℂ)
    have he : (-1 : ℂ) • finiteAveragedDifferential (r i) f = G i := by
      apply LinearMap.ext
      intro a
      apply LinearMap.ext
      intro b
      change (-1 : ℂ) • finiteAveragedDifferential (r i) f a b =
        -finiteAveragedDifferential (r i) f a b
      rw [neg_smul, one_smul]
    change HaagerupBound ((-1 : ℂ) • finiteAveragedDifferential (r i) f)
      (‖(-1 : ℂ)‖ * (2 * c ^ 2)) at h
    rw [he] at h
    simpa only [norm_neg, norm_one, one_mul] using h
  have htG (a b : Algebra M) (ξ η : H) :
      Tendsto (fun i => inner ℂ η ((G i a b : H →L[ℂ] H) ξ))
        (ω : Filter ι) (𝓝 (inner ℂ η (((f - linearCoboundary L) a b : H →L[ℂ] H) ξ))) := by
    have he (i : ι) : G i a b = f a b - linearCoboundary (F i) a b -
        finiteCochainModuleDefect (r i) f a b := by
      change -(finiteCochainModuleDefect (r i) f a b -
        (f a b - linearCoboundary (F i) a b)) = _
      abel
    simp_rw [he]
    have hconst : Tendsto (fun _ : ι => inner ℂ η ((f a b : H →L[ℂ] H) ξ))
        (ω : Filter ι) (𝓝 (inner ℂ η ((f a b : H →L[ℂ] H) ξ))) := tendsto_const_nhds
    have h := (hconst.sub (hd a b ξ η)).sub (hmod a b ξ η)
    simpa [f, inner_sub_right] using h
  have hres := haagerupBound_of_weak_operator_ultralimit M ω G (f - linearCoboundary L)
    (by positivity) hG htG
  have hs : ∀ x y, star (f x y) = f (star y) (star x) := by
    intro x y
    simp [f, hstar, star_sub, star_mul]
  exact ⟨cochainSymmetrize L, cochainSymmetrize_bound hL, cochainSymmetrize_star L,
    cochainSymmetrize_residual_bound hs L hres⟩

end

end KadisonKastler

end OAI
