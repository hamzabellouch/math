import OAI.Algebra.AuslanderReiten.Homology.LinearHomotopy

namespace OAI

noncomputable section

namespace ArExplicit.ProjectiveNullhomotopyAbove

universe u
variable {R : Type u} [Ring R]
variable {P Q : ℕ → Type u}
variable [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)]
variable [∀ n, AddCommGroup (Q n)] [∀ n, Module R (Q n)]
variable (dP : (n : ℕ) → P (n + 1) →ₗ[R] P n)
variable (dQ : (n : ℕ) → Q (n + 1) →ₗ[R] Q n)
variable (f : (n : ℕ) → Q (n + 2) →ₗ[R] P n)

private structure Pair (n : ℕ) where
  lo : Q (n + 1) →ₗ[R] P n
  hi : Q (n + 2) →ₗ[R] P (n + 1)
  eqn : f n = (dP n).comp hi + lo.comp (dQ (n + 1))

variable (hproj : ∀ n, Module.Projective R (Q n))
variable (hQQ : ∀ n, (dQ n).comp (dQ (n + 1)) = 0)
variable (hexact : ∀ n, LinearMap.range (dP (n + 1)) = LinearMap.ker (dP n))
variable (hcomm : ∀ n, (dP n).comp (f (n + 1)) = (f n).comp (dQ (n + 2)))

include hproj hQQ hexact hcomm

private theorem step (n : ℕ) (c : Pair dP dQ f n) :
    ∃ c' : Pair dP dQ f (n + 1), c'.lo = c.hi := by
  let := hproj (n + 3)
  obtain ⟨h, hh⟩ := extend_homotopy_up (dQ (n + 2)) (dQ (n + 1)) (hQQ (n + 1))
    (dP (n + 1)) (dP n) (hexact n) (f (n + 1)) (f n) (hcomm n) c.hi c.lo c.eqn
  exact ⟨⟨c.hi, h, hh⟩, rfl⟩

private def sequence (c : Pair dP dQ f 0) : (n : ℕ) → Pair dP dQ f n
  | 0 => c
  | n + 1 => Classical.choose (step dP dQ f hproj hQQ hexact hcomm n
      (sequence c n))

private theorem sequence_succ_lo (c : Pair dP dQ f 0) (n : ℕ) :
    (sequence dP dQ f hproj hQQ hexact hcomm c (n + 1)).lo =
      (sequence dP dQ f hproj hQQ hexact hcomm c n).hi :=
  Classical.choose_spec (step dP dQ f hproj hQQ hexact hcomm n
    (sequence dP dQ f hproj hQQ hexact hcomm c n))

variable {M : Type u} [AddCommGroup M] [Module R M]

theorem exists_homotopy (e : P 0 →ₗ[R] M) (hepi : Function.Surjective e)
    (he : LinearMap.range (dP 0) = LinearMap.ker e) (z : Q 1 →ₗ[R] M)
    (hz : e.comp (f 0) = z.comp (dQ 1)) :
    ∃ G : (n : ℕ) → Q (n + 1) →ₗ[R] P n,
      e.comp (G 0) = z ∧ ∀ n, f n = (dP n).comp (G (n + 1)) + (G n).comp (dQ (n + 1)) := by
  let := hproj 1
  obtain ⟨g₀, hg₀⟩ := Module.projective_lifting_property e z hepi
  have hc : e.comp (f 0 - g₀.comp (dQ 1)) = 0 := by
    ext x
    have h1 := LinearMap.congr_fun hz x
    have h2 := LinearMap.congr_fun hg₀ (dQ 1 x)
    simp only [LinearMap.comp_apply] at h1 h2
    change e (f 0 x - g₀ (dQ 1 x)) = 0
    rw [map_sub, h2]
    exact sub_eq_zero.mpr h1
  let := hproj 2
  obtain ⟨g₁, hg₁⟩ := lift_through_exact (dP 0) e he (f 0 - g₀.comp (dQ 1)) hc
  let c : Pair dP dQ f 0 := ⟨g₀, g₁, by rw [hg₁, sub_add_cancel]⟩
  refine ⟨fun n => (sequence dP dQ f hproj hQQ hexact hcomm c n).lo, hg₀, ?_⟩
  intro n
  simpa only [sequence_succ_lo] using (sequence dP dQ f hproj hQQ hexact hcomm c n).eqn

end ArExplicit.ProjectiveNullhomotopyAbove

end

end OAI
