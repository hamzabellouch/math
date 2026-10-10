import OAI.Algebra.AuslanderReiten.Complete.CompleteComparison
import OAI.Algebra.AuslanderReiten.Homology.LinearHomotopy
import OAI.Algebra.AuslanderReiten.Stable.StableHom
import Mathlib.Algebra.Homology.Homotopy

namespace OAI

open CategoryTheory

namespace ArExplicit.CompleteComparison

universe u

variable {R : Type u} [Ring R]
variable {P Q : ChainComplex (ModuleCat.{u} R) ℤ}

theorem comm_linear (F : P ⟶ Q) (i j : ℤ) :
    (Q.d i j).hom.comp (F.f i).hom = (F.f j).hom.comp (P.d i j).hom :=
  congrArg (fun f : P.X i ⟶ Q.X j => f.hom) (F.comm i j)

private structure UpHomPair (F : P ⟶ Q) (n : ℕ) where
  lo : P.X (n : ℤ) →ₗ[R] Q.X ((n + 1 : ℕ) : ℤ)
  hi : P.X ((n + 1 : ℕ) : ℤ) →ₗ[R] Q.X ((n + 2 : ℕ) : ℤ)
  eqn : (F.f ((n + 1 : ℕ) : ℤ)).hom = (Q.d ((n + 2 : ℕ) : ℤ) ((n + 1 : ℕ) : ℤ)).hom.comp hi +
    lo.comp (P.d ((n + 1 : ℕ) : ℤ) (n : ℤ)).hom

private theorem exists_upHomStep (hP : ExactProjectiveComplex P)
    (hQ : ExactProjectiveComplex Q) (F : P ⟶ Q) (n : ℕ) (c : UpHomPair F n) :
    ∃ c' : UpHomPair F (n + 1), c'.lo = c.hi := by
  let := hP.projective ((n + 2 : ℕ) : ℤ)
  obtain ⟨h, hh⟩ := extend_homotopy_up
    (P.d ((n + 2 : ℕ) : ℤ) ((n + 1 : ℕ) : ℤ)).hom (P.d ((n + 1 : ℕ) : ℤ) (n : ℤ)).hom (differential_comp P _ _ _)
    (Q.d ((n + 3 : ℕ) : ℤ) ((n + 2 : ℕ) : ℤ)).hom (Q.d ((n + 2 : ℕ) : ℤ) ((n + 1 : ℕ) : ℤ)).hom
    (hQ.exactAt_of_indices (by omega) (by omega))
    (F.f ((n + 2 : ℕ) : ℤ)).hom (F.f ((n + 1 : ℕ) : ℤ)).hom (comm_linear F _ _) c.hi c.lo c.eqn
  exact ⟨⟨c.hi, h, hh⟩, rfl⟩

private noncomputable def upHomSequence (hP : ExactProjectiveComplex P)
    (hQ : ExactProjectiveComplex Q) (F : P ⟶ Q) (c : UpHomPair F 0) :
    (n : ℕ) → UpHomPair F n
  | 0 => c
  | n + 1 => Classical.choose (exists_upHomStep hP hQ F n (upHomSequence hP hQ F c n))

private theorem upHomSequence_succ_lo (hP : ExactProjectiveComplex P)
    (hQ : ExactProjectiveComplex Q) (F : P ⟶ Q) (c : UpHomPair F 0) (n : ℕ) :
    (upHomSequence hP hQ F c (n + 1)).lo = (upHomSequence hP hQ F c n).hi :=
  Classical.choose_spec (exists_upHomStep hP hQ F n (upHomSequence hP hQ F c n))

private structure DownHomPair (F : P ⟶ Q) (n : ℕ) where
  hi : P.X (Int.negSucc n) →ₗ[R] Q.X (-(n : ℤ))
  lo : P.X (Int.negSucc (n + 1)) →ₗ[R] Q.X (Int.negSucc n)
  eqn : (F.f (Int.negSucc n)).hom =
    (Q.d (-(n : ℤ)) (Int.negSucc n)).hom.comp hi +
      lo.comp (P.d (Int.negSucc n) (Int.negSucc (n + 1))).hom

private theorem exists_downHomStep (hP : TotallyAcyclicComplex P)
    (hQ : ExactProjectiveComplex Q) (F : P ⟶ Q) (n : ℕ) (c : DownHomPair F n) :
    ∃ c' : DownHomPair F (n + 1), c'.hi = c.lo := by
  let := hQ.finite (Int.negSucc (n + 1))
  let := hQ.projective (Int.negSucc (n + 1))
  obtain ⟨h, hh⟩ := extend_homotopy_down
    (P.d (Int.negSucc n) (Int.negSucc (n + 1))).hom
    (P.d (Int.negSucc (n + 1)) (Int.negSucc (n + 2))).hom
    (hP.dualExact_of_indices (by omega) (by omega))
    (Q.d (-(n : ℤ)) (Int.negSucc n)).hom
    (Q.d (Int.negSucc n) (Int.negSucc (n + 1))).hom
    (differential_comp Q _ _ _)
    (F.f (Int.negSucc n)).hom (F.f (Int.negSucc (n + 1))).hom
    (comm_linear F _ _) c.hi c.lo c.eqn
  exact ⟨⟨c.lo, h, hh⟩, rfl⟩

private noncomputable def downHomSequence (hP : TotallyAcyclicComplex P)
    (hQ : ExactProjectiveComplex Q) (F : P ⟶ Q) (c : DownHomPair F 0) :
    (n : ℕ) → DownHomPair F n
  | 0 => c
  | n + 1 => Classical.choose
      (exists_downHomStep hP hQ F n (downHomSequence hP hQ F c n))

private theorem downHomSequence_succ_hi (hP : TotallyAcyclicComplex P)
    (hQ : ExactProjectiveComplex Q) (F : P ⟶ Q) (c : DownHomPair F 0) (n : ℕ) :
    (downHomSequence hP hQ F c (n + 1)).hi = (downHomSequence hP hQ F c n).lo :=
  Classical.choose_spec (exists_downHomStep hP hQ F n (downHomSequence hP hQ F c n))

private noncomputable def homComponents (hP : TotallyAcyclicComplex P)
    (hQ : ExactProjectiveComplex Q) (F : P ⟶ Q)
    (c : UpHomPair F 0) (d : DownHomPair F 0) :
    (i j : ℤ) → (ComplexShape.down ℤ).Rel j i → (P.X i ⟶ Q.X j)
  | Int.ofNat n, j, hij => by
      change (n : ℤ) + 1 = j at hij
      subst j
      exact ModuleCat.ofHom (upHomSequence hP.toExactProjectiveComplex hQ F c n).lo
  | Int.negSucc n, j, hij => by
      have hj : j = -(n : ℤ) := by
        change Int.negSucc n + 1 = j at hij
        omega
      clear hij
      subst j
      exact ModuleCat.ofHom (downHomSequence hP hQ F d n).hi

private theorem nullhomotopy_from_pairs_with_initial (hP : TotallyAcyclicComplex P)
    (hQ : ExactProjectiveComplex Q) (F : P ⟶ Q)
    (c : UpHomPair F 0) (d : DownHomPair F 0)
    (hzero : (F.f 0).hom =
      (show P.X 0 →ₗ[R] Q.X 0 from (Q.d 1 0).hom.comp c.lo) +
      (show P.X 0 →ₗ[R] Q.X 0 from d.hi.comp (P.d 0 (-1)).hom)) :
    ∃ H : Homotopy F 0, H.hom (-1) 0 = ModuleCat.ofHom d.hi := by
  let h := homComponents hP hQ F c d
  have hF : F = Homotopy.nullHomotopicMap' h := by
    apply HomologicalComplex.Hom.ext
    funext i
    cases i with
    | ofNat n =>
      cases n with
      | zero =>
        rw [Homotopy.nullHomotopicMap'_f (k₂ := 1) (k₀ := -1) (by decide) (by decide)]
        apply ModuleCat.hom_ext
        change (F.f 0).hom =
          (show P.X 0 →ₗ[R] Q.X 0 from d.hi.comp (P.d 0 (-1)).hom) +
          (show P.X 0 →ₗ[R] Q.X 0 from (Q.d 1 0).hom.comp c.lo)
        rw [add_comm]
        exact hzero
      | succ n =>
        rw [Homotopy.nullHomotopicMap'_f (k₂ := ((n + 2 : ℕ) : ℤ)) (k₀ := (n : ℤ))
          (by change (n + 1 : ℕ) + (1 : ℤ) = (n + 2 : ℕ); omega)
          (by change (n : ℤ) + 1 = (n + 1 : ℕ); omega)]
        apply ModuleCat.hom_ext
        change (F.f ((n + 1 : ℕ) : ℤ)).hom =
          (upHomSequence hP.toExactProjectiveComplex hQ F c n).lo.comp
            (P.d ((n + 1 : ℕ) : ℤ) (n : ℤ)).hom + (Q.d ((n + 2 : ℕ) : ℤ) ((n + 1 : ℕ) : ℤ)).hom.comp
              (upHomSequence hP.toExactProjectiveComplex hQ F c (n + 1)).lo
        rw [upHomSequence_succ_lo]
        exact (upHomSequence hP.toExactProjectiveComplex hQ F c n).eqn.trans (add_comm _ _)
    | negSucc n =>
      rw [Homotopy.nullHomotopicMap'_f (k₂ := -(n : ℤ)) (k₀ := Int.negSucc (n + 1))
        (by change Int.negSucc n + 1 = -(n : ℤ); omega)
        (by change Int.negSucc (n + 1) + 1 = Int.negSucc n; omega)]
      apply ModuleCat.hom_ext
      change (F.f (Int.negSucc n)).hom =
        (show P.X (Int.negSucc n) →ₗ[R] Q.X (Int.negSucc n) from
          (downHomSequence hP hQ F d (n + 1)).hi.comp
            (P.d (Int.negSucc n) (Int.negSucc (n + 1))).hom) +
            (Q.d (-(n : ℤ)) (Int.negSucc n)).hom.comp
              (downHomSequence hP hQ F d n).hi
      rw [downHomSequence_succ_hi, add_comm]
      exact (downHomSequence hP hQ F d n).eqn
  refine ⟨(Homotopy.ofEq hF).trans (Homotopy.nullHomotopy' h), ?_⟩
  simp only [Homotopy.trans_hom, Homotopy.ofEq_hom, Homotopy.nullHomotopy'_hom,
    Pi.zero_apply, zero_add]
  rw [dite_eq_left (show (ComplexShape.down ℤ).Rel 0 (-1) by decide)]
  change homComponents hP hQ F c d (Int.negSucc 0) 0 (by decide) = ModuleCat.ofHom d.hi
  rfl

theorem nullhomotopy_of_initial_with_component (hP : TotallyAcyclicComplex P)
    (hQ : ExactProjectiveComplex Q) (F : P ⟶ Q)
    (h₀ : P.X 0 →ₗ[R] Q.X 1) (hneg₁ : P.X (-1) →ₗ[R] Q.X 0)
    (hh : (F.f 0).hom = (Q.d 1 0).hom.comp h₀ + hneg₁.comp (P.d 0 (-1)).hom) :
    ∃ H : Homotopy F 0, H.hom (-1) 0 = ModuleCat.ofHom hneg₁ := by
  let := hP.projective 1
  let := hQ.finite (-1)
  let := hQ.projective (-1)
  obtain ⟨h₁, hh₁⟩ := extend_homotopy_up
    (P.d 1 0).hom (P.d 0 (-1)).hom (differential_comp P _ _ _)
    (Q.d 2 1).hom (Q.d 1 0).hom
    (hQ.exactAt_of_indices (by omega) (by omega))
    (F.f 1).hom (F.f 0).hom (comm_linear F _ _) h₀ hneg₁ hh
  obtain ⟨hneg₂, hhneg₂⟩ := extend_homotopy_down
    (P.d 0 (-1)).hom (P.d (-1) (-2)).hom
    (hP.dualExact_of_indices (by omega) (by omega))
    (Q.d 1 0).hom (Q.d 0 (-1)).hom (differential_comp Q _ _ _)
    (F.f 0).hom (F.f (-1)).hom (comm_linear F _ _) h₀ hneg₁ hh
  exact nullhomotopy_from_pairs_with_initial hP hQ F
    ⟨h₀, h₁, hh₁⟩ ⟨hneg₁, hneg₂, hhneg₂⟩ hh

theorem nullhomotopy_of_initial (hP : TotallyAcyclicComplex P)
    (hQ : ExactProjectiveComplex Q) (F : P ⟶ Q)
    (h₀ : P.X 0 →ₗ[R] Q.X 1) (hneg₁ : P.X (-1) →ₗ[R] Q.X 0)
    (hh : (F.f 0).hom = (Q.d 1 0).hom.comp h₀ + hneg₁.comp (P.d 0 (-1)).hom) :
    Nonempty (Homotopy F 0) := by
  obtain ⟨H, _⟩ := nullhomotopy_of_initial_with_component hP hQ F h₀ hneg₁ hh
  exact ⟨H⟩

theorem nullhomotopy_of_cokernel_zero (hP : TotallyAcyclicComplex P)
    (hQ : ExactProjectiveComplex Q) (F : P ⟶ Q) (hf : cokernelMap F 0 = 0) :
    ∃ H : Homotopy F 0, H.hom (-1) 0 = 0 := by
  let := hP.projective 0
  have hz : (LinearMap.range (Q.d 1 0).hom).mkQ.comp (F.f 0).hom = 0 := by
    calc
      _ = (cokernelMap F 0).comp (LinearMap.range (P.d 1 0).hom).mkQ :=
        (cokernelMap_mkQ F 0).symm
      _ = 0 := by rw [hf, LinearMap.zero_comp]
  obtain ⟨h₀, hh₀⟩ := lift_through_exact (Q.d 1 0).hom
    (LinearMap.range (Q.d 1 0).hom).mkQ (Submodule.ker_mkQ _).symm (F.f 0).hom hz
  obtain ⟨H, hH⟩ := nullhomotopy_of_initial_with_component hP hQ F h₀ 0 (by
    rw [LinearMap.zero_comp, add_zero, hh₀])
  exact ⟨H, hH⟩

theorem nullhomotopy_of_factorization (hP : TotallyAcyclicComplex P)
    (hQ : ExactProjectiveComplex Q) (F : P ⟶ Q)
    (hf : FactorsThroughFiniteProjective R (Cokernel P 0) (Cokernel Q 0)
      (cokernelMap F 0)) : Nonempty (Homotopy F 0) := by
  rcases hf with ⟨T, hT, hRT, hproj, hfinite, a, b, hab⟩
  let := hP.projective 0
  have hc : (LinearMap.range (Q.d 1 0).hom).mkQ.comp (F.f 0).hom =
      b.comp (a.comp (LinearMap.range (P.d 1 0).hom).mkQ) := by
    calc
      _ = (cokernelMap F 0).comp (LinearMap.range (P.d 1 0).hom).mkQ :=
        (cokernelMap_mkQ F 0).symm
      _ = (b.comp a).comp (LinearMap.range (P.d 1 0).hom).mkQ :=
        congrArg (fun u => u.comp (LinearMap.range (P.d 1 0).hom).mkQ) hab.symm
      _ = _ := LinearMap.comp_assoc _ _ _
  obtain ⟨hneg₁, h₀, hh⟩ := initial_homotopy_of_factorization
    (P.d 1 0).hom (P.d 0 (-1)).hom
    (hP.dualExact_of_indices (by omega) (by omega))
    (Q.d 1 0).hom (F.f 0).hom a b hc
  exact nullhomotopy_of_initial hP hQ F h₀ hneg₁ hh

theorem factorization_of_nullhomotopy (hP : ExactProjectiveComplex P)
    (F : P ⟶ Q) (h : Homotopy F 0) :
    FactorsThroughFiniteProjective R (Cokernel P 0) (Cokernel Q 0) (cokernelMap F 0) := by
  have hh := h.comm 0
  rw [dNext_eq h.hom (i' := -1) (by decide),
    prevD_eq h.hom (j' := 1) (by decide), HomologicalComplex.zero_f_apply, add_zero] at hh
  have hh' : (F.f 0).hom = (Q.d 1 0).hom.comp (h.hom 0 1).hom +
      (h.hom (-1) 0).hom.comp (P.d 0 (-1)).hom := by
    rw [add_comm]
    exact congrArg (fun f : P.X 0 ⟶ Q.X 0 => f.hom) hh
  obtain ⟨a, b, hab⟩ := factorization_of_initial_homotopy
    (P.d 1 0).hom (P.d 0 (-1)).hom (differential_comp P _ _ _)
    (Q.d 1 0).hom (F.f 0).hom (cokernelMap F 0) (cokernelMap_mkQ F 0).symm
    (h.hom (-1) 0).hom (h.hom 0 1).hom hh'
  exact ⟨P.X (-1), inferInstance, inferInstance, hP.projective (-1), hP.finite (-1), a, b, hab⟩

theorem nullhomotopy_iff_stable_zero (hP : TotallyAcyclicComplex P)
    (hQ : ExactProjectiveComplex Q) (F : P ⟶ Q) :
    Nonempty (Homotopy F 0) ↔
      StableHom.classOf R (Cokernel P 0) (Cokernel Q 0) (cokernelMap F 0) = 0 := by
  rw [StableHom.classOf_eq_zero_iff_projective]
  exact ⟨fun ⟨h⟩ => factorization_of_nullhomotopy hP.toExactProjectiveComplex F h,
    nullhomotopy_of_factorization hP hQ F⟩

end ArExplicit.CompleteComparison

end OAI
