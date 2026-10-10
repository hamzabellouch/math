import OAI.Algebra.AuslanderReiten.Complete.CompleteResolution
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive

namespace OAI

open CategoryTheory

namespace ArExplicit

universe u

variable {R : Type u} [Ring R]

structure ExactProjectiveComplex (P : ChainComplex (ModuleCat.{u} R) ℤ) : Prop where
  finite : ∀ n, Module.Finite R (P.X n)
  projective : ∀ n, Module.Projective R (P.X n)
  exactAt : ∀ n, LinearMap.range (P.d (n + 1) n).hom =
    LinearMap.ker (P.d n (n - 1)).hom

structure TotallyAcyclicComplex (P : ChainComplex (ModuleCat.{u} R) ℤ) : Prop
    extends ExactProjectiveComplex P where
  dualExact : ∀ n, HomExactAt (P.d (n + 1) n).hom (P.d n (n - 1)).hom

theorem ExactProjectiveComplex.exactAt_of_indices
    {P : ChainComplex (ModuleCat.{u} R) ℤ} (h : ExactProjectiveComplex P)
    {i j k : ℤ} (hi : i = j + 1) (hk : k = j - 1) :
    LinearMap.range (P.d i j).hom = LinearMap.ker (P.d j k).hom := by
  subst i
  subst k
  exact h.exactAt j

theorem TotallyAcyclicComplex.dualExact_of_indices
    {P : ChainComplex (ModuleCat.{u} R) ℤ} (h : TotallyAcyclicComplex P)
    {i j k : ℤ} (hi : i = j + 1) (hk : k = j - 1) :
    HomExactAt (P.d i j).hom (P.d j k).hom := by
  subst i
  subst k
  exact h.dualExact j

namespace CompleteComparison

variable {P Q : ChainComplex (ModuleCat.{u} R) ℤ}

theorem differential_comp (P : ChainComplex (ModuleCat.{u} R) ℤ) (i j k : ℤ) :
    (P.d j k).hom.comp (P.d i j).hom = 0 :=
  congrArg (fun f : P.X i ⟶ P.X k => f.hom) (P.d_comp_d i j k)

abbrev Cokernel (P : ChainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :=
  P.X n ⧸ LinearMap.range (P.d (n + 1) n).hom

private structure UpPair (P Q : ChainComplex (ModuleCat.{u} R) ℤ) (n : ℕ) where
  lo : P.X (n : ℤ) →ₗ[R] Q.X (n : ℤ)
  hi : P.X ((n + 1 : ℕ) : ℤ) →ₗ[R] Q.X ((n + 1 : ℕ) : ℤ)
  comm : (Q.d (n + 1) n).hom.comp hi = lo.comp (P.d (n + 1) n).hom

private theorem exists_upStep (hP : ExactProjectiveComplex P)
    (hQ : ExactProjectiveComplex Q) (n : ℕ) (c : UpPair P Q n) :
    ∃ c' : UpPair P Q (n + 1), c'.lo = c.hi := by
  let := hP.projective (n + 2)
  have hex : LinearMap.range (Q.d (n + 2) (n + 1)).hom =
      LinearMap.ker (Q.d (n + 1) n).hom := by
    exact hQ.exactAt_of_indices (by omega) (by omega)
  obtain ⟨f, hf⟩ := extend_comparison_up
    (P.d (n + 2) (n + 1)).hom (P.d (n + 1) n).hom
    (differential_comp P _ _ _)
    (Q.d (n + 2) (n + 1)).hom (Q.d (n + 1) n).hom hex c.hi c.lo c.comm
  exact ⟨⟨c.hi, f, hf⟩, rfl⟩

private noncomputable def upSequence (hP : ExactProjectiveComplex P)
    (hQ : ExactProjectiveComplex Q) (c : UpPair P Q 0) : (n : ℕ) → UpPair P Q n
  | 0 => c
  | n + 1 => Classical.choose (exists_upStep hP hQ n (upSequence hP hQ c n))

private theorem upSequence_succ_lo (hP : ExactProjectiveComplex P)
    (hQ : ExactProjectiveComplex Q) (c : UpPair P Q 0) (n : ℕ) :
    (upSequence hP hQ c (n + 1)).lo = (upSequence hP hQ c n).hi :=
  Classical.choose_spec (exists_upStep hP hQ n (upSequence hP hQ c n))

private structure DownPair (P Q : ChainComplex (ModuleCat.{u} R) ℤ) (n : ℕ) where
  hi : P.X (-(n : ℤ)) →ₗ[R] Q.X (-(n : ℤ))
  lo : P.X (Int.negSucc n) →ₗ[R] Q.X (Int.negSucc n)
  comm : (Q.d (-(n : ℤ)) (Int.negSucc n)).hom.comp hi =
    lo.comp (P.d (-(n : ℤ)) (Int.negSucc n)).hom

private theorem exists_downStep (hP : TotallyAcyclicComplex P)
    (hQ : ExactProjectiveComplex Q) (n : ℕ) (c : DownPair P Q n) :
    ∃ c' : DownPair P Q (n + 1), c'.hi = c.lo := by
  let := hQ.finite (Int.negSucc (n + 1))
  let := hQ.projective (Int.negSucc (n + 1))
  have hd : HomExactAt (P.d (-(n : ℤ)) (Int.negSucc n)).hom
      (P.d (Int.negSucc n) (Int.negSucc (n + 1))).hom := by
    exact hP.dualExact_of_indices (by omega) (by omega)
  obtain ⟨f, hf⟩ := extend_comparison_down
    (P.d (-(n : ℤ)) (Int.negSucc n)).hom
    (P.d (Int.negSucc n) (Int.negSucc (n + 1))).hom hd
    (Q.d (-(n : ℤ)) (Int.negSucc n)).hom
    (Q.d (Int.negSucc n) (Int.negSucc (n + 1))).hom
    (differential_comp Q _ _ _) c.hi c.lo c.comm
  exact ⟨⟨c.lo, f, hf.symm⟩, rfl⟩

private noncomputable def downSequence (hP : TotallyAcyclicComplex P)
    (hQ : ExactProjectiveComplex Q) (c : DownPair P Q 0) : (n : ℕ) → DownPair P Q n
  | 0 => c
  | n + 1 => Classical.choose (exists_downStep hP hQ n (downSequence hP hQ c n))

private theorem downSequence_succ_hi (hP : TotallyAcyclicComplex P)
    (hQ : ExactProjectiveComplex Q) (c : DownPair P Q 0) (n : ℕ) :
    (downSequence hP hQ c (n + 1)).hi = (downSequence hP hQ c n).lo :=
  Classical.choose_spec (exists_downStep hP hQ n (downSequence hP hQ c n))

private theorem exists_downStart (hP : TotallyAcyclicComplex P)
    (hQ : ExactProjectiveComplex Q) (c : UpPair P Q 0) :
    ∃ d : DownPair P Q 0, d.hi = c.lo := by
  let := hQ.finite (-1)
  let := hQ.projective (-1)
  obtain ⟨f, hf⟩ := extend_comparison_down
    (P.d 1 0).hom (P.d 0 (-1)).hom
    (hP.dualExact_of_indices (by omega) (by omega))
    (Q.d 1 0).hom (Q.d 0 (-1)).hom
    (differential_comp Q _ _ _) c.hi c.lo c.comm
  exact ⟨⟨c.lo, f, hf.symm⟩, rfl⟩

private noncomputable def components (hP : TotallyAcyclicComplex P)
    (hQ : ExactProjectiveComplex Q) (c : UpPair P Q 0) (d : DownPair P Q 0) :
    (n : ℤ) → P.X n →ₗ[R] Q.X n
  | Int.ofNat n => (upSequence hP.toExactProjectiveComplex hQ c n).lo
  | Int.negSucc n => (downSequence hP hQ d n).lo

private noncomputable def fromPairs (hP : TotallyAcyclicComplex P)
    (hQ : ExactProjectiveComplex Q) (c : UpPair P Q 0) (d : DownPair P Q 0)
    (hd : d.hi = c.lo) : P ⟶ Q where
  f n := ModuleCat.ofHom (components hP hQ c d n)
  comm' i j hij := by
    change j + 1 = i at hij
    subst i
    apply ModuleCat.hom_ext
    cases j with
    | ofNat n =>
      change (Q.d (n + 1) n).hom.comp
          (upSequence hP.toExactProjectiveComplex hQ c (n + 1)).lo =
        (upSequence hP.toExactProjectiveComplex hQ c n).lo.comp (P.d (n + 1) n).hom
      rw [upSequence_succ_lo]
      exact (upSequence hP.toExactProjectiveComplex hQ c n).comm
    | negSucc n =>
      cases n with
      | zero =>
        change (Q.d 0 (-1)).hom.comp c.lo = d.lo.comp (P.d 0 (-1)).hom
        rw [← hd]
        exact d.comm
      | succ n =>
        change (Q.d (Int.negSucc n) (Int.negSucc (n + 1))).hom.comp
            (downSequence hP hQ d n).lo =
          (downSequence hP hQ d (n + 1)).lo.comp
            (P.d (Int.negSucc n) (Int.negSucc (n + 1))).hom
        rw [← downSequence_succ_hi]
        exact (downSequence hP hQ d (n + 1)).comm

theorem lift_cokernels (hP : TotallyAcyclicComplex P) (hQ : ExactProjectiveComplex Q)
    (u : Cokernel P 0 →ₗ[R] Cokernel Q 0) :
    ∃ F : P ⟶ Q,
      (LinearMap.range (Q.d 1 0).hom).mkQ.comp (F.f 0).hom =
        u.comp (LinearMap.range (P.d 1 0).hom).mkQ := by
  let := hP.projective 0
  let := hP.projective 1
  obtain ⟨f₀, f₁, hf₀, hf₁⟩ := lift_cokernel_map (P.d 1 0).hom (Q.d 1 0).hom u
  let c : UpPair P Q 0 := ⟨f₀, f₁, hf₁⟩
  obtain ⟨d, hd⟩ := exists_downStart hP hQ c
  exact ⟨fromPairs hP hQ c d hd, hf₀⟩

def cokernelMap (F : P ⟶ Q) (n : ℤ) : Cokernel P n →ₗ[R] Cokernel Q n :=
  (LinearMap.range (P.d (n + 1) n).hom).mapQ
    (LinearMap.range (Q.d (n + 1) n).hom) (F.f n).hom (by
      rintro _ ⟨x, rfl⟩
      refine ⟨(F.f (n + 1)).hom x, ?_⟩
      exact DFunLike.congr_fun
        (congrArg (fun f : P.X (n + 1) ⟶ Q.X n => f.hom) (F.comm (n + 1) n)) x)

@[simp]
theorem cokernelMap_mkQ (F : P ⟶ Q) (n : ℤ) :
    (cokernelMap F n).comp (LinearMap.range (P.d (n + 1) n).hom).mkQ =
      (LinearMap.range (Q.d (n + 1) n).hom).mkQ.comp (F.f n).hom :=
  Submodule.mapQ_mkQ _ _ _

@[simp]
theorem cokernelMap_id (n : ℤ) : cokernelMap (𝟙 P) n = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (P.d (n + 1) n).hom) x
  rfl

@[simp]
theorem cokernelMap_comp {S : ChainComplex (ModuleCat.{u} R) ℤ}
    (F : P ⟶ Q) (G : Q ⟶ S) (n : ℤ) :
    cokernelMap (F ≫ G) n = (cokernelMap G n).comp (cokernelMap F n) := by
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (P.d (n + 1) n).hom) x
  rfl

@[simp]
theorem cokernelMap_add (F G : P ⟶ Q) (n : ℤ) :
    cokernelMap (F + G) n = cokernelMap F n + cokernelMap G n := by
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (P.d (n + 1) n).hom) x
  exact map_add (LinearMap.range (Q.d (n + 1) n).hom).mkQ _ _

@[simp]
theorem cokernelMap_zero (n : ℤ) : cokernelMap (0 : P ⟶ Q) n = 0 := by
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (P.d (n + 1) n).hom) x
  exact map_zero (LinearMap.range (Q.d (n + 1) n).hom).mkQ

theorem cokernelMap_surjective (hP : TotallyAcyclicComplex P)
    (hQ : ExactProjectiveComplex Q) : Function.Surjective (fun F : P ⟶ Q => cokernelMap F 0) := by
  intro u
  obtain ⟨F, hF⟩ := lift_cokernels hP hQ u
  refine ⟨F, ?_⟩
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (P.d 1 0).hom) x
  exact DFunLike.congr_fun hF y

end CompleteComparison

end ArExplicit

end OAI
