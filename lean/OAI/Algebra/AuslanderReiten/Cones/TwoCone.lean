import OAI.Algebra.AuslanderReiten.Cones.ConeExactness
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.RingTheory.Finiteness.Prod

namespace OAI

noncomputable section

open CategoryTheory

namespace ArExplicit.TwoCone

universe u

variable {R : Type u} [Ring R]

structure Data (R : Type u) [Ring R] where
  term : ℕ → ModuleCat.{u} R
  d : (n : ℕ) → term (n+1) →ₗ[R] term n
  first : (n : ℕ) → term (n+3) →ₗ[R] term n
  second : (n : ℕ) → term (n+3) →ₗ[R] term n
  square : ∀ n, (d n).comp (d (n+1)) = 0
  first_comm : ∀ n, (d n).comp (first (n+1)) = (first n).comp (d (n+3))
  second_comm : ∀ n, (d n).comp (second (n+1)) = (second n).comp (d (n+3))
  comparisons_comm : ∀ n,
    (first n).comp (second (n+3)) = (second n).comp (first (n+3))

variable (D : Data R)

abbrev firstTerm (n : ℕ) : ModuleCat.{u} R :=
  ModuleCat.of R (D.term n × D.term (n+2))

def firstD (n : ℕ) : firstTerm D (n+1) →ₗ[R] firstTerm D n :=
  coneBlock (D.d n) (D.d (n+2)) (D.first n)

def secondOnFirst (n : ℕ) : firstTerm D (n+3) →ₗ[R] firstTerm D n :=
  (D.second n).prodMap (D.second (n+2))

theorem firstD_square (n : ℕ) : (firstD D n).comp (firstD D (n+1)) = 0 :=
  coneBlock_comp_zero _ _ _ _ _ _ (D.square n) (D.square (n+2)) (D.first_comm n)

theorem secondOnFirst_comm (n : ℕ) :
    (firstD D n).comp (secondOnFirst D (n+1)) =
      (secondOnFirst D n).comp (firstD D (n+3)) := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  apply Prod.ext
  · change D.d n (D.second (n+1) x) + D.first n (D.second (n+3) y) =
      D.second n (D.d (n+3) x + D.first (n+3) y)
    rw [map_add, show D.d n (D.second (n+1) x) =
      D.second n (D.d (n+3) x) from DFunLike.congr_fun (D.second_comm n) x,
      show D.first n (D.second (n+3) y) =
      D.second n (D.first (n+3) y) from DFunLike.congr_fun (D.comparisons_comm n) y]
  · change -D.d (n+2) (D.second (n+3) y) =
      D.second (n+2) (-D.d (n+5) y)
    rw [map_neg]
    exact congrArg Neg.neg (DFunLike.congr_fun (D.second_comm (n+2)) y)

abbrev term (n : ℕ) : ModuleCat.{u} R :=
  ModuleCat.of R (firstTerm D n × firstTerm D (n+2))

def d (n : ℕ) : term D (n+1) →ₗ[R] term D n :=
  coneBlock (firstD D n) (firstD D (n+2)) (secondOnFirst D n)

theorem d_square (n : ℕ) : (d D n).comp (d D (n+1)) = 0 :=
  coneBlock_comp_zero _ _ _ _ _ _ (firstD_square D n) (firstD_square D (n+2))
    (secondOnFirst_comm D n)

def complex : ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of (term D) (fun n => ModuleCat.ofHom (d D n))
    (fun n => ModuleCat.hom_ext (d_square D n))

theorem firstD_exact (hex : ∀ n, Function.Exact (D.d (n+1)) (D.d n)) (n : ℕ) :
    Function.Exact (firstD D (n+1)) (firstD D n) :=
  coneBlock_exact _ _ _ _ _ _ (hex n) (hex (n+2)) (D.first_comm n)

theorem d_exact (hex : ∀ n, Function.Exact (D.d (n+1)) (D.d n)) (n : ℕ) :
    Function.Exact (d D (n+1)) (d D n) :=
  coneBlock_exact _ _ _ _ _ _ (firstD_exact D hex n) (firstD_exact D hex (n+2))
    (secondOnFirst_comm D n)

theorem complex_exactAt_succ (hex : ∀ n, Function.Exact (D.d (n+1)) (D.d n))
    (n : ℕ) : (complex D).ExactAt (n+1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n+1+1) (n+1) n (by simp) (by simp)]
  apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
  change Function.Exact
    (ChainComplex.of.d (term D) (fun i => ModuleCat.ofHom (d D i)) (n+1+1) (n+1))
    (ChainComplex.of.d (term D) (fun i => ModuleCat.ofHom (d D i)) (n+1) n)
  rw [ChainComplex.of_d, ChainComplex.of_d]
  exact d_exact D hex n

theorem term_finite (hf : ∀ n, Module.Finite R (D.term n)) (n : ℕ) :
    Module.Finite R (term D n) := by
  let := hf n
  let := hf (n+2)
  let := hf (n+4)
  exact inferInstanceAs (Module.Finite R
    ((D.term n × D.term (n+2)) × (D.term (n+2) × D.term (n+4))))

theorem term_projective (hp : ∀ n, Module.Projective R (D.term n)) (n : ℕ) :
    Module.Projective R (term D n) := by
  let := hp n
  let := hp (n+2)
  let := hp (n+4)
  exact inferInstanceAs (Module.Projective R
    ((D.term n × D.term (n+2)) × (D.term (n+2) × D.term (n+4))))

abbrev Cokernel (N : ℕ) := term D N ⧸ LinearMap.range (d D N)

abbrev C₁ := Cokernel D 1

theorem cokernel_finite (hf : ∀ n, Module.Finite R (D.term n)) (N : ℕ) :
    Module.Finite R (Cokernel D N) := by
  let := term_finite D hf N
  infer_instance

@[simp] theorem d_apply (n : ℕ) (a : D.term (n+1)) (b c : D.term (n+3))
    (e : D.term (n+5)) :
    d D n ((a,b),(c,e)) =
      ((D.d n a + D.first n b + D.second n c,
        -D.d (n+2) b + D.second (n+2) e),
       (-D.d (n+2) c - D.first (n+2) e, D.d (n+4) e)) := by
  simp [d, firstD, secondOnFirst, coneBlock_apply, sub_eq_add_neg]
  abel

end ArExplicit.TwoCone

end

end OAI
